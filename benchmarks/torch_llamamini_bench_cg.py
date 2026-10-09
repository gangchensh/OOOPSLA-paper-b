#!/usr/bin/env python
# -*- coding: utf-8 -*-
"""L4：LLaMA-mini 的手写 PyTorch 参考模型 + eager/compile 时延（torch_env 运行）。

与 llamamini_scale_bench.cu 同一份 bin 权重；数学逐行对应 float64 NumPy 参考
（bench_llamamini_l4.py 生成 ref_prefill.f64.bin / ref_gen.f64.bin）。

用法: torch_llamamini_bench.py BINDIR S H DH DF V NLAY T KVMAX [REPS]
输出: 单行 JSON（eager/compile 的 prefill/decode min/median、与 ref 的误差）。

口径：CUDA events，5 warmup + REPS(默认 20) 次，min/median，GPU-only
（权重/prompt 预先驻留 GPU，与 CUDA 侧"不含搬移"口径一致）；decode 为
T 步整循环时间（含设备侧 argmax 反馈，无 host 往返）。
"""
import json
import sys
from pathlib import Path

import numpy as np
import torch
import torch.nn.functional as F

EPS = 1e-5  # 占位，实际从 bin 读


def load_f32(bindir, name, shape):
    a = np.fromfile(Path(bindir) / name, dtype=np.float32)
    return torch.from_numpy(a.reshape(shape).copy())


class LLaMAMiniTorch:
    def __init__(self, bindir, s, h, dh, df, v, L, T, kvmax, dev):
        self.s, self.h, self.dh, self.df, self.v, self.L, self.T, self.kvmax = \
            s, h, dh, df, v, L, T, kvmax
        self.dm = h * dh
        self.scale = 1.0 / float(np.sqrt(dh))
        b = Path(bindir)
        self.eps = float(np.fromfile(b / "rms_eps.bin", dtype=np.float32)[0])
        base = float(np.fromfile(b / "rope_base.bin", dtype=np.float32)[0])
        self.table = load_f32(bindir, "table.bin", (v, self.dm)).to(dev)
        self.rms1_g, self.rms2_g = [], []
        self.wq, self.wk, self.wv, self.wo = [], [], [], []
        self.w1, self.w3, self.w2 = [], [], []
        for li in range(1, L + 1):
            p = f"l{li}"
            self.rms1_g.append(load_f32(bindir, f"{p}_rms1_g.bin", (self.dm,)).to(dev))
            self.rms2_g.append(load_f32(bindir, f"{p}_rms2_g.bin", (self.dm,)).to(dev))
            for tag, lst, shp in (("wq", self.wq, (self.dm, self.dm)),
                                  ("wk", self.wk, (self.dm, self.dm)),
                                  ("wv", self.wv, (self.dm, self.dm)),
                                  ("wo", self.wo, (self.dm, self.dm)),
                                  ("w1", self.w1, (self.dm, df)),
                                  ("w3", self.w3, (self.dm, df)),
                                  ("w2", self.w2, (df, self.dm))):
                lst.append(load_f32(bindir, f"{p}_{tag}.bin", shp).to(dev))
        self.rmsf_g = load_f32(bindir, "rmsf_g.bin", (self.dm,)).to(dev)
        self.whead = load_f32(bindir, "whead.bin", (self.dm, v)).to(dev)
        # RoPE 频率表：theta[pos, i] = pos * base^(-2i/dh)
        pos = torch.arange(kvmax, dtype=torch.float64)
        fr = torch.pow(torch.tensor(base, dtype=torch.float64),
                       -2.0 * torch.arange(dh // 2, dtype=torch.float64) / dh)
        th = torch.outer(pos, fr)
        self.cos_t = torch.cos(th).float().to(dev)   # [kvmax, dh/2]
        self.sin_t = torch.sin(th).float().to(dev)
        self.arange_s = torch.arange(s, device=dev)
        self.arange_kv = torch.arange(kvmax, device=dev)
        # KV cache（在 inference_mode 外创建，允许原地写）
        self.kc = [torch.zeros(h, kvmax, dh, device=dev) for _ in range(L)]
        self.vc = [torch.zeros(h, kvmax, dh, device=dev) for _ in range(L)]
        self.dev = dev

    def rms(self, x, g):
        ms = (x * x).mean(dim=-1, keepdim=True)
        return x * torch.rsqrt(ms + self.eps) * g

    def rope(self, x, pos_idx):
        # x [..., h, dh]；pos_idx 广播到 [...]；pair 交错 (0,1),(2,3),...
        c = self.cos_t[pos_idx]           # [..., dh/2]
        sn = self.sin_t[pos_idx]
        x0 = x[..., 0::2]
        x1 = x[..., 1::2]
        o = torch.stack((x0 * c.unsqueeze(-2) - x1 * sn.unsqueeze(-2),
                         x0 * sn.unsqueeze(-2) + x1 * c.unsqueeze(-2)), dim=-1)
        return o.flatten(-2)

    def prefill(self, toks):
        s, h, dh, dm = self.s, self.h, self.dh, self.dm
        x = self.table[toks]                       # [s, dm]
        mask = torch.where(
            torch.tril(torch.ones(s, s, dtype=torch.bool, device=self.dev)),
            0.0, -1e30)
        for li in range(self.L):
            n1 = self.rms(x, self.rms1_g[li])
            q = (n1 @ self.wq[li]).view(s, h, dh)
            k = (n1 @ self.wk[li]).view(s, h, dh)
            v = (n1 @ self.wv[li]).view(s, h, dh)
            qr = self.rope(q, self.arange_s)
            kr = self.rope(k, self.arange_s)
            self.kc[li][:, :s] = kr.transpose(0, 1)
            self.vc[li][:, :s] = v.transpose(0, 1)
            sc = torch.einsum("shd,thd->hst", qr, kr) * self.scale
            p = torch.softmax(sc + mask, dim=-1)
            att = torch.einsum("hst,htd->shd", p, self.vc[li][:, :s])
            mha = att.reshape(s, dm) @ self.wo[li]
            r1 = x + mha
            n2 = self.rms(r1, self.rms2_g[li])
            sg = F.silu(n2 @ self.w1[li]) * (n2 @ self.w3[li])
            x = r1 + sg @ self.w2[li]
        return self.rms(x, self.rmsf_g) @ self.whead   # [s, v]

    def step(self, tok, pos):
        """单 decode 步：tok (标量 long tensor)，pos (标量 long tensor)。"""
        h, dh, dm = self.h, self.dh, self.dm
        x = self.table[tok]                          # [dm]
        pos1 = pos.view(1)
        mask = torch.where(self.arange_kv > pos, -1e30, 0.0)   # [kvmax]
        for li in range(self.L):
            n1 = self.rms(x, self.rms1_g[li])
            q = (n1 @ self.wq[li]).view(h, dh)
            k = (n1 @ self.wk[li]).view(h, dh)
            v = (n1 @ self.wv[li]).view(h, dh)
            qr = self.rope(q, pos1).squeeze(0)         # [h, dh]
            kr = self.rope(k, pos1).squeeze(0)
            self.kc[li].index_copy_(1, pos1, kr.unsqueeze(1))
            self.vc[li].index_copy_(1, pos1, v.unsqueeze(1))
            sc = (self.kc[li] * qr.unsqueeze(1)).sum(-1) * self.scale  # [h,kvmax]
            p = torch.softmax(sc + mask, dim=-1)
            att = (p.unsqueeze(-1) * self.vc[li]).sum(1)               # [h,dh]
            mha = att.reshape(dm) @ self.wo[li]
            r1 = x + mha
            n2 = self.rms(r1, self.rms2_g[li])
            sg = F.silu(n2 @ self.w1[li]) * (n2 @ self.w3[li])
            x = r1 + sg @ self.w2[li]
        return self.rms(x, self.rmsf_g) @ self.whead   # [v]

    def decode_loop(self, stepfn, first_tok):
        tok = first_tok
        rows = []
        for t in range(self.T):
            lg = stepfn(tok, torch.tensor(self.s + t, device=self.dev))
            rows.append(lg)
            tok = lg.argmax()
        return torch.stack(rows)


def bench(fn, warmup=5, reps=20):
    for _ in range(warmup):
        fn()
    torch.cuda.synchronize()
    ts = []
    t0 = torch.cuda.Event(enable_timing=True)
    t1 = torch.cuda.Event(enable_timing=True)
    for _ in range(reps):
        t0.record()
        fn()
        t1.record()
        torch.cuda.synchronize()
        ts.append(t0.elapsed_time(t1))
    ts.sort()
    return {"min_ms": ts[0], "median_ms": ts[len(ts) // 2]}


def main():
    bindir = sys.argv[1]
    s, h, dh, df, v, L, T, kvmax = (int(a) for a in sys.argv[2:10])
    reps = int(sys.argv[10]) if len(sys.argv) > 10 else 20
    dev = torch.device("cuda")
    m = LLaMAMiniTorch(bindir, s, h, dh, df, v, L, T, kvmax, dev)
    # 修改点：KV cache 原地写会导致 reduce-overhead 跳过 cudagraphs
    # （"skipping cudagraphs due to mutated inputs"）；按官方做法标记静态地址。
    for _li in range(m.L):
        torch._dynamo.mark_static_address(m.kc[_li])
        torch._dynamo.mark_static_address(m.vc[_li])
    b = Path(bindir)
    toks = torch.from_numpy(
        np.fromfile(b / "tok.bin", dtype=np.int32).astype(np.int64)).to(dev)
    ref_pre = np.fromfile(b / "ref_prefill.f64.bin", dtype=np.float64).reshape(s, v)
    ref_gen = np.fromfile(b / "ref_gen.f64.bin", dtype=np.float64).reshape(T + 1, v)

    out = {"device": torch.cuda.get_device_name(0), "torch": torch.__version__}
    with torch.inference_mode():
        # ---- eager ----
        lg = m.prefill(toks)
        first = lg[-1].argmax()
        gen = m.decode_loop(m.step, first)
        full = torch.cat((lg[-1:].double().cpu(), gen.double().cpu())).numpy()
        out["eager"] = {
            "prefill": bench(lambda: m.prefill(toks), reps=reps),
            "decode": bench(lambda: m.decode_loop(m.step, first), reps=reps),
            "err_prefill": float(np.max(np.abs(lg.double().cpu().numpy() - ref_pre))),
            "err_gen": float(np.max(np.abs(full - ref_gen))),
        }
        # ---- compile ----
        try:
            pre_c = torch.compile(m.prefill)
            step_c = torch.compile(m.step)
            lg2 = pre_c(toks)
            first2 = lg2[-1].argmax()
            gen2 = m.decode_loop(step_c, first2)
            full2 = torch.cat((lg2[-1:].double().cpu(), gen2.double().cpu())).numpy()
            out["compile"] = {
                "prefill": bench(lambda: pre_c(toks), reps=reps),
                "decode": bench(lambda: m.decode_loop(step_c, first2), reps=reps),
                "err_prefill": float(np.max(np.abs(lg2.double().cpu().numpy() - ref_pre))),
                "err_gen": float(np.max(np.abs(full2 - ref_gen))),
            }
        except Exception as e:  # noqa: BLE001
            out["compile_error"] = repr(e)[:500]
        # ---- compile mode="reduce-overhead" (CUDA graphs) ----
        # 修改点：新增块。warmup=10（>5）确保 cudagraph 捕获/树稳定后再计时，
        # warmup 不计入。正确性快照在 bench 的 replay 之前先拷到 CPU（cudagraph
        # trees 会把后续 run 之前的 graph 输出判为 overwritten）。
        first_cg = first
        try:
            pre_g = torch.compile(m.prefill, mode="reduce-overhead")
            lg3 = pre_g(toks)
            lg3_np = lg3.double().cpu().numpy()  # 快照，防后续 replay 过期
            first_cg = lg3[-1].argmax()
            out["cudagraphs_prefill"] = {
                "prefill": bench(lambda: pre_g(toks), warmup=10, reps=reps),
                "err_prefill": float(np.max(np.abs(lg3_np - ref_pre))),
            }
        except Exception as e:  # noqa: BLE001
            out["cudagraphs_prefill_error"] = repr(e)[:800]
        try:
            step_g = torch.compile(m.step, mode="reduce-overhead")

            # cudagraphs 版 decode 循环：每步前 cudagraph_mark_step_begin()；
            # graph 输出不得跨 replay 持有（否则 overwritten-stale 报错）。
            # keep 版逐步 clone 用于正确性核对；fast 版即时消费（argmax 反馈），
            # 与基线 decode_loop 的差异仅在于不累积 rows/末栈（T×v 浮点，
            # 开销可忽略）。
            def cg_keep(stepfn, first_tok):
                tok = first_tok
                rows = []
                for t in range(m.T):
                    torch.compiler.cudagraph_mark_step_begin()
                    lg = stepfn(tok, torch.tensor(m.s + t, device=m.dev))
                    rows.append(lg.clone())
                    tok = lg.argmax()
                return torch.stack(rows)

            def cg_fast(stepfn, first_tok):
                tok = first_tok
                for t in range(m.T):
                    torch.compiler.cudagraph_mark_step_begin()
                    lg = stepfn(tok, torch.tensor(m.s + t, device=m.dev))
                    tok = lg.argmax()
                return tok

            gen3 = cg_keep(step_g, first_cg)
            pre_row = lg3_np[-1] if "cudagraphs_prefill" in out \
                else lg[-1].double().cpu().numpy()
            full3 = np.concatenate(
                (pre_row[None], gen3.double().cpu().numpy())).astype(np.float64)
            out["cudagraphs_decode"] = {
                "decode": bench(lambda: cg_fast(step_g, first_cg),
                                warmup=10, reps=reps),
                "err_gen": float(np.max(np.abs(full3 - ref_gen))),
            }
        except Exception as e:  # noqa: BLE001
            out["cudagraphs_decode_error"] = repr(e)[:800]
    print("JSON " + json.dumps(out))


if __name__ == "__main__":
    main()
