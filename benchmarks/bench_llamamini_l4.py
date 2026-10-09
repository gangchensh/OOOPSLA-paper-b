#!/usr/bin/env python3
"""L4 驱动：LLaMA-mini 规模梯度 + 三方对照（规划 doc/LLM编译工作规划_20260913.md §2-L4）。

对 3 个递增配置（S/M/L）：
  1. 生成权重 bin（S 配置与 validate_llamamini.py 完全同种子同顺序——可直接
     复用 L2 已验证的生成程序做交叉校验）；
  2. 运行 llamamini_scale_bench.cu（naive 镜像链 + opt 链），CUDA events
     5 warmup + 20 reps，min/median，不含 H2D/D2H（搬移单列）；
  3. float64 NumPy 参考（validate_llamamini.py 参考的推广：L 层、任意维度），
     naive/opt 输出逐一对比（atol=rtol=1e-5 + argmax 一致）；
  4. S 配置交叉校验：用同一份 bin 跑 L2 生成程序 llamamini_test / llamagen_test；
  5. 同配置手写 PyTorch 参考模型 eager/compile 时延（torch_llamamini_bench.py，
     torch_env），同权重同口径；
  6. 汇总三方对照表 + JSON 落盘。

Env: NVCC（默认取 PATH 中的 nvcc）、TORCH_PY（默认 /home/chen/torch_env/bin/python，
     请指向本机的 PyTorch 环境）、REPS（默认 20）
     SKIP_TORCH=1 跳过 PyTorch 对照。
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path

import numpy as np

HERE = Path(__file__).resolve().parent
os.chdir(HERE)

NVCC = os.environ.get("NVCC", __import__("shutil").which("nvcc") or "nvcc")
NVCC_FLAGS = os.environ.get("NVCC_FLAGS", "-O2 -arch=native").split()
TORCH_PY = os.environ.get("TORCH_PY", "/home/chen/torch_env/bin/python")
REPS = int(os.environ.get("REPS", "20"))
SKIP_TORCH = os.environ.get("SKIP_TORCH", "") == "1"
ATOL = 1e-5
RTOL = 1e-5
EPS = 1e-5
ROPE_BASE = 10000.0

# 配置梯度：S = L2 的 Small_1_8_2_8（交叉校验锚点），M/L 递增
CONFIGS = {
    "S": dict(s=8, h=2, dh=16, df=32, v=8, L=2, T=6, kvmax=14,
              seed=20260914, he=False),
    "M": dict(s=64, h=4, dh=32, df=512, v=128, L=4, T=8, kvmax=72,
              seed=20260915, he=True),
    "L": dict(s=128, h=8, dh=64, df=2048, v=512, L=4, T=8, kvmax=136,
              seed=20260916, he=True),
}


def f32(a):
    return np.ascontiguousarray(a, dtype=np.float32)


def make_params(cfg):
    """S 配置与 validate_llamamini.py 逐字节一致（同 seed、同抽取顺序）；
    M/L 用 He 式缩放（sigma = 0.15*sqrt(32/fan_in)）控制 float32 误差传播。"""
    rng = np.random.default_rng(cfg["seed"])
    dm, df, v, L = cfg["h"] * cfg["dh"], cfg["df"], cfg["v"], cfg["L"]
    he = cfg["he"]

    def mat(shape):
        fan_in = shape[0]
        sig = 0.15 * np.sqrt(32.0 / fan_in) if he else 0.15
        return f32(rng.standard_normal(shape) * sig)

    p = {}
    p["table"] = f32(rng.standard_normal((v, dm)) * 0.5)
    for li in range(1, L + 1):
        pfx = f"l{li}"
        p[f"{pfx}_rms1_g"] = f32(1.0 + 0.1 * rng.standard_normal(dm))
        p[f"{pfx}_rms2_g"] = f32(1.0 + 0.1 * rng.standard_normal(dm))
        for w in ("wq", "wk", "wv", "wo"):
            p[f"{pfx}_{w}"] = mat((dm, dm))
        p[f"{pfx}_w1"] = mat((dm, df))
        p[f"{pfx}_w3"] = mat((dm, df))
        p[f"{pfx}_w2"] = mat((df, dm))
    p["rmsf_g"] = f32(1.0 + 0.1 * rng.standard_normal(dm))
    p["whead"] = mat((dm, v))
    return p


def make_prompt(cfg):
    if not cfg["he"]:  # S：与 L2 生成程序硬编码的 prompt 一致
        return np.array([3, 1, 4, 1, 5, 2, 6, 0], dtype=np.int32)
    rng = np.random.default_rng(cfg["seed"] + 1000)
    return rng.integers(0, cfg["v"], size=cfg["s"]).astype(np.int32)


# ---------------------------------------------------------------------------
# float64 参考（validate_llamamini.py 的推广：L 层、任意维度）

def rms(x, g):
    x = np.asarray(x, dtype=np.float64)
    ms = (x ** 2).mean(axis=-1, keepdims=True)
    return (x / np.sqrt(ms + EPS)) * np.asarray(g, dtype=np.float64)


def rope_rows(x, dh, pos0=0):
    """x: [s, dm]；行 i 的绝对位置 pos0+i。返回同形。"""
    x = np.asarray(x, dtype=np.float64)
    s, dm = x.shape
    out = np.zeros_like(x)
    for i in range(s):
        for p in range(dh // 2):
            th = (pos0 + i) * ROPE_BASE ** (-(2.0 * p) / dh)
            for hd in range(dm // dh):
                b = hd * dh + 2 * p
                x0, x1 = x[i, b], x[i, b + 1]
                out[i, b] = x0 * np.cos(th) - x1 * np.sin(th)
                out[i, b + 1] = x0 * np.sin(th) + x1 * np.cos(th)
    return out


def ref_forward(cfg, p, toks):
    """返回 (logits[s,v], [(kr_sdm, v_sdm) per layer])，k/v 为 (s,dm) 布局。"""
    h, dh, dm, df, v = cfg["h"], cfg["dh"], cfg["h"] * cfg["dh"], cfg["df"], cfg["v"]
    s = cfg["s"]
    scale = 1.0 / np.sqrt(dh)
    x = np.asarray(p["table"], dtype=np.float64)[toks]  # [s, dm]
    caches = []
    for li in range(1, cfg["L"] + 1):
        pfx = f"l{li}"
        n1 = rms(x, p[f"{pfx}_rms1_g"])
        q = n1 @ p[f"{pfx}_wq"]
        k = n1 @ p[f"{pfx}_wk"]
        vv = n1 @ p[f"{pfx}_wv"]
        qr = rope_rows(q, dh)
        kr = rope_rows(k, dh)
        caches.append((kr.copy(), vv.copy()))
        # 注意力：按头分块
        ao = np.zeros_like(x)
        for hi in range(h):
            sl = slice(hi * dh, (hi + 1) * dh)
            sc = (qr[:, sl] @ kr[:, sl].T) * scale
            mask = np.tril(np.ones((s, s), dtype=bool))
            msc = np.where(mask, sc, -1e30)
            e = np.exp(msc)
            pb = e / e.sum(axis=-1, keepdims=True)
            ao[:, sl] = pb @ vv[:, sl]
        mha = ao @ p[f"{pfx}_wo"]
        r1 = x + mha
        n2 = rms(r1, p[f"{pfx}_rms2_g"])
        sg = (lambda u: (u / (1.0 + np.exp(-u))))(n2 @ p[f"{pfx}_w1"]) * (n2 @ p[f"{pfx}_w3"])
        f2 = sg @ p[f"{pfx}_w2"]
        x = r1 + f2
    xf = rms(x, p["rmsf_g"])
    logits = xf @ np.asarray(p["whead"], dtype=np.float64)
    return logits, caches


def ref_generate(cfg, p, toks):
    h, dh, dm, v = cfg["h"], cfg["dh"], cfg["h"] * cfg["dh"], cfg["v"]
    s, T, kvmax = cfg["s"], cfg["T"], cfg["kvmax"]
    scale = 1.0 / np.sqrt(dh)
    logits, caches = ref_forward(cfg, p, toks)
    kc = [np.zeros((h, kvmax, dh)) for _ in range(cfg["L"])]
    vc = [np.zeros((h, kvmax, dh)) for _ in range(cfg["L"])]
    for li, (kr, vv) in enumerate(caches):
        for hi in range(h):
            kc[li][hi, :s] = kr[:, hi * dh:(hi + 1) * dh]
            vc[li][hi, :s] = vv[:, hi * dh:(hi + 1) * dh]
    gen = np.zeros((T + 1, v))
    gen[0] = logits[s - 1]
    tok = int(np.argmax(gen[0]))
    for t in range(T):
        pos = s + t
        x = np.asarray(p["table"], dtype=np.float64)[tok][None]  # [1, dm]
        for li in range(1, cfg["L"] + 1):
            pfx = f"l{li}"
            n1 = rms(x, p[f"{pfx}_rms1_g"])
            q = n1 @ p[f"{pfx}_wq"]
            k = n1 @ p[f"{pfx}_wk"]
            vv = n1 @ p[f"{pfx}_wv"]
            qr = rope_rows(q, dh, pos0=pos)
            kr = rope_rows(k, dh, pos0=pos)
            for hi in range(h):
                kc[li - 1][hi, pos] = kr[0, hi * dh:(hi + 1) * dh]
                vc[li - 1][hi, pos] = vv[0, hi * dh:(hi + 1) * dh]
            ao = np.zeros_like(x)
            for hi in range(h):
                sl = slice(hi * dh, (hi + 1) * dh)
                sc = (kc[li - 1][hi, :pos + 1] @ qr[0, sl]) * scale
                e = np.exp(sc)
                pb = e / e.sum()
                ao[0, sl] = pb @ vc[li - 1][hi, :pos + 1]
            mha = ao @ p[f"{pfx}_wo"]
            r1 = x + mha
            n2 = rms(r1, p[f"{pfx}_rms2_g"])
            sg = (lambda u: (u / (1.0 + np.exp(-u))))(n2 @ p[f"{pfx}_w1"]) * (n2 @ p[f"{pfx}_w3"])
            x = r1 + sg @ p[f"{pfx}_w2"]
        xf = rms(x, p["rmsf_g"])
        lg = (xf @ np.asarray(p["whead"], dtype=np.float64))[0]
        gen[t + 1] = lg
        tok = int(np.argmax(lg))
    return gen


# ---------------------------------------------------------------------------

def run(cmd, log, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, **kw)
    log.write(f"$ {' '.join(str(c) for c in cmd)}\n")
    log.write(r.stdout)
    if r.returncode != 0:
        log.write(r.stderr)
        log.flush()
        raise SystemExit(f"command failed: {' '.join(str(c) for c in cmd)}")
    log.flush()
    return r


def parse_times(stdout, prefix=""):
    out = {}
    for ln in stdout.splitlines():
        parts = ln.split()
        if len(parts) == 3 and parts[0] in ("TIME", "TIMEMED"):
            out[f"{prefix}{parts[0].lower()}_{parts[1]}"] = float(parts[2])
        elif len(parts) == 2 and parts[0].startswith("MEMTIME"):
            out[f"{prefix}{parts[0].lower()}"] = float(parts[1])
    return out


def compare(out_file, ref, label, results):
    out = np.fromfile(out_file, dtype=np.float32).reshape(ref.shape)
    err = float(np.max(np.abs(out.astype(np.float64) - ref)))
    ok = bool(np.allclose(out.astype(np.float64), ref, atol=ATOL, rtol=RTOL))
    tok_ok = bool(np.array_equal(np.argmax(out, axis=-1), np.argmax(ref, axis=-1)))
    print(f"  {label:40s} max_err={err:.3e}  pass={ok}  argmax_match={tok_ok}")
    results.append(ok and tok_ok)
    return err


def main():
    log_dir = Path("../../work/build_logs/20260914")
    log_dir.mkdir(parents=True, exist_ok=True)
    log = open(log_dir / "llm_l4_bench.log", "w")
    log.write(f"# L4 bench log {time.strftime('%F %T')}\n# NVCC={NVCC} REPS={REPS}\n")

    # 编译（一次，维度全运行时）
    run([NVCC, *NVCC_FLAGS, "-o", "llamamini_scale_bench",
         "llamamini_scale_bench.cu"], log)

    summary = {}
    n_fail = 0
    for name, cfg in CONFIGS.items():
        dm = cfg["h"] * cfg["dh"]
        print(f"\n=== 配置 {name}: s={cfg['s']} h={cfg['h']} dh={cfg['dh']} "
              f"dm={dm} df={cfg['df']} v={cfg['v']} L={cfg['L']} T={cfg['T']} ===")
        bindir = HERE / "l4_bench" / name
        bindir.mkdir(parents=True, exist_ok=True)
        p = make_params(cfg)
        toks = make_prompt(cfg)
        for wname, arr in p.items():
            f32(arr).tofile(bindir / f"{wname}.bin")
        toks.tofile(bindir / "tok.bin")
        np.array([np.float32(EPS)]).tofile(bindir / "rms_eps.bin")
        np.array([np.float32(ROPE_BASE)]).tofile(bindir / "rope_base.bin")

        ref_logits, _ = ref_forward(cfg, p, toks)
        ref_gen = ref_generate(cfg, p, toks)
        ref_logits.tofile(bindir / "ref_prefill.f64.bin")
        ref_gen.tofile(bindir / "ref_gen.f64.bin")

        entry = {"dims": {k: cfg[k] for k in ("s", "h", "dh", "df", "v", "L", "T", "kvmax")},
                 "dm": dm}
        results = []

        # ---- 我们的 naive + opt ----
        r = run(["./llamamini_scale_bench", str(bindir), str(cfg["s"]),
                 str(cfg["h"]), str(cfg["dh"]), str(cfg["df"]), str(cfg["v"]),
                 str(cfg["L"]), str(cfg["T"]), str(cfg["kvmax"]), str(REPS),
                 "2"], log)
        entry["ours"] = parse_times(r.stdout)
        for ln in r.stdout.splitlines():
            if ln.startswith(("SHAPE", "TIME", "TIMEMED", "MEMTIME")):
                print("  " + ln)
        entry["ours"]["err_naive_prefill"] = compare(
            bindir / "out_naive_prefill.bin", ref_logits, "naive prefill vs f64", results)
        entry["ours"]["err_naive_gen"] = compare(
            bindir / "out_naive_gen.bin", ref_gen, "naive genlogits vs f64", results)
        entry["ours"]["err_opt_prefill"] = compare(
            bindir / "out_opt_prefill.bin", ref_logits, "opt prefill vs f64", results)
        entry["ours"]["err_opt_gen"] = compare(
            bindir / "out_opt_gen.bin", ref_gen, "opt genlogits vs f64", results)
        entry["ours"]["err_opt_graph_gen"] = compare(
            bindir / "out_opt_graph_gen.bin", ref_gen, "opt graph genlogits vs f64", results)

        # ---- S 配置：L2 生成程序交叉校验 ----
        if name == "S":
            for net in ("llamamini_test", "llamagen_test"):
                for wname, arr in p.items():
                    f32(arr).tofile(f"{net}_{wname}.bin")
                toks.tofile(f"{net}_tok.bin")
                np.array([np.float32(EPS)]).tofile(f"{net}_rms_eps.bin")
                np.array([np.float32(ROPE_BASE)]).tofile(f"{net}_rope_base.bin")
            np.array([np.int32(0)]).tofile("llamagen_test_kv_t.bin")
            r = run(["./llamamini_test"], log)
            entry["generated"] = parse_times(r.stdout, "prefill_")
            compare("llamamini_test_output.bin", ref_logits[None],
                    "generated llamamini_test vs f64", results)
            r = run(["./llamagen_test"], log)
            entry["generated"].update(parse_times(r.stdout, "gen_"))
            compare("llamagen_test_output.bin", ref_gen,
                    "generated llamagen_test vs f64", results)

        # ---- PyTorch eager/compile ----
        if not SKIP_TORCH:
            r = run([TORCH_PY, "torch_llamamini_bench.py", str(bindir),
                     str(cfg["s"]), str(cfg["h"]), str(cfg["dh"]),
                     str(cfg["df"]), str(cfg["v"]), str(cfg["L"]),
                     str(cfg["T"]), str(cfg["kvmax"]), str(REPS)], log)
            for ln in r.stdout.splitlines():
                if ln.startswith("JSON "):
                    entry["torch"] = json.loads(ln[5:])
            if "torch" in entry:
                t = entry["torch"]
                for mode in ("eager", "compile"):
                    if mode in t:
                        print(f"  torch {mode:8s} prefill min={t[mode]['prefill']['min_ms']:.3f} "
                              f"decode min={t[mode]['decode']['min_ms']:.3f} "
                              f"err_pre={t[mode]['err_prefill']:.2e} err_gen={t[mode]['err_gen']:.2e}")
                    elif mode + "_error" in t:
                        print(f"  torch {mode}: FAILED {t[mode + '_error'][:200]}")
            else:
                print("  torch: no JSON output (see log)")
                results.append(False)

        n_fail += sum(1 for ok in results if not ok)
        summary[name] = entry

    with open(log_dir / "llm_l4_results.json", "w") as f:
        json.dump(summary, f, indent=2)
    print(f"\n# results -> {log_dir}/llm_l4_results.json")
    print(f"{n_fail} validation failures")
    log.close()
    sys.exit(1 if n_fail else 0)


if __name__ == "__main__":
    main()
