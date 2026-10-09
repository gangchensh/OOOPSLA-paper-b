#!/usr/bin/env python3
"""validate_fused_attention.py — L3 融合注意力 kernel 数值验证 + 性能对照.

流程：对每个形状 (b,h,s,d) 生成输入 bin（seed 固定）→ nvcc 编译
fused_attention.cu（一次）→ GPU 运行 → 读 fatt_out_chain/fused.bin →
NumPy float64 参考（稳定 softmax MHA，含 causal mask）逐元素对比
（atol=rtol=1e-5）→ 汇总计时（min/median，CUDA events）。

Env: NVCC (default /tmp/cuda-12.9-debs/usr/local/cuda-12.9/bin/nvcc),
     NVCC_FLAGS (default "-O2 -arch=native").
"""
import os
import shutil
import subprocess
import sys

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
LOGDIR = os.environ.get("LOGDIR", os.path.join(HERE, "logs"))
NVCC = os.environ.get("NVCC", shutil.which("nvcc") or "nvcc")
NVCC_FLAGS = os.environ.get("NVCC_FLAGS", "-O2 -arch=native").split()

SHAPES = [
    (1, 2, 8, 16),    # L1 mha_block_test 基线形状
    (1, 4, 64, 32),
    (1, 8, 256, 64),
    (2, 8, 512, 64),
]
REPS = 20
SEED = 20260914


def run(cmd, **kw):
    r = subprocess.run(cmd, capture_output=True, text=True, cwd=HERE, **kw)
    if r.returncode != 0:
        print(r.stdout)
        print(r.stderr)
        raise SystemExit(f"command failed: {' '.join(cmd)}")
    return r


def gen_inputs(b, h, s, d, seed):
    dm = h * d
    rng = np.random.default_rng(seed)
    x = rng.standard_normal((b, s, dm), dtype=np.float64) * 0.5
    # He-like 缩放（与 validate_cuda_llm.py 同约定）
    ws = [rng.standard_normal((dm, dm)) * np.sqrt(2.0 / dm) * 0.5 for _ in range(4)]
    for name, arr in [("fatt_input.bin", x)] + [
        (f"fatt_w{n}.bin", w) for n, w in zip(["q", "k", "v", "o"], ws)
    ]:
        arr.astype(np.float32).tofile(os.path.join(HERE, name))
    return x, ws


def reference(x, ws, h):
    b, s, dm = x.shape
    d = dm // h
    wq, wk, wv, wo = ws
    q = (x @ wq).reshape(b, s, h, d).transpose(0, 2, 1, 3)
    k = (x @ wk).reshape(b, s, h, d).transpose(0, 2, 1, 3)
    v = (x @ wv).reshape(b, s, h, d).transpose(0, 2, 1, 3)
    sc = q @ k.transpose(0, 1, 3, 2) / np.sqrt(d)
    mask = np.triu(np.ones((s, s), dtype=bool), k=1)
    sc = np.where(mask, -np.inf, sc)
    p = np.exp(sc - sc.max(axis=-1, keepdims=True))
    p = p / p.sum(axis=-1, keepdims=True)
    att = (p @ v).transpose(0, 2, 1, 3).reshape(b, s, dm)
    return att @ wo


def check(name, got, ref):
    err = np.max(np.abs(got - ref))
    denom = np.maximum(np.abs(ref), 1e-12)
    rel = np.max(np.abs(got - ref) / denom)
    ok = np.allclose(got, ref, atol=1e-5, rtol=1e-5)
    print(f"  {name}: max abs err = {err:.3e}, max rel err = {rel:.3e} "
          f"-> {'PASS' if ok else 'FAIL'}")
    return ok, err


def main():
    os.makedirs(LOGDIR, exist_ok=True)
    log_path = os.path.join(LOGDIR, "validate_fused_attention.log")
    tee = open(log_path, "w")

    def log(msg):
        print(msg)
        tee.write(msg + "\n")

    run([NVCC, *NVCC_FLAGS, "-o", "fused_attention", "fused_attention.cu"])
    log(f"compiled: {NVCC} {' '.join(NVCC_FLAGS)}")

    all_ok = True
    summary = []
    for si, (b, h, s, d) in enumerate(SHAPES):
        log(f"\n=== shape b={b} h={h} s={s} d={d} dm={h*d} ===")
        x, ws = gen_inputs(b, h, s, d, SEED + si)
        ref = reference(x, ws, h)
        r = run(["./fused_attention", str(b), str(h), str(s), str(d), str(REPS)])
        log(r.stdout.rstrip())
        out_c = np.fromfile(os.path.join(HERE, "fatt_out_chain.bin"),
                            dtype=np.float32).reshape(b, s, h * d).astype(np.float64)
        out_f = np.fromfile(os.path.join(HERE, "fatt_out_fused.bin"),
                            dtype=np.float32).reshape(b, s, h * d).astype(np.float64)
        ok1, e1 = check("chain13 vs numpy", out_c, ref)
        ok2, e2 = check("fused   vs numpy", out_f, ref)
        err_cf = np.max(np.abs(out_c - out_f))
        log(f"  fused vs chain: max abs diff = {err_cf:.3e}")
        all_ok = all_ok and ok1 and ok2
        t = {}
        for line in r.stdout.splitlines():
            parts = line.split()
            if len(parts) == 3 and parts[0] in ("TIME", "TIMEMED"):
                t[(parts[0], parts[1])] = float(parts[2])
        summary.append(((b, h, s, d), e1, e2, t))

    log("\n=== 性能汇总（ms，min/median，CUDA events，20 reps 5 warmup）===")
    hdr = ("shape", "chain13_sync", "chain13_nosync", "fused5",
           "core5", "core1", "speedup(sync)", "speedup(core)")
    log("\t".join(hdr))
    for (b, h, s, d), e1, e2, t in summary:
        cs = t.get(("TIME", "chain13_sync"), float("nan"))
        cn = t.get(("TIME", "chain13_nosync"), float("nan"))
        f5 = t.get(("TIME", "fused5"), float("nan"))
        c5 = t.get(("TIME", "core5_nosync"), float("nan"))
        c1 = t.get(("TIME", "core1_fused"), float("nan"))
        log(f"({b},{h},{s},{d})\t{cs:.4f}\t{cn:.4f}\t{f5:.4f}\t{c5:.4f}\t{c1:.4f}"
            f"\t{cs/f5:.2f}x\t{c5/c1:.2f}x")
    log(f"\n误差汇总: " + "; ".join(
        f"{shp}: chain={e1:.2e} fused={e2:.2e}" for shp, e1, e2, _ in summary))
    log(f"\nOVERALL: {'PASS' if all_ok else 'FAIL'}")
    tee.close()
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
