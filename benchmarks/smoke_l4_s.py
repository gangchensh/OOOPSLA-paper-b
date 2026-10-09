#!/usr/bin/env python3
"""S 配置烟测（不进交付）：生成 bin + 跑 binary + 对比 f64 参考。"""
import subprocess
import sys
from pathlib import Path

import numpy as np

import bench_llamamini_l4 as drv

cfg = drv.CONFIGS["S"]
p = drv.make_params(cfg)
toks = drv.make_prompt(cfg)
bindir = Path("l4_bench/S")
bindir.mkdir(parents=True, exist_ok=True)
for wname, arr in p.items():
    drv.f32(arr).tofile(bindir / f"{wname}.bin")
toks.tofile(bindir / "tok.bin")
np.array([np.float32(drv.EPS)]).tofile(bindir / "rms_eps.bin")
np.array([np.float32(drv.ROPE_BASE)]).tofile(bindir / "rope_base.bin")
ref_logits, _ = drv.ref_forward(cfg, p, toks)
ref_gen = drv.ref_generate(cfg, p, toks)
ref_logits.tofile(bindir / "ref_prefill.f64.bin")
ref_gen.tofile(bindir / "ref_gen.f64.bin")
same = all((bindir / f"{w}.bin").read_bytes()
           == Path(f"llamamini_test_{w}.bin").read_bytes() for w in p)
print("bins identical to L2 validate inputs:", same)
r = subprocess.run(["./llamamini_scale_bench", str(bindir), "8", "2", "16",
                    "32", "8", "2", "6", "14", "20", "2"],
                   capture_output=True, text=True)
print(r.stdout)
print(r.stderr, file=sys.stderr)
for name, ref in (("out_naive_prefill.bin", ref_logits),
                  ("out_naive_gen.bin", ref_gen),
                  ("out_opt_prefill.bin", ref_logits),
                  ("out_opt_gen.bin", ref_gen)):
    o = np.fromfile(bindir / name, dtype=np.float32).reshape(ref.shape)
    err = np.max(np.abs(o.astype(np.float64) - ref))
    am = np.array_equal(np.argmax(o, -1), np.argmax(ref, -1))
    print(f"{name}: max_err={err:.3e} argmax={am}")
