# Artifact — Verified Optimization by Analytic Rewrite Rules (Paper B)

Open-source evidence for the paper *Verified Optimization by Analytic Rewrite
Rules: Online Softmax and Flash-Attention-Style Reordering* (OOPSLA 2027
Round 1 submission, anonymized). It contains everything needed to re-verify
the paper's theorem claims, reproduce its numerical-validation claims on a
GPU, and rerun its performance protocol.

## Layout

```
coq/                 the Ionia mechanization (Rocq/Coq), full library
  src/Ionia/*.v      86 files; Paper B's theorems live in
                     Opt_OnlineSoftmax.v (analytic rule),
                     Opt_OnlineSoftmax_Acc.v (the full (m,l,a) weighted-accumulator
                     variant: online_merge_all_v_correct, online_merge_all_v_output),
                     and
                     Opt_Tiling.v / Opt_Fusion.v / Opt_ParGranularity.v
                     (structural rules). The remaining files are shared
                     infrastructure also consumed by the companion papers
                     (rule-set metatheory, network end-to-end theorems,
                     stateful semantics, error bounds).
  _CoqProject, Makefile
kernels/             fused-attention kernel and its validation harness
  fused_attention.cu   unfused 13-kernel chain AND fused 5-launch kernel
                       (k_fused_attn) in one translation unit
  validate_fused_attention.py
                     fixed-seed input generation, nvcc compile, GPU run,
                     float64 NumPy reference comparison, CUDA-event timing
benchmarks/          performance protocol scripts (LLaMA-mini S/M/L vs PyTorch)
scripts/             axiom audit for Paper B's theorems
LICENSE              MIT
```

## Claim ↔ evidence map

| Paper claim | Evidence | Reproduce |
|---|---|---|
| Online-softmax equivalence and arbitrary-blocking generalization (Thms. `online_softmax_equiv`, `online_merge_correct`, `online_merge_all_correct`), rebasing identity `esum_scale`, positivity `softmax_denom_pos`; full (m,l,a) flash-state variant (`online_merge_all_v_correct`, `online_merge_all_v_output`) | `coq/src/Ionia/Opt_OnlineSoftmax.v`, `coq/src/Ionia/Opt_OnlineSoftmax_Acc.v` | build `coq/`, see below |
| Structural rules `seqfor_split`, `map_fusion`, `parfor_coarsen` | `coq/src/Ionia/Opt_Tiling.v`, `Opt_Fusion.v`, `Opt_ParGranularity.v` | build `coq/`, see below |
| Zero `Admitted`; only standard classical axioms | `scripts/print_assumptions_B.v` | `./scripts/run_audit.sh` |
| Fused kernel validates against float64 references at ≤ 6.7e-7 on four shapes; fused-vs-unfused ≤ 2.1e-7 | `kernels/` | see below |
| Unfused chain = 13 launches, fused = 5 | `fused_attention.cu` (`k_*` chain vs `k_fused_attn`) | see below |
| Attention-stage speedups (paper §6.2: 9.6–13.9× small shapes; ~3.1× attention core at (2,8,512,64); 1.8–2.0× whole chain) | timing block of `validate_fused_attention.py` | see below (machine-dependent) |
| End-to-end latency table (S/M/L vs torch.compile) | `benchmarks/` (protocol scripts) | see below (requires PyTorch) |

## Requirements

- Rocq 9.2.0 (formerly Coq) — the artifact was built with opam switch
  4.14.1 (`COQBIN=/home/chen/.opam/4.14.1/bin`). Any Rocq 9.2 install works.
- CUDA 12.9 `nvcc` on `PATH` (used: `/home/chen/cuda-12.9/bin/nvcc`).
- Python 3 with NumPy. A CUDA GPU is required for the kernel validation;
  the paper's numbers were measured on an RTX PRO 4000 (sm_120).
- PyTorch (FP32) only for `benchmarks/`.

## 1. Build the mechanization

```bash
cd coq
make            # rocq makefile -f _CoqProject -o Makefile.coq && make -f Makefile.coq -j8
```

Expected: all 86 files compile with zero errors and zero `Admitted`.

## 2. Axiom audit (Paper B's theorems)

```bash
./scripts/run_audit.sh
```

Expected tail: `OK: only standard library axioms are used.` The audit prints
`Print Assumptions` for the nine online-softmax theorems and the three
structural rules of the claim map.

## 3. Reproduce the kernel validation

```bash
cd kernels
python3 validate_fused_attention.py
```

The script generates its own inputs (fixed seed 20260914), compiles
`fused_attention.cu` (`-O2 -arch=native`), runs both the unfused 13-kernel
chain and the fused kernel on the GPU, compares against a float64 stable-
softmax NumPy reference (tolerance 1e-5), and times with CUDA events
(5 warmup + 20 reps, min/median).

Expected result (verified on the paper's GPU class, 2026-10-05):
`OVERALL: PASS`; per-shape max-abs errors 8.9e-08, 2.1e-07, 6.7e-07, 6.0e-07
for shapes (1,2,8,16), (1,4,64,32), (1,8,256,64), (2,8,512,64); fused-vs-
unfused max-abs difference ≤ 2.1e-07. Timing columns are machine-state
dependent and will vary; the launch-count structure (13 → 5) will not.

## 4. Rerun the performance protocol

```bash
cd benchmarks
python3 torch_llamamini_bench.py     # PyTorch reference (eager + torch.compile)
NVCC=$(which nvcc) TORCH_PY=<torch-env>/bin/python python3 bench_llamamini_l4.py
# torch_llamamini_bench_cg.py: default + reduce-overhead (CUDA Graph) torch baseline used for
# the paper's Table 2 compile-g column; raw logs in logs/cg_bench_*.log
# smoke_l4_s.py / bench_torch_baseline.py: protocol variants used for the table
```

All configurations are single-request FP32, GPU-only timing, min of 20
repetitions, weights resident, seeds fixed. The decode-chain measurement uses
CUDA Graph replay; the `torch.compile` baseline is default mode (without
`reduce-overhead` graph capture) — the paper states this asymmetry
explicitly.

## Scope and honesty notes

- The verified core ends at command semantics over ℝ; the CUDA kernels in
  `kernels/` are engineering counterparts whose *reordering* is the proved
  rule and whose *bodies* are validated numerically (this is the paper's
  stated trust boundary).
- The full library is shipped because the structural rules Paper B consumes
  are proved in files that the companion papers also claim; nothing in this
  artifact claims the companion papers' theorems (network-level end-to-end
  theorems, KV-cache/generation semantics, error bounds) — those are mapped
  in the siblings' artifacts.
