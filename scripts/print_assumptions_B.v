(* Axiom audit for Paper B (analytic rewrite rules / online softmax).
   Run after a full build (from the artifact root):
     ./scripts/run_audit.sh
   Expected: every theorem below closes over only the standard classical
   axioms (functional extensionality, proof irrelevance, classical logic,
   and real-number axioms from the Reals library). No Admitted, no custom
   axioms. *)

From Ionia Require Import Opt_OnlineSoftmax.
From Ionia Require Import Opt_OnlineSoftmax_Acc.
From Ionia Require Import Opt_Tiling Opt_Fusion Opt_ParGranularity.

(* ---- Analytic rule: online softmax (Opt_OnlineSoftmax.v) ---- *)
Print Assumptions Ionia.Opt_OnlineSoftmax.esum_scale.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_merge_correct.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_fold_correct.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_softmax_equiv.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_merge_all_correct.
Print Assumptions Ionia.Opt_OnlineSoftmax_Acc.online_merge_all_v_correct.
Print Assumptions Ionia.Opt_OnlineSoftmax_Acc.online_merge_all_v_output.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_merge_two_blocks.
Print Assumptions Ionia.Opt_OnlineSoftmax.softmax_denom_pos.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_loop_spec.
Print Assumptions Ionia.Opt_OnlineSoftmax.online_loop_computes_denominator.

(* ---- Structural rules consumed by the paper (companion rule set) ---- *)
Print Assumptions Ionia.Opt_Tiling.seqfor_split.
Print Assumptions Ionia.Opt_Fusion.map_fusion.
Print Assumptions Ionia.Opt_ParGranularity.parfor_coarsen.
