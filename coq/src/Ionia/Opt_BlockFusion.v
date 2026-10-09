(* E1: whole-block fusion theorem for the ResNet BasicBlock (identity
   shortcut), route A / DPIA rule layer.

   The seven-step chain
     conv3x3 -> BN -> ReLU -> conv3x3 -> BN -> Add(residual) -> ReLU
   ([ResNet18_DPIA.BasicBlock_id]) is shown equal, as a Leibniz equality of
   commands, to a fused single kernel [BasicBlock_fused_comm] whose only
   assignments are to the output cells (plus the scalar accumulators
   internal to [suml]): no intermediate feature-map buffer is ever written
   or read.  This is exactly the semantic content of fusion eliminating the
   DRAM traffic of the five intermediate tensors (c1, n1, r1, c2, n2, a2).

   Proof technique (value-semantics inlining):
   - The stage-1 output [relu (bn (conv1 x))] is kept as a *pure
     expression* [BB_mid1] (register/buffer-resident value); the second
     convolution reads it directly — the expression-level instance of the
     [bind_read_replace] family, so no freshness/disjointness premise is
     needed at all.
   - The BN2 statistics (mean/variance over the conv2 output channel
     slice) and the conv2 channel reduction are chained on the output cell
     accumulator via [C_sum_post3_acc] (Opt_TiledConv) /
     [C_sum_post2_acc] / [C_sum_post_acc]; the residual Add and the final
     ReLU branch are folded into the innermost continuation
     ([A_relu_add_bn_conv_cell], mirroring [A_relu_bn_conv_cell]).

   All proofs are [Qed]; only the standard classical axioms already used by
   [DPIA_Rules.v] may appear (proof irrelevance / functional
   extensionality / classical logic from the [Reals] import).
*)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra Lia.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.Ops_Conv.
Require Import Ionia.Ops_BatchNorm.
Require Import Ionia.Ops_Elementwise.
Require Import Ionia.Opt_TiledConv.
Require Import Ionia.ResNet18_DPIA.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Shared pure expressions (register/buffer-resident intermediate values)     *)
(* -------------------------------------------------------------------------- *)

(* Stage-1 output: relu (bn (conv3x3 x)) as a pure expression.  The second
   convolution consumes this value directly (value passing), so the stage-1
   feature map never touches memory. *)
Definition BB_mid1 {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  ReLU4d (BatchNorm4d (Conv4d_3x3_s1 b1 w1 input) g1 z1 eps).

(* The [fin c]-indexed summand of the second convolution: the 3x3 kernel
   window reduction for input channel [cin] over [BB_mid1].  Mirrors
   [Conv4d_chan_sum] (Opt_TiledConv) for the canonical-size conv. *)
Definition BB_conv2_chan_sum {batch c m1 m2 : nat}
  (mid : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b : fin batch) (cout : fin c) (i0 : fin m1) (j0 : fin m2) (cin : fin c)
  : exp num :=
  sum (mkvSeq (fun i1 : fin 3 =>
    sum (mkvSeq (fun j1 : fin 3 =>
      mul (pad_idx2d 1 (idx (idx mid b) cin)
                     (fin2nat i0 + fin2nat i1)
                     (fin2nat j0 + fin2nat j1))
          (idx (idx (idx (idx w2 cout) cin) i1) j1))))).

(* The conv2 output channel slice (an [m1 x m2] feature map) as a pure
   expression; the BN2 statistics reductions iterate over it.  Mirrors
   [Conv4d_out_slice] (Opt_TiledConv). *)
Definition BB_conv2_out_slice {batch c m1 m2 : nat}
  (mid : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (b2 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b : fin batch) (cout : fin c)
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i0 : fin m1 => mkvSeq (fun j0 : fin m2 =>
    add (sum (mkvSeq (fun cin : fin c => BB_conv2_chan_sum mid w2 b cout i0 j0 cin)))
        (idx b2 cout))).

(* -------------------------------------------------------------------------- *)
(* Scalar key: relu (BN2cell (conv2 sum + bias) stats + residual)             *)
(* -------------------------------------------------------------------------- *)

(* Variant of [A_relu_bn_conv_cell] (Opt_TiledConv) whose continuation also
   folds the residual addition [xr] and the final ReLU branch: the BN
   variance reduction, the BN mean reduction, then the conv2 channel
   reduction whose continuation applies the BN affine transform, adds the
   residual and takes the ReLU branch — all on the single output cell
   accumulator. *)
Lemma A_relu_add_bn_conv_cell : forall (n : nat) (xs : exp (ary '{n} num))
  (bc : exp num) (h w : nat) (x2 : exp (ary '{h} (ary '{w} num)))
  (gmm bt eps xr : exp num) (oj : acc num),
  A(oj, (if leExp (add (BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps) xr) zero
           then zero
           else add (BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps) xr))
  = suml (BNvarSum x2 (BNmean x2)) (fun sv =>
      suml (BNmeanSum x2) (fun sm =>
        suml xs (fun r =>
          oj |:= (if leExp (add (BNcell (add r bc) (div sm (INR (h * w)))
                                   (div sv (INR (h * w))) gmm bt eps) xr) zero
                    then zero
                    else add (BNcell (add r bc) (div sm (INR (h * w)))
                                (div sv (INR (h * w))) gmm bt eps) xr)) oj) oj) oj.
Proof.
  intros n xs bc h w x2 gmm bt eps xr oj.
  assert (Hfold :
    A(oj, (if leExp (add (BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps) xr) zero
             then zero
             else add (BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps) xr))
    = C(sum (BNvarSum x2 (BNmean x2)), fun sv =>
        C(sum (BNmeanSum x2), fun sm =>
          C(sum xs, fun r =>
            oj |:= (if leExp (add (BNcell (add r bc) (div sm (INR (h * w)))
                                     (div sv (INR (h * w))) gmm bt eps) xr) zero
                      then zero
                      else add (BNcell (add r bc) (div sm (INR (h * w)))
                                  (div sv (INR (h * w))) gmm bt eps) xr))))).
  { reflexivity. }
  rewrite Hfold.
  rewrite C_sum_post3_acc.
  apply suml_cont_congr. intro sv.
  rewrite C_sum_post2_acc.
  apply suml_cont_congr. intro sm.
  rewrite C_sum_post_acc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fused single-kernel command for the whole BasicBlock (identity)            *)
(* -------------------------------------------------------------------------- *)

(* Fused per-output-cell command: BN2 variance reduction, BN2 mean
   reduction, then the conv2 channel reduction whose continuation applies
   the BN2 affine transform, adds the residual input cell and takes the
   ReLU branch.  The only assignment target is [output_cell] itself (the
   [suml] skeletons reuse it as their scalar accumulator). *)
Definition BasicBlockCell_fused_comm {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (mid : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (b2 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num)) (eps : exp num)
  (b : fin batch) (cout : fin c) (i0 : fin m1) (j0 : fin m2)
  (output_cell : acc num) : comm :=
  suml (BNvarSum (BB_conv2_out_slice mid b2 w2 b cout)
                 (BNmean (BB_conv2_out_slice mid b2 w2 b cout)))
    (fun sv : exp num =>
      suml (BNmeanSum (BB_conv2_out_slice mid b2 w2 b cout))
        (fun sm : exp num =>
          suml (mkvSeq (fun cin : fin c => BB_conv2_chan_sum mid w2 b cout i0 j0 cin))
            (fun r : exp num =>
              output_cell |:=
                (if leExp (add (BNcell (add r (idx b2 cout))
                                  (div sm (INR (m1 * m2)))
                                  (div sv (INR (m1 * m2)))
                                  (idx g2 cout) (idx z2 cout) eps)
                           (idx (idx (idx (idx input b) cout) i0) j0)) zero
                   then zero
                   else add (BNcell (add r (idx b2 cout))
                               (div sm (INR (m1 * m2)))
                               (div sv (INR (m1 * m2)))
                               (idx g2 cout) (idx z2 cout) eps)
                            (idx (idx (idx (idx input b) cout) i0) j0)))
            output_cell) output_cell) output_cell.

(* Fused single kernel for the whole 4d output: four nested loops over
   (batch, channel, H, W); all intermediate values are pure expressions
   inlined into the reductions — no intermediate feature-map buffer. *)
Definition BasicBlock_fused_comm {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      BasicBlockCell_fused_comm input (BB_mid1 input w1 b1 g1 z1 eps)
        b2 w2 g2 z2 eps b cout i0 j0 o1) o0) oc) ob) output.

(* -------------------------------------------------------------------------- *)
(* Whole-block fusion theorem                                                 *)
(* -------------------------------------------------------------------------- *)

(* The seven-step chain as one fused kernel.  Proof shape mirrors
   [A_Conv4d_BN_ReLU4d] (Opt_TiledConv): AmkvSeq x4 + seqfor_extensionality
   down to the output cell, [idx_mkvSeq] unfolds the operator chain into the
   scalar cell expression, and [A_relu_add_bn_conv_cell] folds BN2 + Add +
   ReLU into the conv2 reduction continuation. *)
Theorem A_BasicBlock_fused : forall (batch c m1 m2 : nat)
  (Hb : batch > 0) (Hc : c > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  A(output, ReLU4d (Add4d (BatchNorm4d (Conv4d_3x3_s1 b2 w2
              (BB_mid1 input w1 b1 g1 z1 eps)) g2 z2 eps) input))
  = BasicBlock_fused_comm input w1 b1 g1 z1 w2 b2 g2 z2 eps output.
Proof.
  intros.
  unfold ReLU4d, Add4d, BatchNorm4d, Conv4d_3x3_s1,
         BB_conv2_out_slice, BB_conv2_chan_sum,
         BasicBlock_fused_comm, BasicBlockCell_fused_comm.
  rewrite AmkvSeq. apply seqfor_extensionality. intro b.
  rewrite AmkvSeq. apply seqfor_extensionality. intro cout.
  rewrite AmkvSeq. apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq. apply seqfor_extensionality. intro j0.
  cbv beta.
  rewrite !idx_mkvSeq by lia.
  apply A_relu_add_bn_conv_cell.
Qed.

(* Stated against [ResNet18_DPIA.BasicBlock_id] itself (the let-chain is
   definitionally the expression above with [BB_mid1] unfolded). *)
Corollary A_BasicBlock_id_fused : forall (batch c m1 m2 : nat)
  (Hb : batch > 0) (Hc : c > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  A(output, BasicBlock_id input w1 b1 g1 z1 w2 b2 g2 z2 eps)
  = BasicBlock_fused_comm input w1 b1 g1 z1 w2 b2 g2 z2 eps output.
Proof.
  intros. unfold BasicBlock_id. cbv zeta.
  apply A_BasicBlock_fused; assumption.
Qed.

(* Bridge to the buffer-layered imperative block: observed at an output
   path, [basicblock_id_comm] (six temporary feature-map buffers bt1..bt6)
   computes the same values as the buffer-free fused kernel. *)
Corollary basicblock_id_comm_eq_fused : forall (batch c m1 m2 : nat)
  (Hb : batch > 0) (Hc : c > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  basicblock_id_comm input w1 b1 g1 z1 w2 b2 g2 z2 eps output rho p
  = BasicBlock_fused_comm input w1 b1 g1 z1 w2 b2 g2 z2 eps output rho p.
Proof.
  intros.
  rewrite A_BasicBlock_id by exact H.
  rewrite A_BasicBlock_id_fused by assumption.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_relu_add_bn_conv_cell.
Print Assumptions A_BasicBlock_fused.
Print Assumptions A_BasicBlock_id_fused.
Print Assumptions basicblock_id_comm_eq_fused.
