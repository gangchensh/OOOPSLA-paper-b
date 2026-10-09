(* Tiled/blocked convolution and Conv+BatchNorm+ReLU fusion rewrite rules
   for the DPIA rule layer (route A).

   This file builds on [Opt_Tiling.v] (loop split/join), [Ops_Conv.v],
   [Ops_BatchNorm.v], [Ops_Elementwise.v] (operator A-rules) and
   [Opt_ParGranularity.v] (parallel coarsening):

   - [Conv4d_chan_sum]: the per-input-channel partial sum of [Conv4dCell],
     factored out so that the tiled kernel and the fusion kernel share the
     exact same summand.
   - [reducel_tile_cast]: a [reducel] over a [mkvSeq] array whose bound [C]
     is only *equal* (not convertible) to a product [n * m] reindexes to the
     same skeleton over the casted array; bridges [seqfor_tile_cast] to
     [reducel_tiled].
   - [A_Conv4d_tiled] (core): Conv4d with the output spatial dims blocked
     into [Ht x TH] / [Wt x TW] tiles and the input-channel reduction
     blocked into [Ct] blocks of [Cin] accumulated per block equals the
     original [Conv4d].  Iteration order is preserved exactly
     ([idx_2d_to_1d] = block*size + offset), so NO algebraic side condition
     is needed.  This is the correctness basis of the CUDA shared-memory
     tiled convolution kernel.
   - [A_Conv4d_BN_ReLU4d] (fusion chain): Conv4d + BatchNorm4d + ReLU4d
     fused into a single kernel.  The BN statistics (variance and mean
     reductions over the conv output channel slice) and the ReLU branch are
     folded into the continuation of the convolution reduction via the new
     three-reduction chaining rule [C_sum_post3] (mirroring
     [Ops_BatchNorm.C_sum_post2]).  This backs the conv+BN+ReLU fused
     kernel used by the CUDA code generator.
   - Bonus: [tiled_parfor_two_level] — an [idx_2d_to_1d]-indexed corollary
     of [Opt_ParGranularity.parfor_coarsen]: a [parfor] over [n * m]
     iterations packs as [n] parallel blocks (CUDA blocks / tiles) of [m]
     sequential iterations (intra-tile threads), with free block-level
     scheduling; the indexing matches [A_Conv4d_tiled] so the two compose.

   All proofs are [Qed]; only the standard classical axioms already used by
   [DPIA_Rules.v] may appear (proof irrelevance / functional
   extensionality / classical logic from the [Reals] import).
*)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra Lia.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Opt_Tiling.
Require Import Ionia.Ops_Conv.
Require Import Ionia.Ops_BatchNorm.
Require Import Ionia.Ops_Elementwise.
Require Import Ionia.Parallel_Safety.
Require Import Ionia.Opt_ParGranularity.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Shared per-channel convolution summand                                     *)
(* -------------------------------------------------------------------------- *)

(* The [fin channel]-indexed summand of [Conv4dCell]: the kernel window
   reduction for input channel [c].  Factored out of [Ops_Conv.Conv4dCell]
   (same body, verbatim) so the tiled kernel and the fusion kernel below
   share it. *)
Definition Conv4d_chan_sum {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (c : fin channel) : exp num :=
  sum (mkvSeq (fun i1 : fin n1 =>
    sum (mkvSeq (fun j1 : fin n2 =>
      mul (pad_idx2d p (idx (idx input b) c)
                     (fin2nat i0 * s + fin2nat i1)
                     (fin2nat j0 * s + fin2nat j1))
          (idx (idx (idx (idx w cout) c) i1) j1))))).

(* -------------------------------------------------------------------------- *)
(* Reduction reindexing along a bound equality                                *)
(* -------------------------------------------------------------------------- *)

(* A [reducel] over a [mkvSeq] array of size [C] reindexes along
   [C = n * m] to the same skeleton over the casted array.  The cast
   preserves values ([fin2nat_tile_cast]), so this is a pure reindexing. *)
Lemma reducel_tile_cast : forall (cdim n m : nat) (Hc : cdim = n * m) (s t : data)
  (op : exp s -> exp t -> exp t) (init : exp t)
  (f : fin cdim -> exp s) (cont : exp t -> comm) (out : acc t),
  cdim > 0 ->
  reducel op init (mkvSeq f) cont out =
  reducel op init (mkvSeq (fun k : fin (n * m) => f (fin_tile_cast (eq_sym Hc) k)))
    cont out.
Proof.
  intros cdim n m Hc s t op init f cont out Hpos.
  unfold reducel, new. cbv beta.
  f_equal. f_equal.
  rewrite (seqfor_tile_cast Hc).
  apply seqfor_extensionality. intro k. cbv beta.
  apply functional_extensionality. intro rho.
  f_equal. f_equal.
  rewrite !idx_mkvSeq by lia.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Core: tiled Conv4d (spatial tiles x input-channel blocks)                  *)
(* -------------------------------------------------------------------------- *)

(* Tiled per-output-cell command: the [fin channel] reduction runs as [Ct]
   outer blocks of [Cin] inner steps (the [reducel_tiled] shape), using the
   output cell itself as the temporary accumulator (as in [Conv4dCell_comm]). *)
Definition Conv4dCell_tiled_comm {batch m1 m2 n1 n2 channel filernum Ct Cin : nat}
  (p s : nat) (Hc : channel = Ct * Cin)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num) : comm :=
  new (fun tmp : acc num =>
    (tmp |:= zero) ';
    (seqfor (fun tc : fin Ct => seqfor (fun c' : fin Cin => fun rho : env =>
       assign tmp
         (add ((mkvSeq (fun k : fin (Ct * Cin) =>
                  Conv4d_chan_sum p s w input b cout i0 j0
                    (fin_tile_cast (eq_sym Hc) k)))|[idx_2d_to_1d tc c'])
              (read_exp rho tmp)) rho)) ';
     (fun rho : env => (output_cell |:= add (read_exp rho tmp) (idx bias cout)) rho)))
    output_cell.

(* Cell-level correctness: blocking the input-channel reduction into
   [Ct] blocks of [Cin] preserves the cell command. *)
Lemma Conv4dCell_tiled : forall (batch m1 m2 n1 n2 channel filernum Ct Cin p s : nat)
  (Hc : channel = Ct * Cin) (Hch : channel > 0)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num),
  Conv4dCell_comm p s bias w input b cout i0 j0 output_cell
  = Conv4dCell_tiled_comm p s Hc bias w input b cout i0 j0 output_cell.
Proof.
  intros.
  unfold Conv4dCell_comm, Conv4dCell_tiled_comm, suml.
  rewrite (reducel_tile_cast (cdim := channel) Ct Cin Hc num num add zero
             (fun c : fin channel =>
                sum (mkvSeq (fun i1 : fin n1 =>
                  sum (mkvSeq (fun j1 : fin n2 =>
                    mul (pad_idx2d p (idx (idx input b) c)
                                   (fin2nat i0 * s + fin2nat i1)
                                   (fin2nat j0 * s + fin2nat j1))
                        (idx (idx (idx (idx w cout) c) i1) j1))))))
             (fun r : exp num => output_cell |:= add r (idx bias cout))
             output_cell Hch).
  rewrite reducel_tiled.
  reflexivity.
Qed.

(* Fully tiled Conv4d: batch/filter loops unchanged; the output spatial
   loops run as [Ht x Wt] tiles of [TH x TW] points (via [fin_tile_cast] +
   [idx_2d_to_1d]); each cell uses the channel-blocked reduction. *)
Definition Conv4d_tiled_comm {batch m1 m2 n1 n2 channel filernum
    Ht TH Wt TW Ct Cin : nat}
  (p s : nat)
  (Hh : (m1 - n1 + 2 * p) / s + 1 = Ht * TH)
  (Hw : (m2 - n2 + 2 * p) / s + 1 = Wt * TW)
  (Hc : channel = Ct * Cin)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    seqfor (fun ti : fin Ht => seqfor (fun i0' : fin TH =>
      seqfor (fun tj : fin Wt => seqfor (fun j0' : fin TW =>
        Conv4dCell_tiled_comm p s Hc bias w input b cout
          (fin_tile_cast (eq_sym Hh) (idx_2d_to_1d ti i0'))
          (fin_tile_cast (eq_sym Hw) (idx_2d_to_1d tj j0'))
          ((oc|{fin_tile_cast (eq_sym Hh) (idx_2d_to_1d ti i0')})
            |{fin_tile_cast (eq_sym Hw) (idx_2d_to_1d tj j0')})))))) ob) output.

(* Core theorem: the tiled/blocked Conv4d implementation equals the
   original Conv4d. *)
Theorem A_Conv4d_tiled : forall (batch m1 m2 n1 n2 channel filernum
    Ht TH Wt TW Ct Cin p s : nat)
  (Hh : (m1 - n1 + 2 * p) / s + 1 = Ht * TH)
  (Hw : (m2 - n2 + 2 * p) / s + 1 = Wt * TW)
  (Hc : channel = Ct * Cin) (Hch : channel > 0)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  A(output, Conv4d p s bias w input)
  = Conv4d_tiled_comm p s Hh Hw Hc bias w input output.
Proof.
  intros.
  rewrite A_Conv4d.
  unfold Conv4d_comm, Conv4d_tiled_comm, mkvSeql. cbv beta.
  apply seqfor_extensionality. intro b.
  apply seqfor_extensionality. intro cout.
  rewrite (seqfor_tile_cast Hh).
  rewrite seqfor_split. cbv beta.
  apply seqfor_extensionality. intro ti.
  apply seqfor_extensionality. intro i0'.
  rewrite (seqfor_tile_cast Hw).
  rewrite seqfor_split. cbv beta.
  apply seqfor_extensionality. intro tj.
  apply seqfor_extensionality. intro j0'.
  apply Conv4dCell_tiled. exact Hch.
Qed.

(* -------------------------------------------------------------------------- *)
(* Three chained reductions on one scalar accumulator                         *)
(* -------------------------------------------------------------------------- *)

(* Three-reduction variant of [C_sum_post2] (Ops_BatchNorm): the outer
   reduction uses [acc' p] as temporary, its value is captured by the
   continuation, and the innermost command finally overwrites [acc' p]. *)
Lemma C_sum_post3 : forall (n1 : nat) (xs : exp (ary '{n1} num)) (p : path)
  (e2 : exp num) (n3 : nat) (x3 : exp (ary '{n3} num))
  (k : exp num -> exp num -> exp num -> exp num),
  C(sum xs, fun r1 => C(e2, fun r2 => C(sum x3, fun r3 => (acc' p) |:= k r1 r2 r3))) =
  suml xs (fun r1 => C(e2, fun r2 => C(sum x3, fun r3 => (acc' p) |:= k r1 r2 r3))) (acc' p).
Proof.
  intros. unfold DPIA_Rules.C, suml, reducel, new.
  rewrite (seq_assoc ((acc' p) |:= zero)
                     (seqfor (fun i : fin n1 => fun rho : env =>
                        ((acc' p) |:= add (xs|[i]) (read_exp rho (acc' p))) rho))
                     (fun rho : env =>
                        ((acc' p) |:= k (read_exp rho (acc' p)) e2 (sum x3)) rho)).
  rewrite reduce_aux_num.
  rewrite (assign_update_num p (reduce add zero xs) (fun old : exp num => k old e2 (sum x3))).
  reflexivity.
Qed.

Corollary C_sum_post3_acc : forall (n1 : nat) (xs : exp (ary '{n1} num)) (a : acc num)
  (e2 : exp num) (n3 : nat) (x3 : exp (ary '{n3} num))
  (k : exp num -> exp num -> exp num -> exp num),
  C(sum xs, fun r1 => C(e2, fun r2 => C(sum x3, fun r3 => a |:= k r1 r2 r3))) =
  suml xs (fun r1 => C(e2, fun r2 => C(sum x3, fun r3 => a |:= k r1 r2 r3))) a.
Proof.
  intros.
  assert (Ha: acc' a = a) by (apply acc'_num).
  rewrite <- Ha. rewrite C_sum_post3.
  rewrite Ha. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fusion chain: Conv4d + BatchNorm4d + ReLU4d                                *)
(* -------------------------------------------------------------------------- *)

(* The conv output channel slice (an [H x W] feature map) as a pure
   expression; the BN statistics reductions iterate over it. *)
Definition Conv4d_out_slice {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (cout : fin filernum)
  : exp (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)) :=
  mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
    mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
      Conv4dCell p s bias w input b cout i0 j0)).

(* Scalar key: relu (BNcell (sum xs + bc) stats) computes as the BN
   variance reduction, then the BN mean reduction, then the conv reduction
   whose continuation applies the BN affine transform and the ReLU branch.
   BN stays the [Ops_BatchNorm.BatchNorm4d] semantics: statistics over the
   channel slice [x2] (the conv output feature map). *)
Lemma A_relu_bn_conv_cell : forall (n : nat) (xs : exp (ary '{n} num)) (bc : exp num)
  (h w : nat) (x2 : exp (ary '{h} (ary '{w} num)))
  (gmm bt eps : exp num) (oj : acc num),
  A(oj, (if leExp (BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps) zero
           then zero
           else BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps))
  = suml (BNvarSum x2 (BNmean x2)) (fun sv =>
      suml (BNmeanSum x2) (fun sm =>
        suml xs (fun r =>
          oj |:= (if leExp (BNcell (add r bc) (div sm (INR (h * w)))
                             (div sv (INR (h * w))) gmm bt eps) zero
                    then zero
                    else BNcell (add r bc) (div sm (INR (h * w)))
                           (div sv (INR (h * w))) gmm bt eps)) oj) oj) oj.
Proof.
  intros n xs bc h w x2 gmm bt eps oj.
  assert (Hfold :
    A(oj, (if leExp (BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps) zero
             then zero
             else BNcell (add (sum xs) bc) (BNmean x2) (BNvar x2 (BNmean x2)) gmm bt eps))
    = C(sum (BNvarSum x2 (BNmean x2)), fun sv =>
        C(sum (BNmeanSum x2), fun sm =>
          C(sum xs, fun r =>
            oj |:= (if leExp (BNcell (add r bc) (div sm (INR (h * w)))
                               (div sv (INR (h * w))) gmm bt eps) zero
                      then zero
                      else BNcell (add r bc) (div sm (INR (h * w)))
                             (div sv (INR (h * w))) gmm bt eps))))).
  { reflexivity. }
  rewrite Hfold.
  rewrite C_sum_post3_acc.
  apply suml_cont_congr. intro sv.
  rewrite C_sum_post2_acc.
  apply suml_cont_congr. intro sm.
  rewrite C_sum_post_acc. reflexivity.
Qed.

(* Fused per-output-cell command: variance reduction, mean reduction, then
   the conv channel reduction with BN + ReLU folded into its continuation. *)
Definition Conv4dBNReLUCell_comm {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : exp (ary '{filernum} num)) (eps : exp num)
  (b : fin batch) (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num) : comm :=
  suml (BNvarSum (Conv4d_out_slice p s bias w input b cout)
                 (BNmean (Conv4d_out_slice p s bias w input b cout)))
    (fun sv : exp num =>
      suml (BNmeanSum (Conv4d_out_slice p s bias w input b cout))
        (fun sm : exp num =>
          suml (mkvSeq (fun c : fin channel =>
                  Conv4d_chan_sum p s w input b cout i0 j0 c))
            (fun r : exp num =>
              output_cell |:=
                (if leExp (BNcell (add r (idx bias cout))
                             (div sm (INR (((m1 - n1 + 2 * p) / s + 1)
                                           * ((m2 - n2 + 2 * p) / s + 1))))
                             (div sv (INR (((m1 - n1 + 2 * p) / s + 1)
                                           * ((m2 - n2 + 2 * p) / s + 1))))
                             (idx gamma cout) (idx beta cout) eps) zero
                   then zero
                   else BNcell (add r (idx bias cout))
                          (div sm (INR (((m1 - n1 + 2 * p) / s + 1)
                                        * ((m2 - n2 + 2 * p) / s + 1))))
                          (div sv (INR (((m1 - n1 + 2 * p) / s + 1)
                                        * ((m2 - n2 + 2 * p) / s + 1))))
                          (idx gamma cout) (idx beta cout) eps))
            output_cell) output_cell) output_cell.

(* Fused single-kernel command for the whole 4d output. *)
Definition Conv4dBNReLU4d_fused_comm {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : exp (ary '{filernum} num)) (eps : exp num)
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      Conv4dBNReLUCell_comm p s bias w input gamma beta eps b cout i0 j0 o1)
      o0) oc) ob) output.

(* Fusion chain theorem: Conv4d + BatchNorm4d + ReLU4d as one kernel. *)
Theorem A_Conv4d_BN_ReLU4d : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hb : batch > 0) (Hf : filernum > 0)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : exp (ary '{filernum} num)) (eps : exp num)
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  A(output, ReLU4d (BatchNorm4d (Conv4d p s bias w input) gamma beta eps))
  = Conv4dBNReLU4d_fused_comm p s bias w input gamma beta eps output.
Proof.
  intros.
  unfold ReLU4d, BatchNorm4d, Conv4d, Conv4d_out_slice, Conv4d_chan_sum,
         Conv4dBNReLU4d_fused_comm, Conv4dBNReLUCell_comm.
  rewrite AmkvSeq. apply seqfor_extensionality. intro b.
  rewrite AmkvSeq. apply seqfor_extensionality. intro cout.
  rewrite AmkvSeq. apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq. apply seqfor_extensionality. intro j0.
  cbv beta.
  rewrite !idx_mkvSeq by lia.
  unfold Conv4dCell.
  apply A_relu_bn_conv_cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* Bonus: two-level schedule (parallel tiles x sequential intra-tile)         *)
(* -------------------------------------------------------------------------- *)

(* [fin_block] (Opt_ParGranularity) and [idx_2d_to_1d] (vector.v) both have
   value [b * m + i]: they are the same flat index. *)
Lemma fin_block_eq_idx_2d_to_1d : forall (n m : nat) (b : fin n) (i : fin m),
  fin_block b i = idx_2d_to_1d b i.
Proof.
  intros n m b i. apply fin_eq.
  rewrite fin2nat_fin_block. reflexivity.
Qed.

(* Two-level schedule: a [parfor] over [n * m] micro-iterations packs as
   [n] parallel blocks of [m] sequential iterations (CUDA block/thread
   levels), and the block order may be permuted by any [τ].  Stated with
   the [idx_2d_to_1d] indexing of [Opt_Tiling.seqfor_split] so that it
   composes with the tiled loops of [A_Conv4d_tiled] (whose tile bodies are
   non-interfering as soon as their write targets are separated, e.g. via
   [Parallel_Safety.parallel_safe_A] on distinct output cells). *)
Theorem tiled_parfor_two_level : forall (n m : nat) (Hm : m > 0) (d : data)
  (out : acc (ary '{n * m} d)) (g : fin (n * m) -> acc d -> comm),
  non_interfering (fun k : fin (n * m) => g k (out|{k})) ->
  parfor out g
  = seqfor (fun i : fin n => seqfor (fun j : fin m =>
      g (idx_2d_to_1d i j) (out|{idx_2d_to_1d i j})))
  /\ (forall τ : fin n -> fin n, (forall i j, τ i = τ j -> i = j) ->
      forall rho : env, parfor out g rho
      = seqfor (fun i : fin n => seqfor (fun j : fin m =>
          g (idx_2d_to_1d (τ i) j) (out|{idx_2d_to_1d (τ i) j}))) rho).
Proof.
  intros n m Hm d out g Hni.
  destruct (parfor_coarsen n m d Hm out g Hni) as [H1 [_ H3]].
  split.
  - rewrite H1.
    apply seqfor_extensionality. intro b.
    apply seqfor_extensionality. intro i.
    rewrite fin_block_eq_idx_2d_to_1d. reflexivity.
  - intros τ Hinj rho.
    rewrite (H3 τ Hinj rho). f_equal.
    apply functional_extensionality. intro b.
    apply seqfor_extensionality. intro i.
    rewrite fin_block_eq_idx_2d_to_1d. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions reducel_tile_cast.
Print Assumptions Conv4dCell_tiled.
Print Assumptions A_Conv4d_tiled.
Print Assumptions C_sum_post3.
Print Assumptions A_relu_bn_conv_cell.
Print Assumptions A_Conv4d_BN_ReLU4d.
Print Assumptions tiled_parfor_two_level.
