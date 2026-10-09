(* DPIA-style Leibniz equivalence proofs for BatchNorm (inference mode with
   batch statistics) in the route-A R-based expression model.

   Neither the old ForCNN5 library nor route B provides a BatchNorm operator
   that fits the route-A R-model, so the operator is defined here from the
   standard formulas: for each channel c,
     mean[c]   = (sum_{i,j} x[c,i,j]) / (m1*m2)
     var[c]    = (sum_{i,j} (x[c,i,j] - mean[c])^2) / (m1*m2)
     y[c,i,j]  = gamma[c] * (x[c,i,j] - mean[c]) / sqrt(var[c] + eps) + beta[c].

   Because [exp num = R] in route A, every scalar operation (sub, div, mul,
   add, sqrt) has a reflexivity-shaped rule (cf. [A_pExp]); [A_sqrt] below is
   the one-liner for [Proof_CodeGen.sqrt].  The mean/var reductions reuse the
   batch-2 [suml] skeleton: [C_sum_post_acc] handles a single reduction whose
   continuation is the final assignment, and the new [C_sum_post2] handles two
   chained reductions that share the same scalar accumulator as temporary —
   the outer continuation captures the first sum as a value before the inner
   loop overwrites the accumulator. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen]: it defines its own
   [num] constructor (Ring_polynom.PExpr) that would otherwise shadow the
   [data] constructor. *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* A-rule for sqrt (one-line reflexivity rule, modelled on [A_pExp])          *)
(* -------------------------------------------------------------------------- *)

Lemma A_sqrt : forall (a : acc num) (e : exp num),
  A(a, sqrt e) = C(e, fun r => a |:= sqrt r).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Two chained reductions on one scalar accumulator                           *)
(* -------------------------------------------------------------------------- *)

(* [suml] respects continuation equality. *)
Lemma suml_cont_congr : forall (n:nat) (xs : exp (ary '{n} num)) (a : acc num)
  (K1 K2 : exp num -> comm),
  (forall r, K1 r = K2 r) ->
  suml xs K1 a = suml xs K2 a.
Proof.
  intros. unfold suml, reducel, new.
  f_equal. f_equal.
  apply functional_extensionality. intro rho.
  rewrite (H (read_exp rho a)). reflexivity.
Qed.

(* Variant of [C_sum_post] whose continuation is itself a [C]: the outer
   reduction uses [acc' p] as temporary, its result is captured by the
   continuation as a value, and the inner command finally overwrites
   [acc' p], so the temporary usage is invisible in the Leibniz equality. *)
Lemma C_sum_post2 : forall (n:nat) (xs : exp (ary '{n} num)) (p : path)
  (e2 : exp num) (k : exp num -> exp num -> exp num),
  C(sum xs, fun r => C(e2, fun s => (acc' p) |:= k r s)) =
  suml xs (fun r => C(e2, fun s => (acc' p) |:= k r s)) (acc' p).
Proof.
  intros. unfold DPIA_Rules.C, suml, reducel, new.
  rewrite (seq_assoc ((acc' p) |:= zero)
                     (seqfor (fun i : fin n => fun rho =>
                        ((acc' p) |:= add (xs|[i]) (read_exp rho (acc' p))) rho))
                     (fun rho : env =>
                        ((acc' p) |:= k (read_exp rho (acc' p)) e2) rho)).
  rewrite reduce_aux_num.
  rewrite (assign_update_num p (reduce add zero xs) (fun old : exp num => k old e2)).
  reflexivity.
Qed.

Corollary C_sum_post2_acc : forall (n:nat) (xs : exp (ary '{n} num)) (a : acc num)
  (e2 : exp num) (k : exp num -> exp num -> exp num),
  C(sum xs, fun r => C(e2, fun s => a |:= k r s)) =
  suml xs (fun r => C(e2, fun s => a |:= k r s)) a.
Proof.
  intros.
  assert (Ha: acc' a = a) by (apply acc'_num).
  rewrite <- Ha. rewrite C_sum_post2.
  rewrite Ha. reflexivity.
Qed.

(* Two chained sums computed into a single scalar accumulator [a]: first the
   [xs] sum (captured by the continuation), then the [ys] sum, then the final
   assignment overwrites [a]. *)
Lemma A_sum2_cell : forall (na nb : nat)
  (xs : exp (ary '{na} num)) (ys : exp (ary '{nb} num))
  (a : acc num) (k : exp num -> exp num -> exp num),
  A(a, k (sum xs) (sum ys)) =
  suml xs (fun r => suml ys (fun s => a |:= k r s) a) a.
Proof.
  intros.
  replace (A(a, k (sum xs) (sum ys)))
    with (C(sum xs, fun r => C(sum ys, fun s => a |:= k r s))) by reflexivity.
  rewrite C_sum_post2_acc.
  apply suml_cont_congr. intro r.
  rewrite C_sum_post_acc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* BatchNorm building blocks (per-channel statistics over an m1 x m2 slice)   *)
(* -------------------------------------------------------------------------- *)

(* Summand array for the mean: [m1] partial row sums. *)
Definition BNmeanSum {m1 m2:nat} (x2 : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} num) :=
  mkvSeq (fun i0 : fin m1 => sum (mkvSeq (fun j0 : fin m2 => idx (idx x2 i0) j0))).

(* Channel mean. *)
Definition BNmean {m1 m2:nat} (x2 : exp (ary '{m1} (ary '{m2} num))) : exp num :=
  div (sum (BNmeanSum x2)) (INR (m1 * m2)).

(* Summand array for the variance: [m1] partial row sums of squared
   deviations from [mean]. *)
Definition BNvarSum {m1 m2:nat} (x2 : exp (ary '{m1} (ary '{m2} num))) (mean : exp num)
  : exp (ary '{m1} num) :=
  mkvSeq (fun i0 : fin m1 => sum (mkvSeq (fun j0 : fin m2 =>
    mul (sub (idx (idx x2 i0) j0) mean) (sub (idx (idx x2 i0) j0) mean)))).

(* Channel variance. *)
Definition BNvar {m1 m2:nat} (x2 : exp (ary '{m1} (ary '{m2} num))) (mean : exp num)
  : exp num :=
  div (sum (BNvarSum x2 mean)) (INR (m1 * m2)).

(* Single normalised element. *)
Definition BNcell (x mean var gamma beta eps : exp num) : exp num :=
  add (mul (div (sub x mean) (sqrt (add var eps))) gamma) beta.

(* -------------------------------------------------------------------------- *)
(* BatchNorm3d (channel x m1 x m2, batch statistics)                          *)
(* -------------------------------------------------------------------------- *)

Definition BatchNorm3d {channel m1 m2:nat}
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  : exp (ary '{channel} (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun c : fin channel => mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    BNcell (idx (idx (idx input c) i) j)
           (BNmean (idx input c))
           (BNvar (idx input c) (BNmean (idx input c)))
           (idx gamma c) (idx beta c) eps))).

Definition BatchNorm3d_comm {channel m1 m2:nat}
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  (output : acc (ary '{channel} (ary '{m1} (ary '{m2} num)))) : comm :=
  mkvSeql (fun c oc => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (BNvarSum (idx input c) (BNmean (idx input c))) (fun sv =>
      suml (BNmeanSum (idx input c)) (fun sm =>
        oj |:= BNcell (idx (idx (idx input c) i) j)
                      (div sm (INR (m1 * m2))) (div sv (INR (m1 * m2)))
                      (idx gamma c) (idx beta c) eps) oj) oj) oi) oc) output.

(* Per-element cell: variance sum and mean sum chained on the element
   accumulator itself via [A_sum2_cell]. *)
Lemma A_BNcell : forall (m1 m2:nat) (x2 : exp (ary '{m1} (ary '{m2} num)))
  (x gamma beta eps : exp num) (oj : acc num),
  A(oj, BNcell x (BNmean x2) (BNvar x2 (BNmean x2)) gamma beta eps)
  = suml (BNvarSum x2 (BNmean x2)) (fun sv =>
      suml (BNmeanSum x2) (fun sm =>
        oj |:= BNcell x (div sm (INR (m1 * m2))) (div sv (INR (m1 * m2)))
                        gamma beta eps) oj) oj.
Proof.
  intros.
  replace (A(oj, BNcell x (BNmean x2) (BNvar x2 (BNmean x2)) gamma beta eps))
    with (C(sum (BNvarSum x2 (BNmean x2)),
            fun sv => C(sum (BNmeanSum x2),
                        fun sm => oj |:= BNcell x (div sm (INR (m1 * m2)))
                                                  (div sv (INR (m1 * m2)))
                                                  gamma beta eps)))
    by reflexivity.
  rewrite C_sum_post2_acc.
  apply suml_cont_congr. intro sv.
  rewrite C_sum_post_acc. reflexivity.
Qed.

Lemma A_BatchNorm3d : forall (channel m1 m2 : nat)
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  (output : acc (ary '{channel} (ary '{m1} (ary '{m2} num)))),
  A(output, BatchNorm3d input gamma beta eps) = BatchNorm3d_comm input gamma beta eps output.
Proof.
  intros. unfold BatchNorm3d, BatchNorm3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_BNcell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* BatchNorm4d (batch x channel x m1 x m2)                                    *)
(* -------------------------------------------------------------------------- *)

Definition BatchNorm4d {batch channel m1 m2:nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      BNcell (idx (idx (idx (idx input b) c) i) j)
             (BNmean (idx (idx input b) c))
             (BNvar (idx (idx input b) c) (BNmean (idx (idx input b) c)))
             (idx gamma c) (idx beta c) eps)))).

Definition BatchNorm4d_comm {batch channel m1 m2:nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun c oc => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (BNvarSum (idx (idx input b) c) (BNmean (idx (idx input b) c))) (fun sv =>
      suml (BNmeanSum (idx (idx input b) c)) (fun sm =>
        oj |:= BNcell (idx (idx (idx (idx input b) c) i) j)
                      (div sm (INR (m1 * m2))) (div sv (INR (m1 * m2)))
                      (idx gamma c) (idx beta c) eps) oj) oj) oi) oc) ob) output.

Lemma A_BatchNorm4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, BatchNorm4d input gamma beta eps) = BatchNorm4d_comm input gamma beta eps output.
Proof.
  intros. unfold BatchNorm4d, BatchNorm4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_BNcell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_sqrt.
Print Assumptions A_BNcell.
Print Assumptions A_BatchNorm3d.
Print Assumptions A_BatchNorm4d.
