(* Online softmax with a weighted accumulator (the flash-attention ternary
   state (m, l, a): running max, rebased exp-sum, and rebased weighted value
   sum) is equivalent to batch attention, for an arbitrary number of blocks.

   Batch attention:   out = Σ_i exp(s_i - max s) / Σ_j exp(s_j - max s) * v_i.
   Online (per block): stream (score, value) pairs, keeping a state (m, l, a)
     m_new = Rmax m_old s,
     l_new = l_old * exp(m_old - m_new) + exp(s - m_new),
     a_new = a_old * exp(m_old - m_new) + exp(s - m_new) * v,
   merge per-block statistics one at a time, and normalise a / l at the end.

   Contents:
   - Pointwise vector arithmetic on [vector R dv] ([vzero]/[vadd]/[vscal]),
     coordinate lemmas and the extensionality principle [vec_eq];
     restatements of the snoc-index facts at the plain type [vector R n].
   - Scalar weighted exp-sum [wsum] over [list (R * R)] and its scaling law
     [wsum_scale] (change of reference point), mimicking [lsum_scale].
   - Vector weighted exp-sum [vwsum] over [list (R * vector R dv)], the
     coordinate lemma [v_idx_vwsum] and the vector scaling law [vwsum_scale];
     the append lemma [vwsum_app].
   - Ternary merge [mergeV], per-block statistics [statV] and the right fold
     [merge_allV] over an arbitrary list of blocks.
   - Main theorem [online_merge_all_v_correct]: merging per-block ternary
     statistics one at a time (any number of blocks, any block sizes) yields
     (global max, global re-referenced exp-sum, global re-referenced weighted
     value sum) for the concatenation of all blocks — isomorphic to
     [Opt_OnlineSoftmax.online_merge_all_correct].
   - Value-level corollaries [online_merge_all_v_output] /
     [online_merge_all_v_output_coord]: the normalised accumulator a / l
     equals the batch attention output of the concatenated data, as a vector
     and coordinatewise.

   All proofs are [Qed]; only the standard classical axioms already used by
   [DPIA_Rules.v] / [Opt_OnlineSoftmax.v] may appear (functional
   extensionality / proof irrelevance / classical logic from the Reals
   library).
*)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra Lia.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Opt_OnlineSoftmax.
Import Proof_CodeGen.
Import ListNotations.

(* -------------------------------------------------------------------------- *)
(* Pointwise vector arithmetic on [vector R dv]                               *)
(* -------------------------------------------------------------------------- *)

Fixpoint vzero {n:nat} : vector R n :=
  match n with
  | O => tt
  | S n' => (vzero, zero)
  end.

Definition vadd {n:nat} (v1 v2 : vector R n) : vector R n :=
  mk_vec (fun i => add (v_idx R0 v1 i) (v_idx R0 v2 i)).

Definition vscal (c : R) {n:nat} (v : vector R n) : vector R n :=
  mk_vec (fun i => mul c (v_idx R0 v i)).

(* Snoc-index facts at the plain type [vector R n] (the [idx_snoc_*] lemmas
   of Opt_OnlineSoftmax are stated through the [exp (ary '{n} num)] cast;
   these restatements avoid the cast). *)
Lemma v_idx_snoc_fs : forall {n} (v : vector R n) (x : R) (i : fin n),
  v_idx R0 ((v, x) : vector R (S n)) (fin2finS i) = v_idx R0 v i.
Proof.
  intros n v x i. unfold v_idx. destruct i as [k pf]. simpl.
  assert (E : (k =? n)%nat = false).
  { apply Nat.eqb_neq. intros ->. lia. }
  rewrite E. reflexivity.
Qed.

Lemma v_idx_snoc_last : forall {n} (v : vector R n) (x : R),
  v_idx R0 ((v, x) : vector R (S n)) (fin_last n) = x.
Proof.
  intros n v x. unfold v_idx, fin_last, nat2fin. simpl.
  rewrite Nat.eqb_refl. reflexivity.
Qed.

(* Every coordinate of the zero vector is zero. *)
Lemma v_idx_vzero : forall {n:nat} (i : fin n), v_idx R0 (@vzero n) i = zero.
Proof.
  induction n as [|n IH]; intros [k pf].
  - exfalso. lia.
  - change (@vzero (S n)) with ((@vzero n, zero) : vector R (S n)).
    unfold v_idx, v_nth. simpl.
    destruct (Nat.eq_dec k n) as [-> | Hne].
    + rewrite Nat.eqb_refl. reflexivity.
    + assert (E : (k =? n)%nat = false) by (apply Nat.eqb_neq; exact Hne).
      rewrite E. assert (pf' : k < n) by lia.
      exact (IH (exist _ k pf')).
Qed.

Lemma v_idx_vadd : forall {n:nat} (v1 v2 : vector R n) (i : fin n),
  v_idx R0 (vadd v1 v2) i = add (v_idx R0 v1 i) (v_idx R0 v2 i).
Proof. intros. unfold vadd. rewrite v_idx_mk_vec. reflexivity. Qed.

Lemma v_idx_vscal : forall (c : R) {n:nat} (v : vector R n) (i : fin n),
  v_idx R0 (vscal c v) i = mul c (v_idx R0 v i).
Proof. intros. unfold vscal. rewrite v_idx_mk_vec. reflexivity. Qed.

(* Extensionality: pointwise-equal vectors are equal. *)
Lemma vec_eq : forall {n:nat} (v1 v2 : vector R n),
  (forall i : fin n, v_idx R0 v1 i = v_idx R0 v2 i) -> v1 = v2.
Proof.
  induction n as [|n IH]; intros v1 v2 H.
  - destruct v1, v2. reflexivity.
  - destruct v1 as [w1 x1], v2 as [w2 x2]. f_equal.
    + apply IH. intro i.
      pose proof (H (fin2finS i)) as H'. rewrite !v_idx_snoc_fs in H'. exact H'.
    + pose proof (H (fin_last n)) as H'. rewrite !v_idx_snoc_last in H'. exact H'.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scalar layer: weighted exp-sum over [list (R * R)]                         *)
(* -------------------------------------------------------------------------- *)

(* Σ_i exp(s_i - m) * w_i over a list of (score, weight) pairs. *)
Fixpoint wsum (m : R) (wv : list (R * R)) : R :=
  match wv with
  | [] => zero
  | (s, w) :: t => add (mul (pExp (sub s m)) w) (wsum m t)
  end.

(* Change of reference point (the algebraic heart of the a-rebase step),
   mimicking [lsum_scale]. *)
Lemma wsum_scale : forall (wv : list (R * R)) (m m' : R),
  wsum m wv = mul (wsum m' wv) (pExp (sub m' m)).
Proof.
  induction wv as [|(s, w) t IH]; intros m m'.
  - simpl. unfold mul, zero. ring.
  - simpl. rewrite (IH m m'). unfold add, mul, sub, pExp.
    replace (s - m)%R with ((s - m') + (m' - m))%R by ring.
    rewrite exp_plus. ring.
Qed.

Lemma wsum_app : forall (wv1 wv2 : list (R * R)) (m : R),
  wsum m (wv1 ++ wv2) = add (wsum m wv1) (wsum m wv2).
Proof.
  induction wv1 as [|(s, w) t IH]; intros wv2 m.
  - simpl. unfold add, zero. ring.
  - simpl. rewrite IH. unfold add. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Vector layer: weighted exp-sum over [list (R * vector R dv)]               *)
(* -------------------------------------------------------------------------- *)

(* Σ_i exp(s_i - m) * v_i (pointwise) over a list of (score, value) pairs. *)
Fixpoint vwsum {dv:nat} (m : R) (wv : list (R * vector R dv)) : vector R dv :=
  match wv with
  | [] => vzero
  | (s, v) :: t => vadd (vscal (pExp (sub s m)) v) (vwsum m t)
  end.

(* Coordinatewise, [vwsum] is the scalar [wsum] with weights v_i. *)
Lemma v_idx_vwsum : forall {dv:nat} (m : R) (wv : list (R * vector R dv)) (i : fin dv),
  v_idx R0 (vwsum m wv) i =
  wsum m (map (fun p => (fst p, v_idx R0 (snd p) i)) wv).
Proof.
  intros dv m wv i. induction wv as [|(s, v) t IH].
  - simpl. apply v_idx_vzero.
  - simpl. rewrite v_idx_vadd, v_idx_vscal, IH. reflexivity.
Qed.

(* Vector change of reference point, by coordinates + [wsum_scale]. *)
Lemma vwsum_scale : forall {dv:nat} (wv : list (R * vector R dv)) (m m' : R),
  vwsum m wv = vscal (pExp (sub m' m)) (vwsum m' wv).
Proof.
  intros dv wv m m'. apply vec_eq. intro i.
  rewrite !v_idx_vwsum, !v_idx_vscal, !v_idx_vwsum.
  rewrite (wsum_scale (map (fun p => (fst p, v_idx R0 (snd p) i)) wv) m m').
  unfold mul. ring.
Qed.

Lemma vwsum_app : forall {dv:nat} (m : R) (wv1 wv2 : list (R * vector R dv)),
  vwsum m (wv1 ++ wv2) = vadd (vwsum m wv1) (vwsum m wv2).
Proof.
  intros dv m wv1 wv2. apply vec_eq. intro i.
  rewrite !v_idx_vwsum, !v_idx_vadd, !v_idx_vwsum, map_app, wsum_app. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Ternary state: merge, per-block statistics, arbitrary-block fold           *)
(* -------------------------------------------------------------------------- *)

(* One merge step of the flash-attention recurrence on (m, l, a). *)
Definition mergeV {dv:nat} (st1 st2 : (R * R) * vector R dv)
    : (R * R) * vector R dv :=
  let '((m1, l1), a1) := st1 in
  let '((m2, l2), a2) := st2 in
  let m := Rmax m1 m2 in
  ((m, add (mul l1 (pExp (sub m1 m))) (mul l2 (pExp (sub m2 m)))),
   vadd (vscal (pExp (sub m1 m)) a1) (vscal (pExp (sub m2 m)) a2)).

(* Per-block ternary statistics: (max score, rebased exp-sum of scores,
   rebased weighted value sum). *)
Definition statV {dv:nat} (wv : list (R * vector R dv)) : (R * R) * vector R dv :=
  let m := lmax (map fst wv) in
  ((m, lsum m (map fst wv)), vwsum m wv).

(* Right fold of [mergeV] over a list of per-block statistics:
   an arbitrary number of blocks merged one at a time. *)
Fixpoint merge_allV {dv:nat} (sts : list ((R * R) * vector R dv))
    : (R * R) * vector R dv :=
  match sts with
  | [] => ((zero, zero), vzero)
  | st :: t => mergeV st (merge_allV t)
  end.

(* -------------------------------------------------------------------------- *)
(* Main theorem: arbitrary-block streaming correctness                        *)
(* -------------------------------------------------------------------------- *)

(* Arbitrary-block streaming correctness for the ternary state: merging
   per-block (m, l, a) statistics one at a time (any number of blocks, any
   block sizes, elements in any order within blocks) yields the batch
   statistics of the whole concatenation — (global max, global re-referenced
   exp-sum, global re-referenced weighted value sum).
   Isomorphic to [online_merge_all_correct]. *)
Theorem online_merge_all_v_correct : forall {dv:nat}
    (blocks : list (list (R * vector R dv))),
  merge_allV (map statV blocks) =
  let m := lmax (map fst (List.concat blocks)) in
  ((m, lsum m (map fst (List.concat blocks))),
   vwsum m (List.concat blocks)).
Proof.
  intros dv blocks. induction blocks as [|b t IH].
  - reflexivity.
  - cbn [map merge_allV]. rewrite IH.
    replace (List.concat (b :: t)) with (b ++ List.concat t) by reflexivity.
    rewrite !map_app, lmax_app, lsum_app, vwsum_app.
    unfold statV, mergeV. cbv beta iota zeta. cbn [fst snd].
    f_equal. f_equal.
    + rewrite <- (lsum_scale (map fst b)
                  (Rmax (lmax (map fst b)) (lmax (map fst (List.concat t))))
                  (lmax (map fst b))).
      rewrite <- (lsum_scale (map fst (List.concat t))
                  (Rmax (lmax (map fst b)) (lmax (map fst (List.concat t))))
                  (lmax (map fst (List.concat t)))).
      reflexivity.
    + rewrite <- (vwsum_scale b
                  (Rmax (lmax (map fst b)) (lmax (map fst (List.concat t))))
                  (lmax (map fst b))).
      rewrite <- (vwsum_scale (List.concat t)
                  (Rmax (lmax (map fst b)) (lmax (map fst (List.concat t))))
                  (lmax (map fst (List.concat t)))).
      reflexivity.
Qed.

(* The two-block case as a direct instance. *)
Corollary online_merge_two_blocks_v : forall {dv:nat}
    (b1 b2 : list (R * vector R dv)),
  merge_allV [statV b1; statV b2] =
  let m := lmax (map fst (b1 ++ b2)) in
  ((m, lsum m (map fst (b1 ++ b2))), vwsum m (b1 ++ b2)).
Proof.
  intros dv b1 b2.
  pose proof (online_merge_all_v_correct [b1; b2]) as H.
  simpl in H. rewrite app_nil_r in H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Value-level corollaries: the normalised accumulator equals batch attention *)
(* -------------------------------------------------------------------------- *)

(* Batch attention output of a (score, value) list: softmax of the scores,
   right-multiplied by the values (one output row). *)
Definition batch_attn {dv:nat} (wv : list (R * vector R dv)) : vector R dv :=
  let m := lmax (map fst wv) in
  vscal (div one (lsum m (map fst wv))) (vwsum m wv).

(* Reading the folded ternary state as softmax(scores) * V:
   a / l (scalar-times-reciprocal form) of the merged statistics equals the
   batch attention output of the concatenated data. *)
Corollary online_merge_all_v_output : forall {dv:nat}
    (blocks : list (list (R * vector R dv))),
  vscal (div one (snd (fst (merge_allV (map statV blocks)))))
        (snd (merge_allV (map statV blocks))) =
  batch_attn (List.concat blocks).
Proof.
  intros dv blocks. unfold batch_attn. rewrite online_merge_all_v_correct.
  reflexivity.
Qed.

(* Coordinate-level reading: each output component is
   (Σ_i exp(s_i - max) * v_i) / (Σ_i exp(s_i - max)). *)
Corollary online_merge_all_v_output_coord : forall {dv:nat}
    (blocks : list (list (R * vector R dv))) (i : fin dv),
  v_idx R0
    (vscal (div one (snd (fst (merge_allV (map statV blocks)))))
           (snd (merge_allV (map statV blocks)))) i =
  div (wsum (lmax (map fst (List.concat blocks)))
            (map (fun p => (fst p, v_idx R0 (snd p) i)) (List.concat blocks)))
      (lsum (lmax (map fst (List.concat blocks)))
            (map fst (List.concat blocks))).
Proof.
  intros dv blocks i. rewrite online_merge_all_v_correct. cbn.
  rewrite v_idx_vscal, v_idx_vwsum.
  unfold div, mul, Rdiv, one. rewrite Rmult_1_l. apply Rmult_comm.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions vadd.
Print Assumptions wsum_scale.
Print Assumptions vwsum_scale.
Print Assumptions online_merge_all_v_correct.
Print Assumptions online_merge_all_v_output.
Print Assumptions online_merge_all_v_output_coord.
