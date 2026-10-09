(* Online softmax (flash-attention style streaming normalisation) is
   equivalent to batch softmax.

   Batch softmax:   softmax(x)_i = exp(x_i - max x) / Σ_j exp(x_j - max x).
   Online softmax:  stream the input, keeping a running state (m, s) with
     m_new = Rmax m_old x,   s_new = s_old * exp(m_old - m_new) + exp(x - m_new),
   and normalise at the end.

   Contents:
   - Pure math layer: [esum] (Σ exp(x_j - m) over a vector), the scaling law
     [esum_scale] (change of reference point, via exp_plus), positivity
     ([esum_nonneg]/[esum_pos_S] — the softmax denominator is always
     positive, so no division-by-zero side condition is needed);
     [online_merge] and its correctness [online_merge_correct]: merging the
     (m, s) statistics of two blocks yields the merged max and the sum of
     the two blocks re-referenced to the merged max (which *is* the sum over
     the concatenated data, split by blocks).
   - Reduction-structure layer: [online_fold] (the streaming loop the
     [reducel] skeleton computes, cf. [DPIA_Rules.reduce_aux_num]) equals the
     batch statistics ([online_fold_correct]); the main theorem
     [online_softmax_equiv]: online softmax = batch softmax on R, where the
     batch side uses [sum]/[max] — exactly the functions the [suml]/[maxl]
     two-pass commands compute (DPIA_Rules.A_sum / A_max).
   - Command layer: [online_loop] (two scalar accumulators pm/ps updated in
     a [seqfor] loop, the [reducel] shape for the pair state) computes the
     online fold ([online_loop_spec]) and hence the batch denominator
     ([online_loop_computes_denominator]).
   - Streaming/any-block-count layer: over stdlib lists,
     [online_merge_all_correct]: right-folding [online_merge] over per-block
     statistics of an arbitrary list of blocks yields (global max, global
     re-referenced sum) for the concatenation of all blocks.

   All proofs are [Qed]; only the standard classical axioms already used by
   [DPIA_Rules.v] may appear (functional extensionality / proof irrelevance
   / classical logic from the Reals library).
*)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra Lia.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.DPIA_Rules.
Import Proof_CodeGen.
Import ListNotations.

(* NOTE: after importing Proof_CodeGen, the bare identifier [exp] is the
   data-indexed expression type family, not the real exponential.  Real
   exponentials are always written via the wrapper [pExp] (or appear after
   [unfold pExp] as [Rtrigo_def.exp], the constant of [exp_plus]/[exp_pos]). *)

(* -------------------------------------------------------------------------- *)
(* Scalar bridges                                                             *)
(* -------------------------------------------------------------------------- *)

(* The project's max2 (boolean comparison) is Rmax with swapped arguments. *)
Lemma max2_Rmax : forall x y : R, max2 x y = Rmax y x.
Proof.
  intros x y. unfold max2, gtExp, Rmax.
  destruct (Rgt_dec x y) as [H | H]; destruct (Rle_dec y x) as [H0 | H0];
    simpl; try reflexivity; lra.
Qed.

(* Plain-vector indexing helpers.  [idx_pred]/[ary_idx_last] from the
   libraries cannot be used with [rewrite] here: their patterns quantify
   over [exp (ary '{S n} t)] with the bound [n] hidden under [fle_self],
   which stalls keyed matching.  These restatements keep the pair at the
   plain type [vector R (S n)] so the patterns match syntactically. *)
Lemma idx_snoc_fs : forall n (v : vector R n) (x : R) (i : fin n),
  (((v, x) : exp (ary '{S n} num))|[FS[i]]) = (v : exp (ary '{n} num))|[i].
Proof. intros. unfold idx. apply v_idx_Sn. Qed.

Lemma idx_snoc_last : forall n (v : vector R n) (x : R),
  (((v, x) : exp (ary '{S n} num))|[fin_last n]) = x.
Proof.
  intros. unfold idx, v_idx. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

Lemma idx_snoc_ltS : forall n (v : vector R n) (x : R),
  (((v, x) : exp (ary '{S n} num))|['[n]]) = x.
Proof.
  intros. unfold idx, v_idx. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(* Composing two reference-point shifts:
   exp(a - b) * exp(b - c) = exp(a - c), stated with Rmult so that it can
   rewrite goals where [add]/[mul] have been unfolded but [pExp]/[sub] are
   still folded. *)
Lemma pExp_sub_add : forall a b c : R,
  (pExp (sub a b) * pExp (sub b c))%R = pExp (sub a c).
Proof.
  intros a b c. unfold pExp, sub.
  rewrite <- exp_plus. f_equal. ring.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pure math layer: esum (sum of exponentials with reference point m)         *)
(* -------------------------------------------------------------------------- *)

(* Σ_j exp(x_j - m) over a vector, in the project's snoc-fold order. *)
Definition esum {n:nat} (m : R) (xs : vector R n) : R :=
  v_reduce (fun x acc => add acc (pExp (sub x m))) zero xs.

Lemma esum_Sn : forall {n} (v : vector R n) (x m : R),
  esum m ((v, x) : vector R (S n)) = add (esum m v) (pExp (sub x m)).
Proof. intros. unfold esum. rewrite v_reduce_Sn. reflexivity. Qed.

(* Change of reference point: Σ exp(x_j - m) = Σ exp(x_j - m') * exp(m' - m).
   This is the algebraic heart of the online rescaling step. *)
Lemma esum_scale : forall {n} (xs : vector R n) (m m' : R),
  esum m xs = mul (esum m' xs) (pExp (sub m' m)).
Proof.
  induction n as [|n IH]; intros xs m m'.
  - destruct xs. unfold esum, mul, zero. simpl. ring.
  - destruct xs as [v x]. rewrite !esum_Sn. rewrite (IH v m m').
    unfold add, mul, sub, pExp.
    replace (x - m)%R with ((x - m') + (m' - m))%R by ring.
    rewrite exp_plus. ring.
Qed.

(* The softmax denominator is a sum of positive terms. *)
Lemma esum_nonneg : forall {n} (xs : vector R n) (m : R), (zero <= esum m xs)%R.
Proof.
  induction n as [|n IH]; intros xs m.
  - destruct xs. unfold esum, zero. simpl. lra.
  - destruct xs as [v x]. rewrite esum_Sn. unfold add, pExp, sub, zero.
    apply Rplus_le_le_0_compat.
    + apply IH.
    + apply Rlt_le. apply exp_pos.
Qed.

Lemma esum_pos_S : forall {n} (xs : vector R (S n)) (m : R),
  (zero < esum m xs)%R.
Proof.
  intros n xs m. destruct xs as [v x]. rewrite esum_Sn.
  unfold add, pExp, sub, zero.
  apply Rplus_le_lt_0_compat.
  - apply esum_nonneg.
  - apply exp_pos.
Qed.

(* sum over a snoc pair peels the last element. *)
Lemma sum_Sn : forall {n} (v : vector R n) (x : R),
  sum ((v, x) : exp (ary '{S n} num)) = add x (sum v).
Proof. intros. reflexivity. Qed.

(* Bridge: esum is exactly [sum] of the mapped vector — i.e. the value the
   [suml] command computes (DPIA_Rules.A_sum). *)
Lemma esum_sum : forall {n} (xs : vector R n) (m : R),
  sum (mkvSeq (fun j : fin n => pExp (sub ((xs : exp (ary '{n} num))|[j]) m)))
  = esum m xs.
Proof.
  induction n as [|n IH]; intros xs m.
  - destruct xs. reflexivity.
  - destruct xs as [v x].
    assert (Hpre : sum (mk_vec (fun i : fin n =>
                        pExp (sub (((v, x):exp (ary '{S n} num))|[FS[i]]) m)))
                   = esum m v).
    { rewrite <- (IH v m). unfold mkvSeq. do 2 f_equal.
      apply functional_extensionality. intro i. rewrite idx_snoc_fs. reflexivity. }
    rewrite esum_Sn. unfold mkvSeq. rewrite mk_vec_S2. cbn beta.
    rewrite sum_Sn. rewrite Hpre.
    replace (exist (fun i0 : nat => (i0 < S n)%nat) n (Nat.lt_succ_diag_r n))
      with (fin_last n) by reflexivity.
    rewrite idx_snoc_last. unfold add. apply Rplus_comm.
Qed.

(* -------------------------------------------------------------------------- *)
(* Running max: rmaxl is the fold the online loop performs; it coincides      *)
(* with the batch [max] (the value [maxl] computes, DPIA_Rules.A_max).        *)
(* -------------------------------------------------------------------------- *)

Definition rmaxl {n:nat} (m0 : R) (xs : vector R n) : R :=
  v_reduce (fun x acc => Rmax acc x) m0 xs.

Lemma rmaxl_Sn : forall {n} (v : vector R n) (x m0 : R),
  rmaxl m0 ((v, x) : vector R (S n)) = Rmax (rmaxl m0 v) x.
Proof. intros. unfold rmaxl. rewrite v_reduce_Sn. reflexivity. Qed.

Lemma max_rmaxl : forall {n} (xs : vector R n), max xs = rmaxl zero xs.
Proof.
  intros n xs. rewrite max_reduce. unfold rmaxl, reduce.
  revert xs. induction n as [|n IH]; intros xs.
  - destruct xs. reflexivity.
  - destruct xs as [v x]. rewrite !v_reduce_Sn. rewrite <- (IH v).
    apply max2_Rmax.
Qed.

(* -------------------------------------------------------------------------- *)
(* online_merge: combining the (m, s) statistics of two blocks                *)
(* -------------------------------------------------------------------------- *)

Definition online_merge (st1 st2 : R * R) : R * R :=
  let '(m1, s1) := st1 in
  let '(m2, s2) := st2 in
  let m := Rmax m1 m2 in
  (m, add (mul s1 (pExp (sub m1 m))) (mul s2 (pExp (sub m2 m)))).

Lemma online_merge_fst : forall st1 st2 : R * R,
  fst (online_merge st1 st2) = Rmax (fst st1) (fst st2).
Proof. intros [m1 s1] [m2 s2]. reflexivity. Qed.

(* Merged denominator: if s1 (resp. s2) is the exp-sum of block 1 (resp. 2)
   referenced to m1 (resp. m2), then the merged s is the sum of both blocks
   referenced to the merged max — i.e. Σ over the concatenated data. *)
Lemma online_merge_snd_esum : forall {n1 n2}
    (xs1 : vector R n1) (xs2 : vector R n2) (m1 m2 s1 s2 : R),
  s1 = esum m1 xs1 ->
  s2 = esum m2 xs2 ->
  snd (online_merge (m1, s1) (m2, s2)) =
  add (esum (Rmax m1 m2) xs1) (esum (Rmax m1 m2) xs2).
Proof.
  intros n1 n2 xs1 xs2 m1 m2 s1 s2 H1 H2. subst s1 s2.
  unfold online_merge. cbv beta iota zeta. cbn [snd].
  rewrite <- (esum_scale xs1 (Rmax m1 m2) m1).
  rewrite <- (esum_scale xs2 (Rmax m1 m2) m2).
  reflexivity.
Qed.

(* Two-block merge correctness (Part 1): merging the batch statistics of two
   blocks gives (Rmax of the block maxima, sum of both blocks re-referenced
   to the merged max). *)
Theorem online_merge_correct : forall {n1 n2}
    (xs1 : vector R n1) (xs2 : vector R n2),
  online_merge (max xs1, esum (max xs1) xs1) (max xs2, esum (max xs2) xs2) =
  (Rmax (max xs1) (max xs2),
   add (esum (Rmax (max xs1) (max xs2)) xs1)
       (esum (Rmax (max xs1) (max xs2)) xs2)).
Proof.
  intros n1 n2 xs1 xs2. unfold online_merge. cbv beta iota zeta.
  f_equal; try reflexivity.
  rewrite <- (esum_scale xs1 (Rmax (max xs1) (max xs2)) (max xs1)).
  rewrite <- (esum_scale xs2 (Rmax (max xs1) (max xs2)) (max xs2)).
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reduction-structure layer: the streaming fold and its correctness          *)
(* -------------------------------------------------------------------------- *)

(* One streaming step: fold element x into state (m, s). *)
Definition online_step (st : R * R) (x : R) : R * R :=
  let '(m, s) := st in
  let m' := Rmax m x in
  (m', add (mul s (pExp (sub m m'))) (pExp (sub x m'))).

(* The streaming fold over a vector (this is the value-level content of a
   [reducel] loop with pair state, cf. DPIA_Rules.reduce_aux_num). *)
Fixpoint online_fold {n:nat} : R * R -> vector R n -> R * R :=
  match n as n0 return (R * R -> vector R n0 -> R * R) with
  | O => fun st _ => st
  | S n' => fun st xs => online_step (online_fold (n:=n') st (fst xs)) (snd xs)
  end.

(* Streaming invariant: from state (m0, s0), folding xs yields
   (M, s0 * exp(m0 - M) + Σ_j exp(x_j - M)) with M the running max. *)
Lemma online_fold_correct : forall {n} (xs : vector R n) (m0 s0 : R),
  online_fold (m0, s0) xs =
  (rmaxl m0 xs,
   (add (mul s0 (pExp (sub m0 (rmaxl m0 xs)))) (esum (rmaxl m0 xs) xs) : R)).
Proof.
  induction n as [|n IH]; intros xs m0 s0.
  - destruct xs.
    change (online_fold (m0, s0) (tt : vector R 0)) with (m0, s0).
    change (rmaxl m0 (tt : vector R 0)) with m0.
    change (esum m0 (tt : vector R 0)) with zero.
    unfold add, mul, sub, pExp, zero.
    replace (m0 - m0)%R with 0%R by ring. rewrite exp_0. f_equal; ring.
  - destruct xs as [v x].
    change (online_fold (m0, s0) ((v, x) : vector R (S n)))
      with (online_step (online_fold (m0, s0) v) x).
    rewrite IH. unfold online_step. cbv beta iota zeta.
    rewrite rmaxl_Sn. rewrite esum_Sn.
    remember (rmaxl m0 v) as rm eqn:Erm.
    f_equal; try reflexivity.
    change (exp num) with R.
    rewrite (esum_scale v (Rmax rm x) rm).
    unfold add, mul.
    rewrite Rmult_plus_distr_r.
    replace (s0 * pExp (sub m0 rm) * pExp (sub rm (Rmax rm x)))%R
      with (s0 * pExp (sub m0 (Rmax rm x)))%R.
    2: { rewrite Rmult_assoc. rewrite pExp_sub_add. reflexivity. }
    ring.
Qed.

(* Batch softmax (two passes: [maxl] then [suml], then pointwise divide). *)
Definition softmax_batch {n:nat} (xs : vector R n) (i : fin n) : R :=
  div (pExp (sub ((xs : exp (ary '{n} num))|[i]) (max xs)))
      (sum (mkvSeq (fun j : fin n =>
             pExp (sub ((xs : exp (ary '{n} num))|[j]) (max xs))))).

(* Online softmax (one streaming pass keeping (m, s), then divide). *)
Definition softmax_online {n:nat} (xs : vector R n) (i : fin n) : R :=
  let st := online_fold (zero, zero) xs in
  div (pExp (sub ((xs : exp (ary '{n} num))|[i]) (fst st))) (snd st).

(* Main theorem (Part 2): online softmax = batch softmax on R. *)
Theorem online_softmax_equiv : forall {n} (xs : vector R n) (i : fin n),
  softmax_online xs i = softmax_batch xs i.
Proof.
  intros n xs i. unfold softmax_online, softmax_batch.
  rewrite online_fold_correct. cbv zeta. cbn [fst snd].
  replace (add (mul zero (pExp (sub zero (rmaxl zero xs))))
               (esum (rmaxl zero xs) xs))
    with (esum (rmaxl zero xs) xs) by (unfold add, mul, zero; ring).
  rewrite <- max_rmaxl. rewrite <- esum_sum. reflexivity.
Qed.

(* The batch denominator is strictly positive on any non-empty input:
   no division-by-zero side condition is ever needed. *)
Lemma softmax_denom_pos : forall {n} (xs : vector R (S n)),
  (zero < sum (mkvSeq (fun j : fin (S n) =>
                 pExp (sub ((xs : exp (ary '{S n} num))|[j]) (max xs)))))%R.
Proof.
  intros n xs. rewrite esum_sum. apply esum_pos_S.
Qed.

(* Correspondingly, the online fold's second component is positive. *)
Lemma online_fold_snd_pos : forall {n} (xs : vector R (S n)),
  (zero < snd (online_fold (zero, zero) xs))%R.
Proof.
  intros n xs. rewrite online_fold_correct. cbn [snd].
  replace (add (mul zero (pExp (sub zero (rmaxl zero xs))))
               (esum (rmaxl zero xs) xs))
    with (esum (rmaxl zero xs) xs) by (unfold add, mul, zero; ring).
  apply esum_pos_S.
Qed.

(* -------------------------------------------------------------------------- *)
(* Command layer: the online loop as an imperative command                    *)
(* -------------------------------------------------------------------------- *)

(* Reading a scalar accumulator at a path. *)
Definition read_num (rho : env) (p : path) : R :=
  read_exp rho (acc' p : acc num).

Lemma read_num_Some : forall (rho : env) (p : path) (v : R),
  rho p = Some v -> read_num rho p = v.
Proof.
  intros rho p v H. unfold read_num, read_exp. rewrite acc'_num, access_num, H.
  reflexivity.
Qed.

(* Loop body: read the running (m, s), fold in xs[i].  The [ps] assignment is
   executed first (innermost) and reads the OLD m, matching [online_step]. *)
Definition online_loop_body {n:nat} (xs : exp (ary '{n} num))
    (pm ps : path) (i : fin n) : comm :=
  fun rho =>
    ((acc' pm : acc num) |:= Rmax (read_num rho pm) (xs|[i]))
    (((acc' ps : acc num) |:= add (mul (read_num rho ps)
                            (pExp (sub (read_num rho pm)
                                       (Rmax (read_num rho pm) (xs|[i])))))
                      (pExp (sub (xs|[i])
                                 (Rmax (read_num rho pm) (xs|[i]))))) rho).

(* The full online pass: initialise (m, s) := (0, 0), then stream. *)
Definition online_loop {n:nat} (xs : exp (ary '{n} num)) (pm ps : path) : comm :=
  (acc' pm |:= zero) ';
  ((acc' ps |:= zero) '; seqfor (fun i : fin n => online_loop_body xs pm ps i)).

(* Loop invariant, snoc induction mirroring DPIA_Rules.reduce_aux_num. *)
Lemma online_loop_aux : forall {n} (xs : exp (ary '{n} num))
    (pm ps : path) (rho : env) (m0 s0 : R),
  pm <> ps ->
  rho pm = Some m0 ->
  rho ps = Some s0 ->
  seqfor (fun i : fin n => online_loop_body xs pm ps i) rho pm =
    Some (fst (online_fold (m0, s0) xs)) /\
  seqfor (fun i : fin n => online_loop_body xs pm ps i) rho ps =
    Some (snd (online_fold (m0, s0) xs)).
Proof.
  induction n as [|n IH]; intros xs pm ps rho m0 s0 Hneq Hpm Hps.
  - destruct xs. simpl. split; assumption.
  - destruct xs as [v x]. rewrite seqfor_Sn. unfold seq. cbv beta.
    assert (Hbody : forall i : fin n,
      online_loop_body ((v, x) : exp (ary '{S n} num)) pm ps FS[i]
      = online_loop_body v pm ps i).
    { intro i. apply functional_extensionality. intro rho0.
      unfold online_loop_body. rewrite idx_snoc_fs. reflexivity. }
    rewrite (seqfor_extensionality _ _ Hbody).
    set (rho1 := seqfor (fun i : fin n => online_loop_body v pm ps i) rho).
    destruct (online_fold (m0, s0) (v : exp (ary '{n} num))) as [mv sv] eqn:Efold.
    destruct (IH v pm ps rho m0 s0 Hneq Hpm Hps) as [Hpm1 Hps1].
    rewrite Efold in Hpm1, Hps1. cbn [fst snd] in Hpm1, Hps1.
    fold rho1 in Hpm1, Hps1.
    change (online_fold (m0, s0) ((v, x) : vector R (S n)))
      with (online_step (online_fold (m0, s0) (v : exp (ary '{n} num))) x).
    rewrite Efold. unfold online_step. cbv beta iota zeta.
    cbn [fst snd].
    unfold online_loop_body. cbv beta. rewrite idx_snoc_ltS.
    rewrite (read_num_Some _ _ _ Hpm1).
    rewrite (read_num_Some _ _ _ Hps1).
    split.
    + rewrite assign_num. rewrite !acc'_num. rewrite update_eq. reflexivity.
    + rewrite assign_num. rewrite !acc'_num. rewrite update_neq by exact Hneq.
      rewrite assign_num. rewrite update_eq. reflexivity.
Qed.

(* The online loop stores exactly the online fold's final state. *)
Theorem online_loop_spec : forall {n} (xs : exp (ary '{n} num))
    (pm ps : path) (rho : env),
  pm <> ps ->
  online_loop xs pm ps rho pm = Some (fst (online_fold (zero, zero) xs)) /\
  online_loop xs pm ps rho ps = Some (snd (online_fold (zero, zero) xs)).
Proof.
  intros n xs pm ps rho Hneq.
  unfold online_loop, seq. cbv beta.
  rewrite !assign_num, !acc'_num.
  apply online_loop_aux with (m0 := zero) (s0 := zero).
  - exact Hneq.
  - rewrite update_neq by (exact (not_eq_sym Hneq)). apply update_eq.
  - apply update_eq.
Qed.

(* Command-level reading of [online_softmax_equiv]: the streaming loop leaves
   in [ps] exactly the denominator that the batch two-pass ([maxl] then
   [suml], via DPIA_Rules.A_max / A_sum) computes. *)
Corollary online_loop_computes_denominator : forall {n} (xs : exp (ary '{n} num))
    (pm ps : path) (rho : env),
  pm <> ps ->
  online_loop xs pm ps rho ps =
  Some (sum (mkvSeq (fun j : fin n => pExp (sub (xs|[j]) (max xs))))).
Proof.
  intros n xs pm ps rho Hneq.
  destruct (online_loop_spec xs pm ps rho Hneq) as [_ Hps].
  rewrite Hps. f_equal.
  rewrite online_fold_correct. cbn [snd].
  replace (add (mul zero (pExp (sub zero (rmaxl zero xs))))
               (esum (rmaxl zero xs) xs))
    with (esum (rmaxl zero xs) xs) by (unfold add, mul, zero; ring).
  rewrite <- max_rmaxl. rewrite <- esum_sum. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Streaming layer (Part 3): merging an arbitrary number of blocks            *)
(* -------------------------------------------------------------------------- *)

(* List-level exp-sum with reference point m. *)
Fixpoint lsum (m : R) (l : list R) : R :=
  match l with
  | [] => zero
  | x :: t => add (pExp (sub x m)) (lsum m t)
  end.

Fixpoint lmax (l : list R) : R :=
  match l with
  | [] => zero
  | x :: t => Rmax x (lmax t)
  end.

(* Per-block online-softmax statistics. *)
Definition block_stat (l : list R) : R * R := (lmax l, lsum (lmax l) l).

(* Right fold of [online_merge] over a list of block statistics:
   an arbitrary number of blocks merged one at a time. *)
Fixpoint merge_allr (sts : list (R * R)) : R * R :=
  match sts with
  | [] => (zero, zero)
  | st :: t => online_merge st (merge_allr t)
  end.

Lemma lsum_scale : forall (l : list R) (m m' : R),
  lsum m l = mul (lsum m' l) (pExp (sub m' m)).
Proof.
  induction l as [|x t IH]; intros m m'.
  - simpl. unfold mul, zero. ring.
  - simpl. rewrite (IH m m'). unfold add, mul, sub, pExp.
    replace (x - m)%R with ((x - m') + (m' - m))%R by ring.
    rewrite exp_plus. ring.
Qed.

Lemma lsum_app : forall (l1 l2 : list R) (m : R),
  lsum m (l1 ++ l2) = add (lsum m l1) (lsum m l2).
Proof.
  induction l1 as [|x t IH]; intros l2 m.
  - simpl. unfold add, zero. ring.
  - simpl. rewrite IH. unfold add. ring.
Qed.

Lemma lsum_nonneg : forall (l : list R) (m : R), (zero <= lsum m l)%R.
Proof.
  induction l as [|x t IH]; intros m.
  - simpl. unfold zero. lra.
  - simpl. unfold add, pExp, sub, zero.
    apply Rplus_le_le_0_compat.
    + apply Rlt_le. apply exp_pos.
    + apply IH.
Qed.

Lemma lsum_pos : forall (l : list R) (m : R), l <> [] -> (zero < lsum m l)%R.
Proof.
  intros l m Hne. destruct l as [|x t].
  - contradiction.
  - simpl. unfold add, pExp, sub, zero.
    apply Rplus_lt_le_0_compat.
    + apply exp_pos.
    + apply lsum_nonneg.
Qed.

Lemma lmax_nonneg : forall l : list R, (zero <= lmax l)%R.
Proof.
  induction l as [|x t IH].
  - simpl. unfold zero. lra.
  - simpl. eapply Rle_trans. exact IH. apply Rmax_r.
Qed.

Lemma lmax_app : forall l1 l2 : list R,
  lmax (l1 ++ l2) = Rmax (lmax l1) (lmax l2).
Proof.
  induction l1 as [|x t IH]; intros l2.
  - simpl. symmetry. apply Rmax_right. apply lmax_nonneg.
  - simpl. rewrite IH. rewrite Rmax_assoc. reflexivity.
Qed.

(* Arbitrary-block streaming correctness: merging per-block statistics one at
   a time (any number of blocks) yields the batch statistics of the whole
   concatenation.  Subsumes the two-block [online_merge_correct]. *)
Theorem online_merge_all_correct : forall blocks : list (list R),
  merge_allr (map block_stat blocks) =
  (lmax (List.concat blocks),
   lsum (lmax (List.concat blocks)) (List.concat blocks)).
Proof.
  induction blocks as [|b t IH].
  - reflexivity.
  - simpl. rewrite IH. unfold block_stat.
    rewrite lmax_app, lsum_app.
    unfold online_merge. cbv beta iota zeta.
    f_equal; try reflexivity.
    rewrite <- (lsum_scale b (Rmax (lmax b) (lmax (List.concat t))) (lmax b)).
    rewrite <- (lsum_scale (List.concat t)
                           (Rmax (lmax b) (lmax (List.concat t)))
                           (lmax (List.concat t))).
    reflexivity.
Qed.

(* The two-block case as a direct instance. *)
Corollary online_merge_two_blocks : forall b1 b2 : list R,
  merge_allr [block_stat b1; block_stat b2] =
  (lmax (b1 ++ b2), lsum (lmax (b1 ++ b2)) (b1 ++ b2)). (* List.concat [b1;b2] *)
Proof.
  intros b1 b2.
  pose proof (online_merge_all_correct [b1; b2]) as H.
  simpl in H. rewrite app_nil_r in H. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions online_merge_correct.
Print Assumptions online_softmax_equiv.
Print Assumptions online_loop_spec.
Print Assumptions online_loop_computes_denominator.
Print Assumptions online_merge_all_correct.
