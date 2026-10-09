(* ========================================================================= *)
(* Opt_ApproxError.v                                                         *)
(*                                                                           *)
(* Approximate-precision (opt-in) track: compositional error bounds for an   *)
(* abstract rounding operator on R.                                          *)
(*                                                                           *)
(* Relation to the strict track: in Proof_CodeGen.v / DPIA_Rules.v the       *)
(* numeric semantics is exact (exp num = R), hence every DPIA rewrite rule   *)
(* (A_reduce_num, reduce_Sn, ...) is a Leibniz equality.  The present file   *)
(* is the proof side of the *approximate* variant: we introduce an abstract  *)
(* rounding operator                                                         *)
(*      rnd : R -> R   with   |rnd x - x| <= u * |x|                         *)
(* (TF32: 10-bit mantissa, u = 2^-11; FP16 has the same u; FP32: u = 2^-24). *)
(* rnd is not constructively definable on R, so it is given as a section     *)
(* variable together with the standard-model property; every theorem is      *)
(* thereby proved for *any* rounding satisfying it (TF32/FP16/FP32 are       *)
(* instances).  No Admitted, no Axiom: after [End RoundingModel] all results *)
(* are ordinary closed theorems, quantified over u and rnd.                  *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   1. Elementary rounding bounds for + - * / (plus compositional forms     *)
(*      with already-perturbed inputs).                                      *)
(*   2. Reduction error bound (core): rsum_rnd vs rsum,                      *)
(*        |Shat - S| <= gamma_n * Sum|x_i|,   gamma_n = (1+u)^n - 1          *)
(*      (the classical form, gamma_n = n*u + O(u^2)).  The exact sum rsum    *)
(*      is literally the semantics computed by A_reduce_num / reducel        *)
(*      (see rsum_eq_sum).                                                   *)
(*   3. Dot-product / conv layer bound:                                      *)
(*        |dhat - d| <= gamma_{n+1} * Sum|w_i * x_i|                         *)
(*      (rounded products + rounded accumulation).  A conv output with       *)
(*      kernel size k and c input channels is a dot product of length k*c    *)
(*      (2D conv: k*k*c), see conv_dot_error.                                *)
(*   4. End-to-end LeNet-5 example: conv1 (5*5*1 = 25 products) followed by  *)
(*      fc1 (400 products), with input-error propagation.                    *)
(* ========================================================================= *)

Require Import Reals Lra Psatz Arith.
Require Import Ionia.Proof_CodeGen.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* Vector-level utilities (pure real semantics, no rounding)                  *)
(* -------------------------------------------------------------------------- *)

(* Exact sum over a real vector: this is the accumulator semantics of
   [reducel add zero] / [A_reduce_num] (see rsum_eq_sum below). *)
Definition rsum {n:nat} (xs : vector R n) : R := v_reduce Rplus 0 xs.

(* Unary pointwise map on the snoc structure (avoids the index-based v_map). *)
Fixpoint v_map1 (f : R -> R) (n:nat) : vector R n -> vector R n :=
  match n return (vector R n -> vector R n) with
  | 0 => fun _ => tt
  | S n' => fun a => (v_map1 f n' (fst a), f (snd a))
  end.

(* Binary pointwise combination on the snoc structure. *)
Fixpoint v_pw2 {A B C : Set} (f : A -> B -> C) (n:nat)
  : vector A n -> vector B n -> vector C n :=
  match n return (vector A n -> vector B n -> vector C n) with
  | 0 => fun _ _ => tt
  | S n' => fun a b => (v_pw2 f n' (fst a) (fst b), f (snd a) (snd b))
  end.

(* Pointwise relation between two vectors. *)
Fixpoint v_pw_rel {A B : Set} (P : A -> B -> Prop) (n:nat)
  : vector A n -> vector B n -> Prop :=
  match n return (vector A n -> vector B n -> Prop) with
  | 0 => fun _ _ => True
  | S n' => fun a b => v_pw_rel P n' (fst a) (fst b) /\ P (snd a) (snd b)
  end.

(* Every component satisfies P. *)
Fixpoint v_all (P : R -> Prop) (n:nat) : vector R n -> Prop :=
  match n return (vector R n -> Prop) with
  | 0 => fun _ => True
  | S n' => fun a => v_all P n' (fst a) /\ P (snd a)
  end.

(* Sum of absolute values, Sum_i |x_i|. *)
Definition v_abs_sum {n:nat} (xs : vector R n) : R := rsum (v_map1 Rabs n xs).

Lemma rsum_Sn : forall (n:nat) (xs : vector R n) (x:R),
  rsum ((xs, x) : vector R (S n)) = x + rsum xs.
Proof. intros. unfold rsum. rewrite v_reduce_Sn. reflexivity. Qed.

Lemma v_map1_Sn : forall (f : R -> R) (n:nat) (a1 : vector R n) (a2 : R),
  v_map1 f (S n) ((a1, a2) : vector R (S n)) = ((v_map1 f n a1, f a2) : vector R (S n)).
Proof. reflexivity. Qed.

Lemma v_pw2_Sn : forall {A B C : Set} (f : A -> B -> C) (n:nat)
    (a1 : vector A n) (b1 : vector B n) (a2 : A) (b2 : B),
  v_pw2 f (S n) ((a1, a2) : vector A (S n)) ((b1, b2) : vector B (S n))
  = ((v_pw2 f n a1 b1, f a2 b2) : vector C (S n)).
Proof. reflexivity. Qed.

Lemma v_abs_sum_Sn : forall (n:nat) (xs : vector R n) (x:R),
  v_abs_sum ((xs, x) : vector R (S n)) = Rabs x + v_abs_sum xs.
Proof. intros. unfold v_abs_sum. rewrite v_map1_Sn, rsum_Sn. ring. Qed.

(* Bridge to the strict track: the exact sum computed by the reduction
   skeleton (A_reduce_num / reduce_Sn in DPIA_Rules.v) is precisely rsum. *)
Lemma rsum_eq_sum : forall (n:nat) (xs : vector R n),
  rsum xs = sum xs.
Proof. reflexivity. Qed.

Lemma rsum_triangle : forall (n:nat) (xs : vector R n),
  Rabs (rsum xs) <= v_abs_sum xs.
Proof.
  intros n; induction n as [|n IHn]; intros xs.
  - destruct xs. unfold v_abs_sum, rsum. simpl.
    rewrite Rabs_R0. lra.
  - destruct xs as [xs' x].
    rewrite rsum_Sn, v_abs_sum_Sn.
    pose proof (IHn xs') as IH.
    pose proof (Rabs_triang x (rsum xs')) as Ht.
    lra.
Qed.

Lemma v_abs_sum_nonneg : forall (n:nat) (xs : vector R n),
  0 <= v_abs_sum xs.
Proof.
  intros n; induction n as [|n IHn]; intros xs.
  - destruct xs. unfold v_abs_sum, rsum. simpl. lra.
  - destruct xs as [xs' x]. rewrite v_abs_sum_Sn.
    pose proof (IHn xs'). pose proof (Rabs_pos x). lra.
Qed.

Lemma rsum_pw_le : forall (n:nat) (a b : vector R n),
  v_pw_rel Rle n a b -> rsum a <= rsum b.
Proof.
  intros n; induction n as [|n IHn]; intros a b H.
  - destruct a, b. unfold rsum. simpl. lra.
  - destruct a as [a1 a2], b as [b1 b2].
    destruct H as [Hrec Hlast].
    rewrite !rsum_Sn. apply Rplus_le_compat; auto.
Qed.

Lemma rsum_pw2_sub_abs : forall (n:nat) (a b : vector R n),
  Rabs (rsum a - rsum b) <= rsum (v_pw2 (fun x y => Rabs (x - y)) n a b).
Proof.
  intros n; induction n as [|n IHn]; intros a b.
  - destruct a, b. unfold rsum. simpl.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - destruct a as [a1 a2], b as [b1 b2].
    rewrite v_pw2_Sn, !rsum_Sn.
    pose proof (IHn a1 b1) as IH.
    replace (a2 + rsum a1 - (b2 + rsum b1))
      with ((a2 - b2) + (rsum a1 - rsum b1)) by ring.
    pose proof (Rabs_triang (a2 - b2) (rsum a1 - rsum b1)) as Ht.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* The abstract rounding model                                                *)
(* -------------------------------------------------------------------------- *)

Section RoundingModel.

Variable u : R.
Hypothesis Hu : 0 <= u.

Variable rnd : R -> R.
Hypothesis rnd_rel : forall x:R, Rabs (rnd x - x) <= u * Rabs x.

(* gamma_n = (1+u)^n - 1, the classical accumulated relative-error factor. *)
Lemma pow_1pu_ge_1 : forall n:nat, 1 <= (1 + u) ^ n.
Proof.
  induction n as [|n IHn].
  - simpl. lra.
  - replace ((1 + u) ^ S n) with ((1 + u) * (1 + u) ^ n) by reflexivity.
    replace 1 with (1 * 1) at 1 by ring.
    apply Rmult_le_compat; lra.
Qed.

Lemma gamma_nonneg : forall n:nat, 0 <= (1 + u) ^ n - 1.
Proof. intros. pose proof (pow_1pu_ge_1 n). lra. Qed.

(* ---- 1. Elementary rounding bounds ---- *)

Lemma rnd_abs_bound : forall x:R, Rabs (rnd x) <= (1 + u) * Rabs x.
Proof.
  intro x. pose proof (rnd_rel x) as H.
  assert (Ht : Rabs (rnd x) <= Rabs (rnd x - x) + Rabs x).
  { replace (rnd x) with ((rnd x - x) + x) at 1 by ring. apply Rabs_triang. }
  lra.
Qed.

Lemma rnd_add_err : forall x y:R,
  Rabs (rnd (x + y) - (x + y)) <= u * Rabs (x + y).
Proof. intros. apply rnd_rel. Qed.

Lemma rnd_sub_err : forall x y:R,
  Rabs (rnd (x - y) - (x - y)) <= u * Rabs (x - y).
Proof. intros. apply rnd_rel. Qed.

Lemma rnd_mul_err : forall x y:R,
  Rabs (rnd (x * y) - x * y) <= u * Rabs (x * y).
Proof. intros. apply rnd_rel. Qed.

Lemma rnd_div_err : forall x y:R,
  Rabs (rnd (x / y) - x / y) <= u * Rabs (x / y).
Proof. intros. apply rnd_rel. Qed.

(* Compositional forms: inputs may already carry perturbations. *)
Lemma add_err_compositional : forall a b x y:R,
  Rabs (rnd (a + b) - (x + y))
  <= u * Rabs (a + b) + Rabs (a - x) + Rabs (b - y).
Proof.
  intros. pose proof (rnd_rel (a + b)) as H.
  replace (rnd (a + b) - (x + y))
    with ((rnd (a + b) - (a + b)) + ((a - x) + (b - y))) by ring.
  eapply Rle_trans. apply Rabs_triang.
  pose proof (Rabs_triang (a - x) (b - y)) as Ht.
  lra.
Qed.

Lemma mul_err_compositional : forall a b x y:R,
  Rabs (rnd (a * b) - x * y)
  <= u * Rabs (a * b) + Rabs b * Rabs (a - x) + Rabs x * Rabs (b - y).
Proof.
  intros. pose proof (rnd_rel (a * b)) as H.
  replace (rnd (a * b) - x * y)
    with ((rnd (a * b) - a * b) + ((a - x) * b + x * (b - y))) by ring.
  eapply Rle_trans. apply Rabs_triang.
  pose proof (Rabs_triang ((a - x) * b) (x * (b - y))) as Ht.
  rewrite !Rabs_mult in Ht.
  lra.
Qed.

(* ---- 2. Reduction error bound (core) ---- *)

(* Rounded sequential accumulation: the approximate counterpart of the
   accumulator loop that [reducel add zero] / [A_reduce_num] implement.
   acc_{i+1} = rnd (x_i + acc_i),  acc_0 = 0. *)
Definition rsum_rnd {n:nat} (xs : vector R n) : R :=
  v_reduce (fun x acc => rnd (x + acc)) 0 xs.

Lemma rsum_rnd_Sn : forall (n:nat) (xs : vector R n) (x:R),
  rsum_rnd ((xs, x) : vector R (S n)) = rnd (x + rsum_rnd xs).
Proof. intros. unfold rsum_rnd. rewrite v_reduce_Sn. reflexivity. Qed.

(* Main reduction bound: |Shat - S| <= gamma_n * Sum|x_i|,
   gamma_n = (1+u)^n - 1 = n*u + O(u^2). *)
Theorem rsum_rnd_error : forall (n:nat) (xs : vector R n),
  Rabs (rsum_rnd xs - rsum xs) <= ((1 + u) ^ n - 1) * v_abs_sum xs.
Proof.
  intros n; induction n as [|n IHn]; intros xs.
  - destruct xs. unfold rsum_rnd, rsum, v_abs_sum. simpl.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - destruct xs as [xs' x].
    rewrite rsum_Sn, rsum_rnd_Sn, v_abs_sum_Sn.
    pose proof (IHn xs') as IH.
    pose proof (rnd_rel (x + rsum_rnd xs')) as Hr.
    pose proof (rsum_triangle n xs') as Htri.
    pose proof (v_abs_sum_nonneg n xs') as Hm.
    pose proof (pow_1pu_ge_1 n) as Hg1.
    pose proof (Rabs_pos x) as Hx.
    assert (Hsplit : Rabs (rnd (x + rsum_rnd xs') - (x + rsum xs'))
            <= Rabs (rnd (x + rsum_rnd xs') - (x + rsum_rnd xs'))
               + Rabs (rsum_rnd xs' - rsum xs')).
    { replace (rnd (x + rsum_rnd xs') - (x + rsum xs'))
        with ((rnd (x + rsum_rnd xs') - (x + rsum_rnd xs'))
              + (rsum_rnd xs' - rsum xs')) by ring.
      apply Rabs_triang. }
    assert (Harg : Rabs (x + rsum_rnd xs')
            <= Rabs x + v_abs_sum xs' + ((1 + u) ^ n - 1) * v_abs_sum xs').
    { assert (H1 : Rabs (x + rsum_rnd xs')
              <= Rabs (x + rsum xs') + Rabs (rsum_rnd xs' - rsum xs')).
      { replace (x + rsum_rnd xs')
          with ((x + rsum xs') + (rsum_rnd xs' - rsum xs')) by ring.
        apply Rabs_triang. }
      pose proof (Rabs_triang x (rsum xs')) as H2.
      lra. }
    assert (Hstep : Rabs (rnd (x + rsum_rnd xs') - (x + rsum xs'))
            <= u * (Rabs x + v_abs_sum xs' + ((1 + u) ^ n - 1) * v_abs_sum xs')
               + ((1 + u) ^ n - 1) * v_abs_sum xs').
    { assert (Hu' : u * Rabs (x + rsum_rnd xs')
              <= u * (Rabs x + v_abs_sum xs' + ((1 + u) ^ n - 1) * v_abs_sum xs')).
      { apply Rmult_le_compat_l; lra. }
      lra. }
    replace ((1 + u) ^ S n) with ((1 + u) * (1 + u) ^ n) by reflexivity.
    assert (Hnn : 0 <= (1 + u) * ((1 + u) ^ n - 1) * Rabs x).
    { apply Rmult_le_pos. apply Rmult_le_pos; lra. apply Rabs_pos. }
    nra.
Qed.

(* ---- 3. Dot product / conv layer ---- *)

(* Exact dot product. *)
Definition dot_exact {n:nat} (w x : vector R n) : R := rsum (v_pw2 Rmult n w x).

(* Rounded dot product: each product is rounded, accumulation is rounded. *)
Definition dot_rnd {n:nat} (w x : vector R n) : R :=
  rsum_rnd (v_pw2 (fun a b => rnd (a * b)) n w x).

Lemma v_abs_sum_pwmul_rnd : forall (n:nat) (w x : vector R n),
  v_abs_sum (v_pw2 (fun a b => rnd (a * b)) n w x)
  <= (1 + u) * v_abs_sum (v_pw2 Rmult n w x).
Proof.
  intros n; induction n as [|n IHn]; intros w x.
  - destruct w, x. unfold v_abs_sum, rsum. simpl. lra.
  - destruct w as [w1 w2], x as [x1 x2].
    rewrite !v_pw2_Sn, !v_abs_sum_Sn.
    pose proof (IHn w1 x1) as IH.
    pose proof (rnd_abs_bound (w2 * x2)) as Hb.
    pose proof (v_abs_sum_nonneg n (v_pw2 Rmult n w1 x1)) as Hm.
    pose proof (Rabs_pos (w2 * x2)) as Hp.
    lra.
Qed.

Lemma rsum_pwmul_rnd_sub : forall (n:nat) (w x : vector R n),
  rsum (v_pw2 (fun p q => Rabs (p - q)) n
          (v_pw2 (fun a b => rnd (a * b)) n w x)
          (v_pw2 Rmult n w x))
  <= u * v_abs_sum (v_pw2 Rmult n w x).
Proof.
  intros n; induction n as [|n IHn]; intros w x.
  - destruct w, x. unfold v_abs_sum, rsum. simpl. lra.
  - destruct w as [w1 w2], x as [x1 x2].
    rewrite !v_pw2_Sn, rsum_Sn, v_abs_sum_Sn.
    pose proof (IHn w1 x1) as IH.
    pose proof (rnd_rel (w2 * x2)) as Hr.
    lra.
Qed.

(* Dot-product bound: |dhat - d| <= gamma_{n+1} * Sum|w_i x_i|. *)
Theorem dot_rnd_error : forall (n:nat) (w x : vector R n),
  Rabs (dot_rnd w x - dot_exact w x)
  <= ((1 + u) ^ (S n) - 1) * v_abs_sum (v_pw2 Rmult n w x).
Proof.
  intros n w x. unfold dot_rnd, dot_exact.
  pose proof (rsum_rnd_error n (v_pw2 (fun a b => rnd (a * b)) n w x)) as H1.
  pose proof (rsum_pw2_sub_abs n (v_pw2 (fun a b => rnd (a * b)) n w x)
                                 (v_pw2 Rmult n w x)) as H2.
  pose proof (rsum_pwmul_rnd_sub n w x) as H3.
  pose proof (v_abs_sum_pwmul_rnd n w x) as H4.
  pose proof (pow_1pu_ge_1 n) as Hg1.
  assert (Hsplit : Rabs (rsum_rnd (v_pw2 (fun a b => rnd (a * b)) n w x)
                         - rsum (v_pw2 Rmult n w x))
          <= Rabs (rsum_rnd (v_pw2 (fun a b => rnd (a * b)) n w x)
                   - rsum (v_pw2 (fun a b => rnd (a * b)) n w x))
             + Rabs (rsum (v_pw2 (fun a b => rnd (a * b)) n w x)
                     - rsum (v_pw2 Rmult n w x))).
  { replace (rsum_rnd (v_pw2 (fun a b => rnd (a * b)) n w x)
             - rsum (v_pw2 Rmult n w x))
      with ((rsum_rnd (v_pw2 (fun a b => rnd (a * b)) n w x)
             - rsum (v_pw2 (fun a b => rnd (a * b)) n w x))
            + (rsum (v_pw2 (fun a b => rnd (a * b)) n w x)
               - rsum (v_pw2 Rmult n w x))) by ring.
    apply Rabs_triang. }
  assert (H5 : ((1 + u) ^ n - 1) * v_abs_sum (v_pw2 (fun a b => rnd (a * b)) n w x)
        <= ((1 + u) ^ n - 1) * ((1 + u) * v_abs_sum (v_pw2 Rmult n w x))).
  { apply Rmult_le_compat_l; lra. }
  replace ((1 + u) ^ S n) with ((1 + u) * (1 + u) ^ n) by reflexivity.
  nra.
Qed.

(* A conv output with kernel size k and c input channels is a dot product of
   length k*c (for a 2D k x k kernel: k*k*c).  Hence the conv-layer bound. *)
Corollary conv_dot_error : forall (k c : nat) (w x : vector R (k * c)%nat),
  Rabs (dot_rnd w x - dot_exact w x)
  <= ((1 + u) ^ (S (k * c)) - 1) * v_abs_sum (v_pw2 Rmult (k * c)%nat w x).
Proof. intros. apply dot_rnd_error. Qed.

(* Relative form, given a condition-number-style hypothesis
   Sum|w_i x_i| <= kappa * |d|. *)
Theorem dot_rnd_rel_error : forall (n:nat) (w x : vector R n) (kappa : R),
  0 <= kappa ->
  v_abs_sum (v_pw2 Rmult n w x) <= kappa * Rabs (dot_exact w x) ->
  Rabs (dot_rnd w x - dot_exact w x)
  <= kappa * (((1 + u) ^ (S n) - 1) * Rabs (dot_exact w x)).
Proof.
  intros n w x kappa Hk Hcond.
  pose proof (dot_rnd_error n w x) as H.
  pose proof (gamma_nonneg (S n)) as Hg.
  assert (Hm : ((1+u)^(S n) - 1) * v_abs_sum (v_pw2 Rmult n w x)
        <= ((1+u)^(S n) - 1) * (kappa * Rabs (dot_exact w x))).
  { apply Rmult_le_compat_l; assumption. }
  lra.
Qed.

(* ---- 4. Layer composition and the LeNet-5 end-to-end example ---- *)

(* Error propagation of the exact dot product under perturbed inputs. *)
Lemma dot_exact_perturb : forall (n:nat) (w c chat delta : vector R n),
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= snd p) n chat
    (v_pw2 (@pair R R) n c delta) ->
  Rabs (dot_exact w chat - dot_exact w c)
  <= rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w delta).
Proof.
  intros n; induction n as [|n IHn]; intros w c chat delta H.
  - destruct w, c, chat, delta. unfold dot_exact, rsum. simpl.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. lra.
  - destruct w as [w1 w2], c as [c1 c2], chat as [ch1 ch2], delta as [d1 d2].
    destruct H as [Hrec Hlast].
    assert (Hlast' : Rabs (ch2 - c2) <= d2) by exact Hlast.
    pose proof (IHn w1 c1 ch1 d1 Hrec) as IH. unfold dot_exact in IH.
    unfold dot_exact. rewrite !v_pw2_Sn, !rsum_Sn.
    replace (w2 * ch2 + rsum (v_pw2 Rmult n w1 ch1)
             - (w2 * c2 + rsum (v_pw2 Rmult n w1 c1)))
      with (w2 * (ch2 - c2)
            + (rsum (v_pw2 Rmult n w1 ch1) - rsum (v_pw2 Rmult n w1 c1))) by ring.
    eapply Rle_trans. apply Rabs_triang.
    rewrite Rabs_mult.
    assert (K : Rabs w2 * Rabs (ch2 - c2) <= Rabs w2 * d2).
    { apply Rmult_le_compat_l. apply Rabs_pos. exact Hlast'. }
    lra.
Qed.

(* The absolute sum of products with perturbed inputs. *)
Lemma v_abs_sum_pwmul_perturb : forall (n:nat) (w c chat delta : vector R n),
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= snd p) n chat
    (v_pw2 (@pair R R) n c delta) ->
  v_abs_sum (v_pw2 Rmult n w chat)
  <= v_abs_sum (v_pw2 Rmult n w c)
     + rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w delta).
Proof.
  intros n; induction n as [|n IHn]; intros w c chat delta H.
  - destruct w, c, chat, delta. unfold v_abs_sum, rsum. simpl. lra.
  - destruct w as [w1 w2], c as [c1 c2], chat as [ch1 ch2], delta as [d1 d2].
    destruct H as [Hrec Hlast].
    assert (Hlast' : Rabs (ch2 - c2) <= d2) by exact Hlast.
    pose proof (IHn w1 c1 ch1 d1 Hrec) as IH.
    rewrite !v_pw2_Sn, !v_abs_sum_Sn, rsum_Sn, !Rabs_mult.
    assert (K1 : Rabs w2 * Rabs ch2 <= Rabs w2 * (Rabs c2 + Rabs (ch2 - c2))).
    { apply Rmult_le_compat_l. apply Rabs_pos.
      replace ch2 with (c2 + (ch2 - c2)) at 1 by ring. apply Rabs_triang. }
    assert (K2 : Rabs w2 * Rabs (ch2 - c2) <= Rabs w2 * d2).
    { apply Rmult_le_compat_l. apply Rabs_pos. exact Hlast'. }
    lra.
Qed.

(* Generic two-layer composition: a rounded dot product over inputs that are
   themselves outputs of a previous (approximate) layer with pointwise error
   bound delta. *)
Theorem two_layer_error : forall (n:nat) (w c chat delta : vector R n),
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= snd p) n chat
    (v_pw2 (@pair R R) n c delta) ->
  Rabs (dot_rnd w chat - dot_exact w c)
  <= ((1 + u) ^ (S n) - 1)
       * (v_abs_sum (v_pw2 Rmult n w c)
          + rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w delta))
     + rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w delta).
Proof.
  intros n w c chat delta H.
  pose proof (dot_rnd_error n w chat) as H1.
  pose proof (dot_exact_perturb n w c chat delta H) as H2.
  pose proof (v_abs_sum_pwmul_perturb n w c chat delta H) as H3.
  pose proof (gamma_nonneg (S n)) as Hg.
  assert (Hsplit : Rabs (dot_rnd w chat - dot_exact w c)
          <= Rabs (dot_rnd w chat - dot_exact w chat)
             + Rabs (dot_exact w chat - dot_exact w c)).
  { replace (dot_rnd w chat - dot_exact w c)
      with ((dot_rnd w chat - dot_exact w chat)
            + (dot_exact w chat - dot_exact w c)) by ring.
    apply Rabs_triang. }
  assert (H4 : ((1+u)^(S n) - 1) * v_abs_sum (v_pw2 Rmult n w chat)
        <= ((1+u)^(S n) - 1)
             * (v_abs_sum (v_pw2 Rmult n w c)
                + rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w delta))).
  { apply Rmult_le_compat_l; assumption. }
  lra.
Qed.

(* Scaling helpers for the end-to-end instantiation. *)
Lemma v_all_map_scale : forall (n:nat) (g:R) (S0 : vector R n),
  0 <= g ->
  v_all (fun s => 0 <= s) n S0 ->
  v_all (fun d => 0 <= d) n (v_map1 (Rmult g) n S0).
Proof.
  intros n; induction n as [|n IHn]; intros g S0 Hg H.
  - destruct S0. exact I.
  - destruct S0 as [s1 s2]. destruct H as [Hrec Hlast].
    split. apply IHn; auto.
    apply Rmult_le_pos; auto.
Qed.

Lemma v_pw_rel_scale : forall (n:nat) (g:R) (chat c S0 : vector R n),
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= g * snd p) n chat
    (v_pw2 (@pair R R) n c S0) ->
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= snd p) n chat
    (v_pw2 (@pair R R) n c (v_map1 (Rmult g) n S0)).
Proof.
  intros n; induction n as [|n IHn]; intros g chat c S0 H.
  - destruct chat, c, S0. exact I.
  - destruct chat as [ch1 ch2], c as [c1 c2], S0 as [s1 s2].
    destruct H as [Hrec Hlast].
    split. apply IHn. exact Hrec. exact Hlast.
Qed.

Lemma rsum_absmul_map_scale : forall (n:nat) (g:R) (w S0 : vector R n),
  rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w (v_map1 (Rmult g) n S0))
  = g * rsum (v_pw2 (fun wj sj => Rabs wj * sj) n w S0).
Proof.
  intros n; induction n as [|n IHn]; intros g w S0.
  - destruct w, S0. unfold rsum. simpl. ring.
  - destruct w as [w1 w2], S0 as [s1 s2].
    rewrite v_map1_Sn, !v_pw2_Sn, !rsum_Sn, IHn. ring.
Qed.

(* LeNet-5 conv1: 5x5 kernel, 1 input channel -> dot products of length 25. *)
Theorem lenet5_conv1_error : forall (w x : vector R (5*5*1)%nat),
  Rabs (dot_rnd w x - dot_exact w x)
  <= ((1 + u) ^ 26%nat - 1) * v_abs_sum (v_pw2 Rmult (5*5*1)%nat w x).
Proof. intros. apply dot_rnd_error. Qed.

(* LeNet-5 fc1: dot products of length 400. *)
Theorem lenet5_fc1_error : forall (w x : vector R 400%nat),
  Rabs (dot_rnd w x - dot_exact w x)
  <= ((1 + u) ^ 401%nat - 1) * v_abs_sum (v_pw2 Rmult 400%nat w x).
Proof. intros. apply dot_rnd_error. Qed.

(* End-to-end: conv1 (25 products, gamma_26 per output) feeds fc1
   (400 products).  The hypothesis is the pointwise conv1 error bound
   |chat_i - c_i| <= gamma_26 * S_i, e.g. from lenet5_conv1_error. *)
Theorem lenet5_conv_fc_end_to_end : forall (w2 c chat S0 : vector R 400%nat),
  v_all (fun s => 0 <= s) 400%nat S0 ->
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= ((1 + u) ^ 26%nat - 1) * snd p)
    400%nat chat (v_pw2 (@pair R R) 400%nat c S0) ->
  Rabs (dot_rnd w2 chat - dot_exact w2 c)
  <= ((1 + u) ^ 401%nat - 1)
       * (v_abs_sum (v_pw2 Rmult 400%nat w2 c)
          + ((1 + u) ^ 26%nat - 1)
              * rsum (v_pw2 (fun wj sj => Rabs wj * sj) 400%nat w2 S0))
     + ((1 + u) ^ 26%nat - 1)
         * rsum (v_pw2 (fun wj sj => Rabs wj * sj) 400%nat w2 S0).
Proof.
  intros w2 c chat S0 HS Hconv.
  set (g := (1 + u) ^ 26%nat - 1) in *.
  pose proof (two_layer_error 400%nat w2 c chat (v_map1 (Rmult g) 400%nat S0)
                (v_pw_rel_scale 400%nat g chat c S0 Hconv)) as H2.
  rewrite rsum_absmul_map_scale in H2.
  exact H2.
Qed.

End RoundingModel.

(* -------------------------------------------------------------------------- *)
(* TF32 instantiation: u = 2^-11 (10-bit mantissa)                            *)
(* -------------------------------------------------------------------------- *)

Definition u_TF32 : R := / 2048.

Lemma u_TF32_nonneg : 0 <= u_TF32.
Proof. unfold u_TF32. apply Rlt_le. apply Rinv_0_lt_compat. lra. Qed.

(* Example: the TF32 LeNet-5 conv1 bound, for any rounding operator that
   satisfies the standard model at u_TF32. *)
Example tf32_lenet5_conv1_error : forall (rnd : R -> R),
  (forall x:R, Rabs (rnd x - x) <= u_TF32 * Rabs x) ->
  forall (w x : vector R (5*5*1)%nat),
    Rabs (dot_rnd rnd w x - dot_exact w x)
    <= ((1 + u_TF32) ^ 26%nat - 1) * v_abs_sum (v_pw2 Rmult (5*5*1)%nat w x).
Proof.
  intros rnd0 Hrnd w x.
  apply (dot_rnd_error u_TF32 u_TF32_nonneg rnd0 Hrnd).
Qed.

(* Axiom audit: everything below must report "Closed under the global
   context" (the section variables u, rnd are discharged as universal
   premises, not axioms). *)
Print Assumptions rsum_rnd_error.
Print Assumptions dot_rnd_error.
Print Assumptions lenet5_conv_fc_end_to_end.
