(* ========================================================================= *)
(* Opt_QuantError.v                                                          *)
(*                                                                           *)
(* int8 quantization track: absolute-error bounds for uniform affine         *)
(* quantization with int32-exact accumulation.                               *)
(*                                                                           *)
(* Relation to Opt_ApproxError.v (the TF32/FP16 track):                      *)
(*   - TF32 rounding satisfies a RELATIVE standard model |rnd x - x| <=      *)
(*     u*|x|, which drives the multiplicative gamma_n = (1+u)^n - 1 bounds   *)
(*     for rounded accumulation.                                             *)
(*   - int8 quantization Q(x) = scale * clamp(round(x/scale)) satisfies an   *)
(*     ABSOLUTE model |Q(x) - x| <= scale/2 (in range).  The two models are  *)
(*     not instances of each other: the absolute bound is valid only under   *)
(*     an in-range (no-clamp) hypothesis, but it does not degrade near zero  *)
(*     (cancellation-immune), whereas a relative model needs |x| bounded     *)
(*     below (see quant_err_to_rel for the exact conversion).                *)
(*   - KEY STRUCTURAL DIFFERENCE: in the int8 pipeline (int8 inputs, int32   *)
(*     accumulator) the accumulation is EXACT — integer arithmetic in R has  *)
(*     no rounding.  Hence there is NO gamma_n factor at all: the dot-       *)
(*     product error comes solely from (i) input/weight quantization and     *)
(*     (ii) output requantization, and grows LINEARLY in the reduction       *)
(*     length n (through the integer abs-sums), not like (1+u)^n - 1.        *)
(*     Theorem dot_int8_eq_deq states the exactness formally: the int8       *)
(*     pipeline computes exactly the dot product of the dequantized vectors. *)
(*                                                                           *)
(* Semantics modeled (per-tensor symmetric affine quantization, zero point   *)
(* 0, clamp to [qmin, qmax], e.g. int8: qmin = -128, qmax = 127):            *)
(*   quant_r lo hi s x = s * clamp lo hi (round (x / s))                     *)
(* i.e. quantize-and-dequantize fused into one R -> R map; the integer       *)
(* levels themselves need no integrality assumption for the error bounds.    *)
(* [round] is abstract (section variable) with the round-to-nearest property *)
(* |round t - t| <= 1/2, mirroring the abstract [rnd] of Opt_ApproxError.v.  *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   1. clamp and the fused quantizer quant_r: in-range error s/2, general   *)
(*      error with a clamp-distance term, output range, absolute->relative   *)
(*      conversion, and a vectorized quantization-error relation.            *)
(*   2. int8 dot product with int32-exact accumulation:                      *)
(*        |dot_int8 - dot_exact|                                             *)
(*          <= (sw*sx/2) * (Qx + Qw) + INR n * (sw*sx/4)                     *)
(*      where Qx, Qw bound the INTEGER abs-sums of the quantized levels      *)
(*      (corollary dot_int8_error_int8: <= sw*sx*INR n * 509/4 for the       *)
(*      worst-case int8 levels |q| <= 127).  No gamma_n — accumulation is    *)
(*      exact; the only further error is output requantization (+sy/2,       *)
(*      dot_int8_requant_error).                                             *)
(*   3. LeNet-5 per-layer and end-to-end chain (absolute version of          *)
(*      Opt_ApproxError_Apply.v): per-stage errors                           *)
(*        d_{k+1} = sy_k/2 + (sw_k/2)*(Sb_k + n_k * d_k) + Wb_k * d_k        *)
(*      composed over conv1(25) -> conv2(150) -> fc1(400) -> fc2(120) ->     *)
(*      fc3(84), with the same pool/ReLU bound-preservation hypotheses       *)
(*      (discharged by the Lipschitz-1 lemmas of Opt_ApproxError_Apply.v).   *)
(*   4. TF32 comparison: comments + quant_err_to_rel.                        *)
(*                                                                           *)
(* No Admitted, no Axiom: [round] is discharged as a universal premise.      *)
(* Print Assumptions reports only the two standard classical axioms already  *)
(* present in Opt_ApproxError.v (ClassicalDedekindReals.sig_forall_dec and   *)
(* functional_extensionality_dep via Proof_CodeGen.v).                       *)
(* ========================================================================= *)

Require Import Reals Lra Psatz Arith.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.Opt_ApproxError.
Require Import Ionia.Opt_ApproxError_Apply.

Open Scope R_scope.

Section QuantRounding.

(* Abstract round-to-nearest on R (any tie-breaking satisfying the bound). *)
Variable round : R -> R.
Hypothesis round_err : forall t:R, Rabs (round t - t) <= / 2.

(* -------------------------------------------------------------------------- *)
(* 1. clamp and the fused quantizer                                          *)
(* -------------------------------------------------------------------------- *)

Definition clamp (lo hi x : R) : R := Rmin hi (Rmax lo x).

Lemma le_Rmax_l : forall a b : R, a <= Rmax a b.
Proof. intros; unfold Rmax; destruct (Rle_dec a b); lra. Qed.

Lemma le_Rmax_r : forall a b : R, b <= Rmax a b.
Proof. intros; unfold Rmax; destruct (Rle_dec a b); lra. Qed.

Lemma min2_lipschitz : forall a b c d : R,
  Rabs (Rmin a b - Rmin c d) <= Rabs (a - c) + Rabs (b - d).
Proof.
  intros a b c d. unfold Rmin, Rabs.
  destruct (Rle_dec a b); destruct (Rle_dec c d);
  repeat match goal with |- context [Rcase_abs ?e] => destruct (Rcase_abs e) end;
  lra.
Qed.

Lemma clamp_lipschitz : forall lo hi a b,
  lo <= hi -> Rabs (clamp lo hi a - clamp lo hi b) <= Rabs (a - b).
Proof.
  intros lo hi a b Hlh. unfold clamp.
  pose proof (max2_lipschitz lo a lo b) as H1.
  pose proof (min2_lipschitz hi (Rmax lo a) hi (Rmax lo b)) as H2.
  replace (hi - hi) with 0 in H2 by ring.
  replace (lo - lo) with 0 in H1 by ring.
  rewrite Rabs_R0 in H1, H2.
  lra.
Qed.

Lemma clamp_in_range : forall lo hi x,
  lo <= hi -> lo <= x -> x <= hi -> clamp lo hi x = x.
Proof.
  intros lo hi x Hlh Hlo Hhi. unfold clamp, Rmin, Rmax.
  destruct (Rle_dec lo x) as [H1|H1].
  - destruct (Rle_dec hi x) as [H2|H2]; lra.
  - destruct (Rle_dec hi lo) as [H3|H3]; lra.
Qed.

Lemma clamp_bounds : forall lo hi x,
  lo <= hi -> lo <= clamp lo hi x <= hi.
Proof.
  intros lo hi x Hlh. unfold clamp, Rmin, Rmax.
  destruct (Rle_dec lo x) as [H1|H1].
  - destruct (Rle_dec hi x) as [H2|H2]; lra.
  - destruct (Rle_dec hi lo) as [H3|H3]; lra.
Qed.

(* Clamp edge cases: the error of clamp is the distance to [lo, hi]. *)
Lemma clamp_dist : forall lo hi x,
  lo <= hi ->
  Rabs (clamp lo hi x - x) <= Rmax 0 (Rmax (lo - x) (x - hi)).
Proof.
  intros lo hi x Hlh.
  pose proof (le_Rmax_l 0 (Rmax (lo - x) (x - hi))) as H0.
  pose proof (le_Rmax_r 0 (Rmax (lo - x) (x - hi))) as H0r.
  pose proof (le_Rmax_l (lo - x) (x - hi)) as H1.
  pose proof (le_Rmax_r (lo - x) (x - hi)) as H2.
  unfold clamp.
  destruct (Rle_dec lo x) as [Hlo|Hlo].
  - assert (Hmax : Rmax lo x = x) by (unfold Rmax; destruct (Rle_dec lo x); lra).
    rewrite Hmax. clear Hmax.
    destruct (Rle_dec hi x) as [Hhi|Hhi].
    + assert (Hmin : Rmin hi x = hi) by (unfold Rmin; destruct (Rle_dec hi x); lra).
      rewrite Hmin.
      assert (Hxh : Rabs (hi - x) = x - hi) by (rewrite Rabs_left1; lra).
      rewrite Hxh. lra.
    + assert (Hmin : Rmin hi x = x) by (unfold Rmin; destruct (Rle_dec hi x); lra).
      rewrite Hmin. replace (x - x) with 0 by ring. rewrite Rabs_R0. exact H0.
  - assert (Hmax : Rmax lo x = lo) by (unfold Rmax; destruct (Rle_dec lo x); lra).
    rewrite Hmax. clear Hmax.
    assert (Hmin : Rmin hi lo = lo) by (unfold Rmin; destruct (Rle_dec hi lo); lra).
    rewrite Hmin.
    assert (Hxl : Rabs (lo - x) = lo - x) by (apply Rabs_pos_eq; lra).
    rewrite Hxl. lra.
Qed.

(* Fused quantize-dequantize: quant_r lo hi s x = s * clamp lo hi (round(x/s)).
   (dequant (quant x): dequant s q = s * q is inlined; the stored integer is
   clamp lo hi (round (x/s)).) *)
Definition quant_r (lo hi s x : R) : R := s * clamp lo hi (round (x / s)).

(* In-range: the quantization error is at most half a quantum. *)
Lemma quant_r_err_in_range : forall lo hi s x,
  0 < s -> lo <= hi -> s * lo <= x <= s * hi ->
  Rabs (quant_r lo hi s x - x) <= s / 2.
Proof.
  intros lo hi s x Hs Hlh Hrange. destruct Hrange as [Hlo Hhi].
  assert (Hsinv : 0 < / s) by (apply Rinv_0_lt_compat; exact Hs).
  assert (Hsinv' : 0 <= / s) by (apply Rlt_le; exact Hsinv).
  assert (He1 : s * lo * / s = lo) by (field; lra).
  assert (He2 : s * hi * / s = hi) by (field; lra).
  pose proof (Rmult_le_compat_r (/s) (s*lo) x Hsinv' Hlo) as H1. rewrite He1 in H1.
  pose proof (Rmult_le_compat_r (/s) x (s*hi) Hsinv' Hhi) as H2. rewrite He2 in H2.
  assert (Hx : x = s * (x / s)) by (field; lra).
  unfold quant_r. rewrite Hx at 2.
  replace (s * clamp lo hi (round (x / s)) - s * (x / s))
    with (s * (clamp lo hi (round (x / s)) - x / s)) by ring.
  rewrite Rabs_mult. rewrite (Rabs_pos_eq s) by (apply Rlt_le; exact Hs).
  assert (Hb2 : Rabs (clamp lo hi (round (x / s)) - x / s) <= / 2).
  { pose proof (clamp_in_range lo hi (x / s) Hlh H1 H2) as Hc.
    pose proof (clamp_lipschitz lo hi (round (x / s)) (x / s) Hlh) as Hcl.
    rewrite Hc in Hcl.
    pose proof (round_err (x / s)) as Hr.
    lra. }
  transitivity (s * / 2).
  - apply Rmult_le_compat_l; lra.
  - apply Req_le. reflexivity.
Qed.

(* General form with clamping: half a quantum plus the overshoot distance. *)
Lemma quant_r_err_general : forall lo hi s x,
  0 < s -> lo <= hi ->
  Rabs (quant_r lo hi s x - x)
  <= s * (/ 2 + Rmax 0 (Rmax (lo - x / s) (x / s - hi))).
Proof.
  intros lo hi s x Hs Hlh.
  pose proof (round_err (x / s)) as Hr.
  pose proof (clamp_lipschitz lo hi (round (x / s)) (x / s) Hlh) as Hcl.
  pose proof (clamp_dist lo hi (x / s) Hlh) as Hcd.
  assert (Htri : Rabs (clamp lo hi (round (x / s)) - x / s)
    <= Rabs (clamp lo hi (round (x / s)) - clamp lo hi (x / s))
       + Rabs (clamp lo hi (x / s) - x / s)).
  { replace (clamp lo hi (round (x / s)) - x / s)
      with ((clamp lo hi (round (x / s)) - clamp lo hi (x / s))
            + (clamp lo hi (x / s) - x / s)) by ring.
    apply Rabs_triang. }
  assert (Hb : Rabs (clamp lo hi (round (x / s)) - x / s)
        <= / 2 + Rmax 0 (Rmax (lo - x / s) (x / s - hi))) by lra.
  unfold quant_r.
  assert (Hx : x = s * (x / s)) by (field; lra).
  rewrite Hx at 2.
  replace (s * clamp lo hi (round (x / s)) - s * (x / s))
    with (s * (clamp lo hi (round (x / s)) - x / s)) by ring.
  rewrite Rabs_mult. rewrite (Rabs_pos_eq s) by (apply Rlt_le; exact Hs).
  apply Rmult_le_compat_l; lra.
Qed.

(* The quantized value always lands in [s*lo, s*hi]. *)
Lemma quant_r_bounds : forall lo hi s x,
  0 < s -> lo <= hi -> s * lo <= quant_r lo hi s x <= s * hi.
Proof.
  intros lo hi s x Hs Hlh. unfold quant_r.
  pose proof (clamp_bounds lo hi (round (x / s)) Hlh) as [H1 H2].
  split; apply Rmult_le_compat_l; lra.
Qed.

(* Absolute -> relative conversion: with a lower bound x0 <= |x| the int8
   model instantiates a relative standard model with u = s / (2 * x0).
   This is the precise sense in which int8 quantization is "relative-error
   capable" only away from zero, unlike TF32's u = 2^-11 everywhere. *)
Lemma quant_err_to_rel : forall lo hi s x x0,
  0 < s -> lo <= hi -> s * lo <= x <= s * hi ->
  0 < x0 -> x0 <= Rabs x ->
  Rabs (quant_r lo hi s x - x) <= (s / (2 * x0)) * Rabs x.
Proof.
  intros lo hi s x x0 Hs Hlh Hrange Hx0 Hx0le.
  pose proof (quant_r_err_in_range lo hi s x Hs Hlh Hrange) as Hq.
  assert (Hc : 0 <= s / (2 * x0)).
  { unfold Rdiv. apply Rmult_le_pos. lra. apply Rlt_le. apply Rinv_0_lt_compat. lra. }
  assert (He : s / (2 * x0) * x0 = s / 2) by (field; lra).
  eapply Rle_trans. exact Hq.
  rewrite <- He. apply Rmult_le_compat_l; assumption.
Qed.

(* Vectorized form: componentwise quantization of an in-range vector
   satisfies the half-quantum pointwise relation used by the dot bounds. *)
Lemma quant_vec_err : forall (n:nat) (w : vector R n) lo hi s,
  0 < s -> lo <= hi ->
  v_all (fun wi => s * lo <= wi <= s * hi) n w ->
  v_pw_rel (fun q wi => Rabs (s * q - wi) <= s / 2) n
    (v_map1 (fun wi => clamp lo hi (round (wi / s))) n w) w.
Proof.
  intros n; induction n as [|n IHn]; intros w lo hi s Hs Hlh Hall.
  - destruct w. exact I.
  - destruct w as [w1 w2]. destruct Hall as [Hrec Hlast].
    rewrite v_map1_Sn. split.
    + apply IHn; auto.
    + exact (quant_r_err_in_range lo hi s w2 Hs Hlh Hlast).
Qed.

(* -------------------------------------------------------------------------- *)
(* 2. int8 dot product with int32-exact accumulation                         *)
(* -------------------------------------------------------------------------- *)

(* The int8 pipeline: integer levels qw, qx (int8), exact int32 accumulation
   modeled in R, then dequantization by the product scale sw*sx.
   dot_int8 sw sx qw qx = sw*sx * Sum_i qw_i*qx_i. *)
Definition dot_int8 (sw sx : R) {n:nat} (qw qx : vector R n) : R :=
  sw * sx * rsum (v_pw2 Rmult n qw qx).

Lemma dot_int8_Sn : forall (n:nat) (qw qx : vector R n) (q2 x2 sw sx : R),
  dot_int8 sw sx ((qw, q2) : vector R (S n)) ((qx, x2) : vector R (S n))
  = (sw * q2) * (sx * x2) + dot_int8 sw sx qw qx.
Proof.
  intros. unfold dot_int8. rewrite v_pw2_Sn, rsum_Sn. ring.
Qed.

(* Exactness of int accumulation: the int8 pipeline computes exactly the
   dot product of the dequantized vectors.  This is the formal content of
   "int8 + int32 accumulate has no accumulation rounding" — contrast with
   dot_rnd of Opt_ApproxError.v, where every accumulation step is rounded
   and the gamma_n factor emerges. *)
Theorem dot_int8_eq_deq : forall (n:nat) (qw qx : vector R n) (sw sx : R),
  dot_int8 sw sx qw qx
  = dot_exact (v_map1 (Rmult sw) n qw) (v_map1 (Rmult sx) n qx).
Proof.
  intros n; induction n as [|n IHn]; intros qw qx sw sx.
  - destruct qw, qx. unfold dot_int8, dot_exact, rsum. simpl. ring.
  - destruct qw as [qw1 q2], qx as [qx1 x2].
    rewrite dot_int8_Sn, (IHn qw1 qx1 sw sx).
    unfold dot_exact. rewrite !v_map1_Sn, !v_pw2_Sn, !rsum_Sn. ring.
Qed.

(* Core error bound: only the input quantization errors matter.
   With |sw*qw_i - w_i| <= dw and |sx*qx_i - x_i| <= dx pointwise,
     |dot_int8 - dot_exact w x|
       <= dw * (sx * Sum|qx_i|) + dx * Sum|w_i|.                       *)
Theorem dot_int8_error : forall (n:nat) (w x qw qx : vector R n)
    (sw sx dw dx : R),
  0 <= dw -> 0 <= dx ->
  v_pw_rel (fun q wi => Rabs (sw * q - wi) <= dw) n qw w ->
  v_pw_rel (fun q xi => Rabs (sx * q - xi) <= dx) n qx x ->
  Rabs (dot_int8 sw sx qw qx - dot_exact w x)
  <= dw * v_abs_sum (v_map1 (Rmult sx) n qx) + dx * v_abs_sum w.
Proof.
  intros n; induction n as [|n IHn]; intros w x qw qx sw sx dw dx Hdw Hdx Hw Hx.
  - destruct w, x, qw, qx. unfold dot_int8, dot_exact, v_abs_sum, rsum. simpl.
    replace (sw * sx * 0 - 0) with 0 by ring. rewrite Rabs_R0. nra.
  - destruct w as [w1 w2], x as [x1 x2], qw as [qw1 q2], qx as [qx1 qx2].
    destruct Hw as [Hwrec Hwlast], Hx as [Hxrec Hxlast].
    rewrite dot_int8_Sn. unfold dot_exact in *.
    rewrite v_pw2_Sn, rsum_Sn, v_map1_Sn, !v_abs_sum_Sn.
    pose proof (IHn w1 x1 qw1 qx1 sw sx dw dx Hdw Hdx Hwrec Hxrec) as IH.
    assert (Hloc : Rabs ((sw * q2) * (sx * qx2) - w2 * x2)
            <= dw * Rabs (sx * qx2) + dx * Rabs w2).
    { replace ((sw * q2) * (sx * qx2) - w2 * x2)
        with ((sw * q2 - w2) * (sx * qx2) + w2 * (sx * qx2 - x2)) by ring.
      eapply Rle_trans. apply Rabs_triang.
      assert (K1 : Rabs ((sw * q2 - w2) * (sx * qx2)) <= dw * Rabs (sx * qx2)).
      { rewrite Rabs_mult. apply Rmult_le_compat_r. apply Rabs_pos. exact Hwlast. }
      assert (K2 : Rabs (w2 * (sx * qx2 - x2)) <= Rabs w2 * dx).
      { rewrite Rabs_mult. apply Rmult_le_compat_l. apply Rabs_pos. exact Hxlast. }
      lra. }
    replace ((sw * q2) * (sx * qx2) + dot_int8 sw sx qw1 qx1
             - (w2 * x2 + rsum (v_pw2 Rmult n w1 x1)))
      with (((sw * q2) * (sx * qx2) - w2 * x2)
            + (dot_int8 sw sx qw1 qx1 - rsum (v_pw2 Rmult n w1 x1))) by ring.
    eapply Rle_trans. apply Rabs_triang. lra.
Qed.

(* Absolute-value sum commutes with nonnegative scaling. *)
Lemma v_abs_sum_map_scale : forall (n:nat) (s : R) (q : vector R n),
  0 <= s -> v_abs_sum (v_map1 (Rmult s) n q) = s * v_abs_sum q.
Proof.
  intros n; induction n as [|n IHn]; intros s q Hs.
  - destruct q. unfold v_abs_sum, rsum. simpl. ring.
  - destruct q as [q1 q2]. rewrite v_map1_Sn, !v_abs_sum_Sn, IHn by exact Hs.
    rewrite Rabs_mult, (Rabs_pos_eq s) by exact Hs. ring.
Qed.

(* The exact weights inherit an abs-sum bound from their quantized levels. *)
Lemma v_abs_sum_perturb : forall (n:nat) (qw w : vector R n) (sw dw : R),
  0 <= sw -> 0 <= dw ->
  v_pw_rel (fun q wi => Rabs (sw * q - wi) <= dw) n qw w ->
  v_abs_sum w <= sw * v_abs_sum qw + INR n * dw.
Proof.
  intros n; induction n as [|n IHn]; intros qw w sw dw Hsw Hdw H.
  - destruct qw, w. unfold v_abs_sum, rsum. simpl. lra.
  - destruct qw as [qw1 q2], w as [w1 w2]. destruct H as [Hrec Hlast].
    simpl in Hlast.
    rewrite !v_abs_sum_Sn, S_INR.
    pose proof (IHn qw1 w1 sw dw Hsw Hdw Hrec) as IH.
    assert (Hw2 : Rabs w2 <= sw * Rabs q2 + dw).
    { assert (Ht : Rabs w2 <= Rabs (sw * q2) + Rabs (sw * q2 - w2)).
      { replace w2 with (sw * q2 - (sw * q2 - w2)) at 1 by ring.
        eapply Rle_trans. apply Rabs_triang. rewrite Rabs_Ropp. lra. }
      rewrite Rabs_mult, (Rabs_pos_eq sw) in Ht by exact Hsw.
      lra. }
    lra.
Qed.

(* Componentwise |q_i| <= B gives the integer abs-sum bound. *)
Lemma v_abs_sum_le_INR : forall (n:nat) (B : R) (q : vector R n),
  0 <= B ->
  v_all (fun qi => Rabs qi <= B) n q -> v_abs_sum q <= INR n * B.
Proof.
  intros n; induction n as [|n IHn]; intros B q HB H.
  - destruct q. unfold v_abs_sum, rsum. simpl. lra.
  - destruct q as [q1 q2]. destruct H as [Hrec Hlast]. simpl in Hlast.
    rewrite v_abs_sum_Sn, S_INR.
    pose proof (IHn B q1 HB Hrec) as IH. lra.
Qed.

(* Headline int8 bound, integer-abs-sum form: with half-quantum input
   quantization (dw = sw/2, dx = sx/2, e.g. from quant_r_err_in_range) and
   integer abs-sum bounds Qx, Qw,
     |dot_int8 - dot_exact|
       <= (sw*sx/2) * (Qx + Qw) + INR n * (sw*sx/4).
   The error is LINEAR in n (through Qx, Qw and the explicit INR n term);
   there is no gamma_n = (1+u)^n - 1 because accumulation is exact. *)
Theorem dot_int8_error_intsum : forall (n:nat) (w x qw qx : vector R n)
    (sw sx Qx Qw : R),
  0 <= sw -> 0 <= sx ->
  v_pw_rel (fun q wi => Rabs (sw * q - wi) <= sw / 2) n qw w ->
  v_pw_rel (fun q xi => Rabs (sx * q - xi) <= sx / 2) n qx x ->
  v_abs_sum qx <= Qx -> v_abs_sum qw <= Qw ->
  Rabs (dot_int8 sw sx qw qx - dot_exact w x)
  <= (sw * sx / 2) * (Qx + Qw) + INR n * (sw * sx / 4).
Proof.
  intros n w x qw qx sw sx Qx Qw Hsw Hsx Hw Hx HQx HQw.
  assert (Hdw : 0 <= sw / 2) by lra.
  assert (Hdx : 0 <= sx / 2) by lra.
  pose proof (dot_int8_error n w x qw qx sw sx (sw/2) (sx/2) Hdw Hdx Hw Hx) as H0.
  rewrite (v_abs_sum_map_scale n sx qx Hsx) in H0.
  pose proof (v_abs_sum_perturb n qw w sw (sw/2) Hsw Hdw Hw) as Kw.
  assert (Kw2 : v_abs_sum w <= sw * Qw + INR n * (sw / 2)).
  { assert (K : sw * v_abs_sum qw <= sw * Qw)
      by (apply Rmult_le_compat_l; auto). lra. }
  assert (Kx2 : sx * v_abs_sum qx <= sx * Qx)
    by (apply Rmult_le_compat_l; auto).
  assert (Hm1 : sw / 2 * (sx * v_abs_sum qx) <= sw / 2 * (sx * Qx)).
  { apply Rmult_le_compat_l; auto. }
  assert (Hm2 : sx / 2 * v_abs_sum w <= sx / 2 * (sw * Qw + INR n * (sw / 2))).
  { apply Rmult_le_compat_l; auto. }
  nra.
Qed.

(* Worst-case int8 instance: levels in [-127, 127] give Qx, Qw <= 127*n,
   hence |dot_int8 - dot_exact| <= sw*sx*n*509/4  (= sw*sx*n*127.25).
   Linear in n; compare TF32's gamma_{n+1} = (1+2^-11)^(n+1) - 1 which is
   exponential in n (n*u to first order). *)
Corollary dot_int8_error_int8 : forall (n:nat) (w x qw qx : vector R n)
    (sw sx : R),
  0 <= sw -> 0 <= sx ->
  v_pw_rel (fun q wi => Rabs (sw * q - wi) <= sw / 2) n qw w ->
  v_pw_rel (fun q xi => Rabs (sx * q - xi) <= sx / 2) n qx x ->
  v_all (fun q => Rabs q <= 127) n qw ->
  v_all (fun q => Rabs q <= 127) n qx ->
  Rabs (dot_int8 sw sx qw qx - dot_exact w x)
  <= sw * sx * INR n * (509 / 4).
Proof.
  intros n w x qw qx sw sx Hsw Hsx Hw Hx Hallw Hallx.
  assert (Bw : v_abs_sum qw <= INR n * 127)
    by (apply v_abs_sum_le_INR; [lra | exact Hallw]).
  assert (Bx : v_abs_sum qx <= INR n * 127)
    by (apply v_abs_sum_le_INR; [lra | exact Hallx]).
  pose proof (dot_int8_error_intsum n w x qw qx sw sx
                (INR n * 127) (INR n * 127) Hsw Hsx Hw Hx Bx Bw) as H.
  pose proof (pos_INR n) as Hn.
  nra.
Qed.

(* Full layer-local pipeline: int8 dot + output requantization.
   The output requantization adds exactly sy/2 (in range); the int32
   accumulator itself contributes nothing. *)
Theorem dot_int8_requant_error : forall (n:nat) (w x qw qx : vector R n)
    (sw sx sy qmin qmax Qx Qw : R),
  0 < sy -> qmin <= qmax -> 0 <= sw -> 0 <= sx ->
  v_pw_rel (fun q wi => Rabs (sw * q - wi) <= sw / 2) n qw w ->
  v_pw_rel (fun q xi => Rabs (sx * q - xi) <= sx / 2) n qx x ->
  v_abs_sum qx <= Qx -> v_abs_sum qw <= Qw ->
  sy * qmin <= dot_int8 sw sx qw qx <= sy * qmax ->
  Rabs (quant_r qmin qmax sy (dot_int8 sw sx qw qx) - dot_exact w x)
  <= sy / 2 + ((sw * sx / 2) * (Qx + Qw) + INR n * (sw * sx / 4)).
Proof.
  intros n w x qw qx sw sx sy qmin qmax Qx Qw Hsy Hqq Hsw Hsx Hw Hx HQx HQw Hrange.
  pose proof (dot_int8_error_intsum n w x qw qx sw sx Qx Qw Hsw Hsx Hw Hx HQx HQw)
    as Hd.
  pose proof (quant_r_err_in_range qmin qmax sy (dot_int8 sw sx qw qx)
                Hsy Hqq Hrange) as Hq.
  replace (quant_r qmin qmax sy (dot_int8 sw sx qw qx) - dot_exact w x)
    with ((quant_r qmin qmax sy (dot_int8 sw sx qw qx) - dot_int8 sw sx qw qx)
          + (dot_int8 sw sx qw qx - dot_exact w x)) by ring.
  eapply Rle_trans. apply Rabs_triang. lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. LeNet-5 chain, absolute-error version                                   *)
(* -------------------------------------------------------------------------- *)

(* Per-layer scalar error, absolute form (the int8 analogue of [layer_err]
   in Opt_ApproxError_Apply.v):
     q_layer_err sw sy n Wb Sb d
       = sy/2 + (sw/2)*(Sb + n*d) + Wb*d
   where sy/2 = output requantization, sw/2 = weight quantization acting on
   the perturbed activation abs-sum (<= Sb + n*d), and Wb*d = propagation of
   the incoming pointwise activation error d through the exact weights.
   Note: no gamma factor — exact int32 accumulation. *)
Definition q_layer_err (sw sy : R) (n:nat) (Wb Sb d : R) : R :=
  sy / 2 + (sw / 2) * (Sb + INR n * d) + Wb * d.

Lemma q_layer_err_nonneg : forall (sw sy : R) (n:nat) (Wb Sb d : R),
  0 <= sw -> 0 <= sy -> 0 <= Wb -> 0 <= Sb -> 0 <= d ->
  0 <= q_layer_err sw sy n Wb Sb d.
Proof.
  intros sw sy n Wb Sb d Hsw Hsy HWb HSb Hd. unfold q_layer_err.
  pose proof (pos_INR n) as Hn.
  assert (H1 : 0 <= INR n * d) by (apply Rmult_le_pos; auto).
  assert (H2 : 0 <= Sb + INR n * d) by lra.
  assert (H3 : 0 <= sw / 2 * (Sb + INR n * d)).
  { apply Rmult_le_pos; lra. }
  assert (H4 : 0 <= Wb * d) by (apply Rmult_le_pos; auto).
  lra.
Qed.

(* Weight perturbation of the exact dot product. *)
Lemma dot_weight_perturb : forall (n:nat) (wq w x : vector R n) (dw : R),
  0 <= dw ->
  v_pw_rel (fun a b => Rabs (a - b) <= dw) n wq w ->
  Rabs (dot_exact wq x - dot_exact w x) <= dw * v_abs_sum x.
Proof.
  intros n; induction n as [|n IHn]; intros wq w x dw Hdw H.
  - destruct wq, w, x. unfold dot_exact, rsum, v_abs_sum. simpl.
    replace (rsum (tt : vector R 0)) with 0 by reflexivity.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. nra.
  - destruct wq as [wq1 wq2], w as [w1 w2], x as [x1 x2].
    destruct H as [Hrec Hlast].
    unfold dot_exact in *. rewrite !v_pw2_Sn, !rsum_Sn, v_abs_sum_Sn.
    pose proof (IHn wq1 w1 x1 dw Hdw Hrec) as IH.
    replace (wq2 * x2 + rsum (v_pw2 Rmult n wq1 x1)
             - (w2 * x2 + rsum (v_pw2 Rmult n w1 x1)))
      with ((wq2 - w2) * x2
            + (rsum (v_pw2 Rmult n wq1 x1) - rsum (v_pw2 Rmult n w1 x1))) by ring.
    eapply Rle_trans. apply Rabs_triang. rewrite Rabs_mult.
    assert (K : Rabs (wq2 - w2) * Rabs x2 <= dw * Rabs x2).
    { apply Rmult_le_compat_r. apply Rabs_pos. exact Hlast. }
    lra.
Qed.

(* Uniform pointwise perturbation inflates the abs-sum by at most n*d. *)
Lemma v_abs_sum_pw_ub : forall (n:nat) (d : R) (a b : vector R n),
  0 <= d -> v_pw_ub d n a b ->
  v_abs_sum a <= v_abs_sum b + INR n * d.
Proof.
  intros n; induction n as [|n IHn]; intros d a b Hd Hub.
  - destruct a, b. unfold v_abs_sum, rsum. simpl. lra.
  - destruct a as [a1 a2], b as [b1 b2]. destruct Hub as [Hrec Hlast].
    simpl in Hlast.
    rewrite !v_abs_sum_Sn, S_INR.
    pose proof (IHn d a1 b1 Hd Hrec) as IH.
    assert (Ha : Rabs a2 <= Rabs b2 + d).
    { assert (Ht : Rabs a2 <= Rabs (a2 - b2) + Rabs b2).
      { replace a2 with ((a2 - b2) + b2) at 1 by ring. apply Rabs_triang. }
      lra. }
    lra.
Qed.

(* Scalar layer core: exact dot product over dequantized weights and
   perturbed activations. *)
Lemma qdot_error_deq : forall (n:nat) (w wq x xq : vector R n)
    (dw d Sb Wb : R),
  0 <= dw -> 0 <= d -> 0 <= Sb -> 0 <= Wb ->
  v_pw_rel (fun a b => Rabs (a - b) <= dw) n wq w ->
  v_pw_ub d n xq x ->
  v_abs_sum x <= Sb -> v_abs_sum w <= Wb ->
  Rabs (dot_exact wq xq - dot_exact w x) <= dw * (Sb + INR n * d) + d * Wb.
Proof.
  intros n w wq x xq dw d Sb Wb Hdw Hd HSb HWb Hw Hub Hx Hwb.
  assert (Hsplit : Rabs (dot_exact wq xq - dot_exact w x)
          <= Rabs (dot_exact wq xq - dot_exact w xq)
             + Rabs (dot_exact w xq - dot_exact w x)).
  { replace (dot_exact wq xq - dot_exact w x)
      with ((dot_exact wq xq - dot_exact w xq)
            + (dot_exact w xq - dot_exact w x)) by ring.
    apply Rabs_triang. }
  pose proof (dot_weight_perturb n wq w xq dw Hdw Hw) as H1.
  pose proof (v_abs_sum_pw_ub n d xq x Hd Hub) as Hxq.
  assert (Hxq2 : v_abs_sum xq <= Sb + INR n * d) by lra.
  assert (H1' : dw * v_abs_sum xq <= dw * (Sb + INR n * d)).
  { apply Rmult_le_compat_l; auto. }
  pose proof (dot_exact_perturb n w x xq (v_map1 (fun _ : R => d) n x)
                (v_pw_ub_to_rel n d xq x Hub)) as H2.
  rewrite rsum_absmul_constdelta in H2.
  assert (H2' : d * v_abs_sum w <= d * Wb).
  { apply Rmult_le_compat_l; auto. }
  lra.
Qed.

(* Scalar layer with output requantization: the full per-layer bound. *)
Theorem qint_layer_scalar : forall (n:nat) (w wq x xq : vector R n)
    (qmin qmax sy sw Sb Wb d : R),
  0 < sy -> 0 <= sw -> qmin <= qmax -> 0 <= d -> 0 <= Sb -> 0 <= Wb ->
  v_pw_rel (fun a b => Rabs (a - b) <= sw / 2) n wq w ->
  v_pw_ub d n xq x ->
  v_abs_sum x <= Sb -> v_abs_sum w <= Wb ->
  sy * qmin <= dot_exact wq xq <= sy * qmax ->
  Rabs (quant_r qmin qmax sy (dot_exact wq xq) - dot_exact w x)
  <= q_layer_err sw sy n Wb Sb d.
Proof.
  intros n w wq x xq qmin qmax sy sw Sb Wb d Hsy Hsw Hqq Hd HSb HWb
         Hw Hub Hx Hwb Hrange.
  assert (Hdw : 0 <= sw / 2) by lra.
  pose proof (quant_r_err_in_range qmin qmax sy (dot_exact wq xq) Hsy Hqq Hrange)
    as Hq.
  pose proof (qdot_error_deq n w wq x xq (sw/2) d Sb Wb Hdw Hd HSb HWb
                Hw Hub Hx Hwb) as Hdq.
  unfold q_layer_err.
  replace (quant_r qmin qmax sy (dot_exact wq xq) - dot_exact w x)
    with ((quant_r qmin qmax sy (dot_exact wq xq) - dot_exact wq xq)
          + (dot_exact wq xq - dot_exact w x)) by ring.
  eapply Rle_trans. apply Rabs_triang. lra.
Qed.

(* Row relation for one linear layer: p = (stored dequantized weights,
   stored activations), q = (exact weights, exact activations).  Bundles the
   half-quantum weight quantization, the abs-sum bounds, and the no-clamp
   (in-range) condition of the int32 accumulator w.r.t. the output scale. *)
Definition qrow_rel (n:nat) (sw sy qmin qmax Wb Sb : R)
    (p q : vector R n * vector R n) : Prop :=
  v_pw_rel (fun a b => Rabs (a - b) <= sw / 2) n (fst p) (fst q) /\
  v_abs_sum (fst q) <= Wb /\
  v_abs_sum (snd q) <= Sb /\
  (sy * qmin <= dot_exact (fst p) (snd p) <= sy * qmax).

(* Whole-layer lifting: m output neurons, each an int8 dot product of
   length n plus requantization (conv: each row paired with its patch). *)
Theorem qint_lin_layer_pw_ub : forall (m n:nat)
    (W Wq X Xh : vector (vector R n) m)
    (qmin qmax sw sy Wb Sb d : R),
  0 < sy -> 0 <= sw -> qmin <= qmax -> 0 <= d -> 0 <= Sb -> 0 <= Wb ->
  v_pw_rel (qrow_rel n sw sy qmin qmax Wb Sb) m
    (v_pw2 (@pair _ _) m Wq Xh) (v_pw2 (@pair _ _) m W X) ->
  v_pw_rel (fun xh x => v_pw_ub d n xh x) m Xh X ->
  v_pw_ub (q_layer_err sw sy n Wb Sb d) m
    (v_pw2 (fun a b => quant_r qmin qmax sy (dot_exact a b)) m Wq Xh)
    (v_pw2 (fun a b => dot_exact a b) m W X).
Proof.
  intros m n; induction m as [|m IHm];
    intros W Wq X Xh qmin qmax sw sy Wb Sb d Hsy Hsw Hqq Hd HSb HWb Hrows Hin.
  - destruct W, Wq, X, Xh. exact I.
  - destruct W as [W1 w], Wq as [Wq1 wq], X as [X1 x], Xh as [Xh1 xh].
    destruct Hrows as [Hrows Hrlast], Hin as [Hin Hilast].
    rewrite !v_pw2_Sn. split.
    + apply (IHm W1 Wq1 X1 Xh1 qmin qmax sw sy Wb Sb d); auto.
    + unfold qrow_rel in Hrlast. simpl in Hrlast.
      destruct Hrlast as [Hwq [HWb' [HSb' Hrange]]].
      exact (qint_layer_scalar n w wq x xh qmin qmax sy sw Sb Wb d
               Hsy Hsw Hqq Hd HSb HWb Hwq Hilast HSb' HWb' Hrange).
Qed.

(* Per-stage accumulated errors for the LeNet-5 chain.
   d0 = sx0/2: input image quantization (in range).
   conv1: 5*5*1 = 25; conv2: 5*5*6 = 150; fc1: 400; fc2: 120; fc3: 84.
   In a per-tensor int8 chain the output scale of layer k IS the input
   scale of layer k+1, so only sy_k appears at each stage. *)
Definition qd0 (sx0 : R) : R := sx0 / 2.
Definition qd1 (sx0 sw1 sy1 Wb1 Sb1 : R) : R :=
  q_layer_err sw1 sy1 (5*5*1)%nat Wb1 Sb1 (qd0 sx0).
Definition qd2 (sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 : R) : R :=
  q_layer_err sw2 sy2 (5*5*6)%nat Wb2 Sb2 (qd1 sx0 sw1 sy1 Wb1 Sb1).
Definition qd3 (sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3 : R) : R :=
  q_layer_err sw3 sy3 400%nat Wb3 Sb3 (qd2 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2).
Definition qd4 (sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
               sw4 sy4 Wb4 Sb4 : R) : R :=
  q_layer_err sw4 sy4 120%nat Wb4 Sb4
    (qd3 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3).
Definition qd5 (sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
               sw4 sy4 Wb4 Sb4 sw5 sy5 Wb5 Sb5 : R) : R :=
  q_layer_err sw5 sy5 84%nat Wb5 Sb5
    (qd4 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3 sw4 sy4 Wb4 Sb4).

(* Chain hypotheses, bundled (absolute-error analogue of [lenet5_hyps]):
   - nonnegativity / positivity of scales and bounds, qmin <= qmax;
   - per-layer row relations (weight quantization, abs-sum bounds, int32
     accumulator within the output quantization range — the no-clamp
     condition; if clamping can occur, quant_r_err_general supplies the
     extra overshoot term instead);
   - the input quantization bound (d0 = sx0/2, from quant_vec_err) and the
     bound-preservation relations across pool1+patching, pool2+flattening
     and the ReLU stages — each discharged by maxpool2x2_lipschitz resp.
     v_pw_ub_relu of Opt_ApproxError_Apply.v (pooling, patch extraction and
     ReLU never increase a uniform pointwise bound). *)
Definition qint_lenet5_hyps
    (m1 m2 m3 m4 m5 : nat)
    (W1 Wq1 : vector (vector R (5*5*1)%nat) m1)
    (X1 X1h : vector (vector R (5*5*1)%nat) m1)
    (W2 Wq2 : vector (vector R (5*5*6)%nat) m2)
    (X2 X2h : vector (vector R (5*5*6)%nat) m2)
    (W3 Wq3 : vector (vector R 400%nat) m3)
    (X3 X3h : vector (vector R 400%nat) m3)
    (W4 Wq4 : vector (vector R 120%nat) m4)
    (X4 X4h : vector (vector R 120%nat) m4)
    (W5 Wq5 : vector (vector R 84%nat) m5)
    (X5 X5h : vector (vector R 84%nat) m5)
    (sx0 sw1 sy1 sw2 sy2 sw3 sy3 sw4 sy4 sw5 sy5 qmin qmax : R)
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm : R) : Prop :=
  (0 <= sx0 /\ 0 <= sw1 /\ 0 <= sw2 /\ 0 <= sw3 /\ 0 <= sw4 /\ 0 <= sw5 /\
   0 < sy1 /\ 0 < sy2 /\ 0 < sy3 /\ 0 < sy4 /\ 0 < sy5 /\
   qmin <= qmax /\
   0 <= Wb1 /\ 0 <= Wb2 /\ 0 <= Wb3 /\ 0 <= Wb4 /\ 0 <= Wb5 /\
   0 <= Sb1 /\ 0 <= Sb2 /\ 0 <= Sb3 /\ 0 <= Sb4 /\ 0 <= Sb5 /\ 0 <= Lsm) /\
  (v_pw_rel (qrow_rel (5*5*1)%nat sw1 sy1 qmin qmax Wb1 Sb1) m1
     (v_pw2 (@pair _ _) m1 Wq1 X1h) (v_pw2 (@pair _ _) m1 W1 X1) /\
   v_pw_rel (qrow_rel (5*5*6)%nat sw2 sy2 qmin qmax Wb2 Sb2) m2
     (v_pw2 (@pair _ _) m2 Wq2 X2h) (v_pw2 (@pair _ _) m2 W2 X2) /\
   v_pw_rel (qrow_rel 400%nat sw3 sy3 qmin qmax Wb3 Sb3) m3
     (v_pw2 (@pair _ _) m3 Wq3 X3h) (v_pw2 (@pair _ _) m3 W3 X3) /\
   v_pw_rel (qrow_rel 120%nat sw4 sy4 qmin qmax Wb4 Sb4) m4
     (v_pw2 (@pair _ _) m4 Wq4 X4h) (v_pw2 (@pair _ _) m4 W4 X4) /\
   v_pw_rel (qrow_rel 84%nat sw5 sy5 qmin qmax Wb5 Sb5) m5
     (v_pw2 (@pair _ _) m5 Wq5 X5h) (v_pw2 (@pair _ _) m5 W5 X5)) /\
  (v_pw_rel (fun xh x => v_pw_ub (qd0 sx0) (5*5*1)%nat xh x) m1 X1h X1 /\
   v_pw_rel (fun xh x => v_pw_ub (qd1 sx0 sw1 sy1 Wb1 Sb1) (5*5*6)%nat xh x)
     m2 X2h X2 /\
   v_pw_rel (fun xh x =>
       v_pw_ub (qd2 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2) 400%nat xh x)
     m3 X3h X3 /\
   v_pw_rel (fun xh x =>
       v_pw_ub (qd3 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3)
         120%nat xh x) m4 X4h X4 /\
   v_pw_rel (fun xh x =>
       v_pw_ub (qd4 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                  sw4 sy4 Wb4 Sb4) 84%nat xh x) m5 X5h X5).

(* End-to-end int8 LeNet-5: the stored (quantized, requantized) fc3 output
   vector vs the exact one, followed by any softmax component sm with
   Lipschitz constant Lsm.  Absolute-error counterpart of lenet5_end_to_end
   in Opt_ApproxError_Apply.v: the bound is Lsm * qd5 with qd5 built purely
   from half-quanta and abs-sums — no gamma factors anywhere. *)
Theorem qint_lenet5_end_to_end : forall
    (m1 m2 m3 m4 m5 : nat)
    (W1 Wq1 : vector (vector R (5*5*1)%nat) m1)
    (X1 X1h : vector (vector R (5*5*1)%nat) m1)
    (W2 Wq2 : vector (vector R (5*5*6)%nat) m2)
    (X2 X2h : vector (vector R (5*5*6)%nat) m2)
    (W3 Wq3 : vector (vector R 400%nat) m3)
    (X3 X3h : vector (vector R 400%nat) m3)
    (W4 Wq4 : vector (vector R 120%nat) m4)
    (X4 X4h : vector (vector R 120%nat) m4)
    (W5 Wq5 : vector (vector R 84%nat) m5)
    (X5 X5h : vector (vector R 84%nat) m5)
    (sx0 sw1 sy1 sw2 sy2 sw3 sy3 sw4 sy4 sw5 sy5 qmin qmax : R)
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm : R),
  qint_lenet5_hyps m1 m2 m3 m4 m5
    W1 Wq1 X1 X1h W2 Wq2 X2 X2h W3 Wq3 X3 X3h W4 Wq4 X4 X4h W5 Wq5 X5 X5h
    sx0 sw1 sy1 sw2 sy2 sw3 sy3 sw4 sy4 sw5 sy5 qmin qmax
    Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm ->
  forall (sm : vector R m5 -> R),
  (forall a b : vector R m5,
     v_pw_ub (qd5 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                sw4 sy4 Wb4 Sb4 sw5 sy5 Wb5 Sb5) m5 a b ->
     Rabs (sm a - sm b)
       <= Lsm * qd5 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                    sw4 sy4 Wb4 Sb4 sw5 sy5 Wb5 Sb5) ->
  Rabs (sm (v_pw2 (fun a b => quant_r qmin qmax sy5 (dot_exact a b))
                  m5 Wq5 X5h)
        - sm (v_pw2 (fun a b => dot_exact a b) m5 W5 X5))
  <= Lsm * qd5 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
               sw4 sy4 Wb4 Sb4 sw5 sy5 Wb5 Sb5.
Proof.
  intros m1 m2 m3 m4 m5
         W1 Wq1 X1 X1h W2 Wq2 X2 X2h W3 Wq3 X3 X3h W4 Wq4 X4 X4h W5 Wq5 X5 X5h
         sx0 sw1 sy1 sw2 sy2 sw3 sy3 sw4 sy4 sw5 sy5 qmin qmax
         Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm H sm Hsm.
  destruct H as [Hnn [Hrows Hin]].
  destruct Hnn as (Hsx0 & Hsw1 & Hsw2 & Hsw3 & Hsw4 & Hsw5
                  & Hsy1 & Hsy2 & Hsy3 & Hsy4 & Hsy5 & Hqq
                  & HWb1 & HWb2 & HWb3 & HWb4 & HWb5
                  & HSb1 & HSb2 & HSb3 & HSb4 & HSb5 & HLsm).
  destruct Hrows as [Hr1 [Hr2 [Hr3 [Hr4 Hr5]]]].
  destruct Hin as [Hu1 [Hu2 [Hu3 [Hu4 Hu5]]]].
  (* stage nonnegativity certificates *)
  assert (Hd0 : 0 <= qd0 sx0) by (unfold qd0; lra).
  assert (Hd1 : 0 <= qd1 sx0 sw1 sy1 Wb1 Sb1)
    by (unfold qd1; apply q_layer_err_nonneg; lra).
  assert (Hd2 : 0 <= qd2 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2)
    by (unfold qd2; apply q_layer_err_nonneg; lra).
  assert (Hd3 : 0 <= qd3 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3)
    by (unfold qd3; apply q_layer_err_nonneg; lra).
  assert (Hd4 : 0 <= qd4 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                     sw4 sy4 Wb4 Sb4)
    by (unfold qd4; apply q_layer_err_nonneg; lra).
  (* stage 1: conv1 (25 products), inputs carry d0 = sx0/2 *)
  assert (E1 : v_pw_ub (qd1 sx0 sw1 sy1 Wb1 Sb1) m1
      (v_pw2 (fun a b => quant_r qmin qmax sy1 (dot_exact a b)) m1 Wq1 X1h)
      (v_pw2 (fun a b => dot_exact a b) m1 W1 X1)).
  { unfold qd1.
    apply (qint_lin_layer_pw_ub m1 (5*5*1)%nat W1 Wq1 X1 X1h
             qmin qmax sw1 sy1 Wb1 Sb1 (qd0 sx0)); assumption. }
  (* stage 2: conv2 (150 products) over pooled conv1 outputs *)
  assert (E2 : v_pw_ub (qd2 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2) m2
      (v_pw2 (fun a b => quant_r qmin qmax sy2 (dot_exact a b)) m2 Wq2 X2h)
      (v_pw2 (fun a b => dot_exact a b) m2 W2 X2)).
  { unfold qd2.
    apply (qint_lin_layer_pw_ub m2 (5*5*6)%nat W2 Wq2 X2 X2h
             qmin qmax sw2 sy2 Wb2 Sb2 (qd1 sx0 sw1 sy1 Wb1 Sb1)); assumption. }
  (* stage 3: fc1 (400 products) over pooled+flattened conv2 outputs *)
  assert (E3 : v_pw_ub (qd3 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3) m3
      (v_pw2 (fun a b => quant_r qmin qmax sy3 (dot_exact a b)) m3 Wq3 X3h)
      (v_pw2 (fun a b => dot_exact a b) m3 W3 X3)).
  { unfold qd3.
    apply (qint_lin_layer_pw_ub m3 400%nat W3 Wq3 X3 X3h
             qmin qmax sw3 sy3 Wb3 Sb3
             (qd2 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2)); assumption. }
  (* stage 4: fc2 (120 products) over ReLU(fc1) *)
  assert (E4 : v_pw_ub (qd4 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                           sw4 sy4 Wb4 Sb4) m4
      (v_pw2 (fun a b => quant_r qmin qmax sy4 (dot_exact a b)) m4 Wq4 X4h)
      (v_pw2 (fun a b => dot_exact a b) m4 W4 X4)).
  { unfold qd4.
    apply (qint_lin_layer_pw_ub m4 120%nat W4 Wq4 X4 X4h
             qmin qmax sw4 sy4 Wb4 Sb4
             (qd3 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3));
      assumption. }
  (* stage 5: fc3 (84 products) over ReLU(fc2) *)
  assert (E5 : v_pw_ub (qd5 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                           sw4 sy4 Wb4 Sb4 sw5 sy5 Wb5 Sb5) m5
      (v_pw2 (fun a b => quant_r qmin qmax sy5 (dot_exact a b)) m5 Wq5 X5h)
      (v_pw2 (fun a b => dot_exact a b) m5 W5 X5)).
  { unfold qd5.
    apply (qint_lin_layer_pw_ub m5 84%nat W5 Wq5 X5 X5h
             qmin qmax sw5 sy5 Wb5 Sb5
             (qd4 sx0 sw1 sy1 Wb1 Sb1 sw2 sy2 Wb2 Sb2 sw3 sy3 Wb3 Sb3
                sw4 sy4 Wb4 Sb4)); assumption. }
  (* softmax component *)
  apply Hsm. exact E5.
Qed.

(* int8 instance of conv1: qmin = -128, qmax = 127. *)
Example qint_lenet5_conv1_int8 : forall (m1:nat)
    (W1 Wq1 X1 X1h : vector (vector R (5*5*1)%nat) m1)
    (sx0 sw1 sy1 Wb1 Sb1 : R),
  0 <= sx0 -> 0 <= sw1 -> 0 < sy1 -> 0 <= Wb1 -> 0 <= Sb1 ->
  v_pw_rel (qrow_rel (5*5*1)%nat sw1 sy1 (-128) 127 Wb1 Sb1) m1
    (v_pw2 (@pair _ _) m1 Wq1 X1h) (v_pw2 (@pair _ _) m1 W1 X1) ->
  v_pw_rel (fun xh x => v_pw_ub (qd0 sx0) (5*5*1)%nat xh x) m1 X1h X1 ->
  v_pw_ub (qd1 sx0 sw1 sy1 Wb1 Sb1) m1
    (v_pw2 (fun a b => quant_r (-128) 127 sy1 (dot_exact a b)) m1 Wq1 X1h)
    (v_pw2 (fun a b => dot_exact a b) m1 W1 X1).
Proof.
  intros m1 W1 Wq1 X1 X1h sx0 sw1 sy1 Wb1 Sb1 Hsx0 Hsw1 Hsy1 HWb1 HSb1 Hrows Hin.
  unfold qd1.
  apply (qint_lin_layer_pw_ub m1 (5*5*1)%nat W1 Wq1 X1 X1h
           (-128) 127 sw1 sy1 Wb1 Sb1 (qd0 sx0)); try lra; try assumption.
  unfold qd0; lra.
Qed.

End QuantRounding.

(* -------------------------------------------------------------------------- *)
(* 4. TF32 vs int8: absolute vs relative error models (summary)               *)
(* -------------------------------------------------------------------------- *)
(*                                                                           *)
(* TF32 track (Opt_ApproxError.v / Opt_ApproxError_Apply.v):                 *)
(*   model  |rnd x - x| <= u * |x|,   u = 2^-11, no range hypothesis;        *)
(*   dot    |dot_rnd - dot| <= gamma_{n+1} * Sum|w_i x_i|,                   *)
(*          gamma_{n+1} = (1+u)^(n+1) - 1  (grows with n, rounded accum.);   *)
(*   chain  Lsm * gamma_784 * Sbar  (relative to the abs-sum scale Sbar).    *)
(*   Valid for every magnitude, but the relative form degrades when          *)
(*   |dot| << Sum|w_i x_i| (cancellation, condition number kappa).           *)
(*                                                                           *)
(* int8 track (this file):                                                   *)
(*   model  |quant_r x - x| <= s/2 (ABSOLUTE), only in range [s*qmin,s*qmax] *)
(*          (otherwise + overshoot term, quant_r_err_general);               *)
(*   dot    |dot_int8 - dot| <= (sw*sx/2)*(Qx + Qw) + n*sw*sx/4              *)
(*          — LINEAR in n, no gamma: int32 accumulation is EXACT             *)
(*          (dot_int8_eq_deq); the only rounding is input quantization       *)
(*          and output requantization (+sy/2 per layer);                     *)
(*   chain  Lsm * qd5, qd5 from the recurrence                               *)
(*          d_{k+1} = sy_k/2 + (sw_k/2)*(Sb_k + n_k d_k) + Wb_k d_k.         *)
(*   Absolute bounds are cancellation-immune (valid near zero where the      *)
(*   relative model blows up), but require the dynamic range to be           *)
(*   controlled (the in-range hypotheses); scales trade range vs quantum.    *)
(*   Bridge: quant_err_to_rel — with |x| >= x0 > 0 the absolute model yields *)
(*   a relative one with u = s/(2*x0), recovering the TF32-style form.       *)
(*                                                                           *)
(* Coral NPU connection (hw_adapt/01_CoralNPU适配分析.md §2): the int8 path   *)
(* modeled here is exactly the Coral edge-TPU datapath (int8 operands,       *)
(* int32 accumulator, per-tensor scales, requantization at layer outputs).   *)
(*                                                                           *)
(* Axiom audit: only the two standard classical axioms inherited from the    *)
(* base development (ClassicalDedekindReals.sig_forall_dec,                  *)
(* functional_extensionality_dep).  [round]/[round_err] are discharged as    *)
(* universal premises by the section mechanism, not axioms.                  *)
(* -------------------------------------------------------------------------- *)

Print Assumptions quant_r_err_in_range.
Print Assumptions quant_r_err_general.
Print Assumptions dot_int8_eq_deq.
Print Assumptions dot_int8_error.
Print Assumptions dot_int8_error_intsum.
Print Assumptions dot_int8_error_int8.
Print Assumptions dot_int8_requant_error.
Print Assumptions qint_layer_scalar.
Print Assumptions qint_lin_layer_pw_ub.
Print Assumptions qint_lenet5_end_to_end.
