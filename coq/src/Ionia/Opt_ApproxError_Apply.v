(* ========================================================================= *)
(* Opt_ApproxError_Apply.v                                                   *)
(*                                                                           *)
(* Application of the abstract rounding error bounds of Opt_ApproxError.v    *)
(* to a full LeNet-5 inference chain:                                        *)
(*                                                                           *)
(*     conv1 -> pool1 -> conv2 -> pool2 -> fc1 -> fc2 -> fc3 -> softmax      *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   1. Lipschitz-1 building blocks: ReLU (relu_lipschitz) and 2x2 maxpool   *)
(*      (maxpool2x2_lipschitz), plus their pointwise-vector liftings.        *)
(*   2. dot_layer_scalar: scalar (uniform-bound) form of two_layer_error     *)
(*      from Opt_ApproxError.v - one linear layer with reduction length n,   *)
(*      weight abs-sum Wb, exact abs-sum bound Sb and input pointwise        *)
(*      error d produces output error                                        *)
(*          layer_err g Wb Sb d = g*(Sb + Wb*d) + Wb*d,   g = gamma_{n+1}.   *)
(*   3. lin_layer_pw_ub: lifting to a whole layer (vector of dot products).  *)
(*   4. lenet5_end_to_end: composition over the 5 linear layers of LeNet-5.  *)
(*      Pooling / patch-extraction / ReLU between layers enter as pointwise  *)
(*      bound-preservation hypotheses, each discharged by the Lipschitz-1    *)
(*      lemmas of part 1 (pooling and patch extraction never increase a      *)
(*      pointwise error bound; ReLU neither).  softmax enters through its    *)
(*      Lipschitz constant Lsm (kept symbolic; classically Lsm <= 1/2 in     *)
(*      the max-norm).                                                       *)
(*   5. lenet5_end_to_end_compact: closed single-gamma form.  With weight    *)
(*      abs-sums Wb <= 1 (e.g. after normalization) and uniform abs-sum      *)
(*      bound Sbar, the whole chain collapses to                             *)
(*          |out_rnd - out_exact| <= Lsm * gamma_784 * Sbar,                 *)
(*      784 = 26 + 151 + 401 + 121 + 85 (sum of the five per-layer gamma     *)
(*      indices), because prod (1+g_k) = (1+u)^784.                          *)
(*   6. TF32 numeric table (u = 2^-11): each gamma_n is bounded above by a   *)
(*      decimal rational, computed with vm_compute over Q and transferred    *)
(*      to R via Q2R.  Paper table:                                          *)
(*                                                                           *)
(*      layer | reduction n | gamma index | gamma_{n+1} (exact)  | upper bd  *)
(*      ------+-------------+-------------+----------------------+---------- *)
(*      conv1 | 25 (5*5*1)  |    26       | 1.277310e-2          | 1.278e-2  *)
(*      conv2 | 150 (5*5*6) |   151       | 7.649724e-2          | 7.650e-2  *)
(*      fc1   | 400         |   401       | 2.162265e-1          | 2.163e-1  *)
(*      fc2   | 120         |   121       | 6.084696e-2          | 6.085e-2  *)
(*      fc3   | 84          |    85       | 4.236667e-2          | 4.237e-2  *)
(*      chain | sum = 784   |   784       | 4.662661e-1          | 4.663e-1  *)
(*                                                                           *)
(*      (n*u linear approximations: 1.2695e-2, 7.3730e-2, 1.9580e-1,         *)
(*       5.9082e-2, 4.1504e-2, 3.8281e-1 -- gamma_n = n*u + O(u^2) is a      *)
(*       slight under-estimate; cf. gamma_ge_INR_mul_u.)                     *)
(*                                                                           *)
(*   Comparison with measurement (doc/TF32试点报告_20260828.md):              *)
(*      the measured TF32 conv-layer normwise relative error is 7.7e-4       *)
(*      (default rounding) resp. 2.9e-4 (RNE pre-rounding), insensitive to   *)
(*      the reduction length K.  Our worst-case per-layer bounds are         *)
(*      gamma_26 = 1.28e-2 (conv1) ... gamma_401 = 2.16e-1 (fc1), i.e.       *)
(*      16.6x resp. 44x above the measured value for conv1.  This matches    *)
(*      the 4-12x conservatism established in                                *)
(*      doc/双精度版本与误差界报告_20260828.md (same order of magnitude; the  *)
(*      residual gap is the worst-case/coherent-accumulation assumption of   *)
(*      the gamma_n model plus the normwise-vs-elementwise difference and    *)
(*      the condition number kappa >= 1 that the relative form would need).  *)
(*      The end-to-end gamma_784 = 4.66e-1 * Lsm * Sbar is the formal        *)
(*      worst-case certificate: loose but fully proved, parameter-free,      *)
(*      and valid for *every* rounding operator satisfying the standard      *)
(*      model at u = 2^-11.                                                  *)
(*                                                                           *)
(* No Admitted, no Axiom.  Print Assumptions reports only the two standard   *)
(* classical axioms already present in the base file Opt_ApproxError.v       *)
(* (ClassicalDedekindReals.sig_forall_dec from the stdlib construction of R, *)
(* and functional_extensionality_dep via Proof_CodeGen.v).                   *)
(* ========================================================================= *)

Require Import Reals Lra Psatz Arith QArith Qreals.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.Opt_ApproxError.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* 1. Pointwise uniform error bound and Lipschitz-1 layers                    *)
(* -------------------------------------------------------------------------- *)

(* Uniform pointwise bound: every component of a differs from b by <= d. *)
Definition v_pw_ub (d : R) (n:nat) (a b : vector R n) : Prop :=
  v_pw_rel (fun x y => Rabs (x - y) <= d) n a b.

Lemma v_pw_ub_refl : forall (n:nat) (d:R) (a : vector R n),
  0 <= d -> v_pw_ub d n a a.
Proof.
  intros n d a; revert d; induction n as [|n IHn]; intros d Hd.
  - destruct a. exact I.
  - destruct a as [a1 a2]. split; [apply IHn; exact Hd|].
    simpl. replace (a2 - a2) with 0 by ring. rewrite Rabs_R0. exact Hd.
Qed.

(* ReLU as max(0, .). *)
Definition relu (x:R) : R := Rmax 0 x.

Lemma relu_lipschitz : forall a b : R,
  Rabs (relu a - relu b) <= Rabs (a - b).
Proof.
  intros a b. unfold relu, Rmax, Rabs.
  destruct (Rle_dec 0 a); destruct (Rle_dec 0 b);
  repeat match goal with |- context [Rcase_abs ?e] => destruct (Rcase_abs e) end;
  lra.
Qed.

(* Binary max is 1-Lipschitz in each argument (sum form). *)
Lemma max2_lipschitz : forall a b c d : R,
  Rabs (Rmax a b - Rmax c d) <= Rabs (a - c) + Rabs (b - d).
Proof.
  intros a b c d. unfold Rmax, Rabs.
  destruct (Rle_dec a b); destruct (Rle_dec c d);
  repeat match goal with |- context [Rcase_abs ?e] => destruct (Rcase_abs e) end;
  lra.
Qed.

(* 2x2 maxpool window: the output error is bounded by the sum (hence also by
   the max, and a fortiori by any uniform pointwise bound) of input errors. *)
Lemma maxpool2x2_lipschitz : forall a b c d a' b' c' d' : R,
  Rabs (Rmax (Rmax a b) (Rmax c d) - Rmax (Rmax a' b') (Rmax c' d'))
  <= Rabs (a - a') + Rabs (b - b') + Rabs (c - c') + Rabs (d - d').
Proof.
  intros a b c d a' b' c' d'.
  pose proof (max2_lipschitz (Rmax a b) (Rmax c d) (Rmax a' b') (Rmax c' d')) as H0.
  pose proof (max2_lipschitz a b a' b') as H1.
  pose proof (max2_lipschitz c d c' d') as H2.
  lra.
Qed.

(* ReLU (pointwise) preserves any uniform pointwise error bound. *)
Lemma v_pw_ub_relu : forall (n:nat) (d:R) (a b : vector R n),
  v_pw_ub d n a b ->
  v_pw_ub d n (v_map1 relu n a) (v_map1 relu n b).
Proof.
  intros n d a b; revert a b; induction n as [|n IHn]; intros a b H.
  - destruct a, b. exact I.
  - destruct a as [a1 a2], b as [b1 b2].
    destruct H as [Hrec Hlast].
    rewrite !v_map1_Sn. split; [apply IHn; exact Hrec|].
    eapply Rle_trans. apply relu_lipschitz. exact Hlast.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2-3. Scalar layer bound and its lifting to whole layers                    *)
(* -------------------------------------------------------------------------- *)

Section ChainError.

Variable u : R.
Hypothesis Hu : 0 <= u.

Variable rnd : R -> R.
Hypothesis Hrnd : forall x:R, Rabs (rnd x - x) <= u * Rabs x.

(* gamma_n >= n*u: the linear approximation is a lower bound (Bernoulli). *)
Lemma gamma_ge_INR_mul_u : forall n:nat, INR n * u <= (1 + u) ^ n - 1.
Proof.
  induction n as [|n IHn].
  - simpl. lra.
  - rewrite S_INR.
    replace ((1 + u) ^ S n) with ((1 + u) * (1 + u) ^ n) by reflexivity.
    pose proof (pow_1pu_ge_1 u Hu n) as H1.
    pose proof (pos_INR n) as Hn.
    nra.
Qed.

(* The error of one linear layer, scalar form:
   g = gamma_{n+1}, Wb = weight abs-sum bound, Sb = exact abs-sum bound,
   d = uniform input pointwise error. *)
Definition layer_err (g Wb Sb d : R) : R := g * (Sb + Wb * d) + Wb * d.

Lemma layer_err_nonneg : forall g Wb Sb d : R,
  0 <= g -> 0 <= Wb -> 0 <= Sb -> 0 <= d -> 0 <= layer_err g Wb Sb d.
Proof.
  unfold layer_err. intros g Wb Sb d Hg HW HS Hd.
  assert (H1 : 0 <= Wb * d) by (apply Rmult_le_pos; auto).
  assert (H2 : 0 <= Sb + Wb * d) by lra.
  assert (H3 : 0 <= g * (Sb + Wb * d)) by (apply Rmult_le_pos; auto).
  lra.
Qed.

(* Convert a uniform pointwise bound into the paired-delta relation that
   two_layer_error expects, with constant delta vector d. *)
Lemma v_pw_ub_to_rel : forall (n:nat) (d:R) (chat c : vector R n),
  v_pw_ub d n chat c ->
  v_pw_rel (fun chi p => Rabs (chi - fst p) <= snd p) n chat
    (v_pw2 (@pair R R) n c (v_map1 (fun _ : R => d) n c)).
Proof.
  intros n d chat c; revert chat c; induction n as [|n IHn]; intros chat c H.
  - destruct chat, c. exact I.
  - destruct chat as [ch1 ch2], c as [c1 c2].
    destruct H as [Hrec Hlast].
    rewrite v_map1_Sn, v_pw2_Sn. split; [apply IHn; exact Hrec | exact Hlast].
Qed.

Lemma rsum_absmul_constdelta : forall (n:nat) (w c : vector R n) (d:R),
  rsum (v_pw2 (fun wj dj => Rabs wj * dj) n w (v_map1 (fun _ : R => d) n c))
  = d * v_abs_sum w.
Proof.
  intros n w c; revert w c; induction n as [|n IHn]; intros w c d.
  - destruct w, c. unfold v_abs_sum, rsum. simpl. ring.
  - destruct w as [w1 w2], c as [c1 c2].
    rewrite v_map1_Sn, v_pw2_Sn, rsum_Sn, v_abs_sum_Sn, IHn. ring.
Qed.

(* Scalar form of two_layer_error (Opt_ApproxError.v): one dot product over
   perturbed inputs, bounded by gamma_{n+1}, Sb and the weight abs-sum. *)
Theorem dot_layer_scalar : forall (n:nat) (w c chat : vector R n) (Sb d : R),
  0 <= d ->
  v_pw_ub d n chat c ->
  v_abs_sum (v_pw2 Rmult n w c) <= Sb ->
  Rabs (dot_rnd rnd w chat - dot_exact w c)
  <= ((1 + u) ^ (S n) - 1) * (Sb + v_abs_sum w * d) + v_abs_sum w * d.
Proof.
  intros n w c chat Sb d Hd Hub HSb.
  pose proof (two_layer_error u Hu rnd Hrnd n w c chat
                (v_map1 (fun _ : R => d) n c)
                (v_pw_ub_to_rel n d chat c Hub)) as H2.
  rewrite rsum_absmul_constdelta in H2.
  pose proof (gamma_nonneg u Hu (S n)) as Hg.
  assert (Hle : ((1+u)^(S n) - 1) * (v_abs_sum (v_pw2 Rmult n w c)
                                       + d * v_abs_sum w)
                + d * v_abs_sum w
          <= ((1+u)^(S n) - 1) * (Sb + v_abs_sum w * d) + v_abs_sum w * d).
  { replace (v_abs_sum w * d) with (d * v_abs_sum w) by ring.
    apply Rplus_le_compat_r. apply Rmult_le_compat_l; auto.
    apply Rplus_le_compat_r. exact HSb. }
  eapply Rle_trans; eassumption.
Qed.

Lemma v_pw_ub_refl_rows : forall (m n:nat) (X : vector (vector R n) m),
  v_pw_rel (fun xh x => v_pw_ub 0 n xh x) m X X.
Proof.
  intros m n; induction m as [|m IHm]; intros X.
  - destruct X. exact I.
  - destruct X as [X1 x]. split; [apply IHm | apply v_pw_ub_refl; lra].
Qed.

(* Whole-layer lifting: m output neurons, each a dot product of length n
   (conv: each row w paired with its own input patch x). *)
Theorem lin_layer_pw_ub : forall (m n:nat)
    (W Xh X : vector (vector R n) m) (Sb Wb d : R),
  0 <= d -> 0 <= Sb -> 0 <= Wb ->
  v_pw_rel (fun w x => v_abs_sum w <= Wb
                       /\ v_abs_sum (v_pw2 Rmult n w x) <= Sb) m W X ->
  v_pw_rel (fun xh x => v_pw_ub d n xh x) m Xh X ->
  v_pw_ub (((1+u)^(S n) - 1) * (Sb + Wb * d) + Wb * d) m
    (v_pw2 (fun w x => dot_rnd rnd w x) m W Xh)
    (v_pw2 (fun w x => dot_exact w x) m W X).
Proof.
  intros m n W Xh X; revert W Xh X; induction m as [|m IHm]; intros W Xh X Sb Wb d Hd HSb HWb Hrows Hin.
  - destruct W, Xh, X. exact I.
  - destruct W as [W1 w], Xh as [Xh1 xh], X as [X1 x].
    destruct Hrows as [Hrows Hrlast], Hin as [Hin Hilast].
    rewrite !v_pw2_Sn. split; [apply IHm; auto|].
    destruct Hrlast as [HW HS].
    pose proof (dot_layer_scalar n w x xh Sb d Hd Hilast HS) as Hs.
    pose proof (gamma_nonneg u Hu (S n)) as Hg.
    pose proof (v_abs_sum_nonneg n w) as Hw.
    assert (Hwd : v_abs_sum w * d <= Wb * d).
    { apply Rmult_le_compat_r; auto. }
    assert (H3 : ((1+u)^(S n) - 1) * (v_abs_sum w * d)
                 <= ((1+u)^(S n) - 1) * (Wb * d)).
    { apply Rmult_le_compat_l; auto. }
    eapply Rle_trans. exact Hs.
    replace (((1+u)^(S n) - 1) * (Sb + v_abs_sum w * d))
      with (((1+u)^(S n) - 1) * Sb + ((1+u)^(S n) - 1) * (v_abs_sum w * d))
      by ring.
    replace (((1+u)^(S n) - 1) * (Sb + Wb * d))
      with (((1+u)^(S n) - 1) * Sb + ((1+u)^(S n) - 1) * (Wb * d))
      by ring.
    lra.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. LeNet-5 end-to-end chain                                                *)
(* -------------------------------------------------------------------------- *)

(* Per-layer gamma factors: gamma index = reduction length + 1.
   conv1: 5*5*1 = 25 products -> gamma_26;  conv2: 5*5*6 = 150 -> gamma_151;
   fc1: 400 -> gamma_401;  fc2: 120 -> gamma_121;  fc3: 84 -> gamma_85. *)
Definition g_conv1 : R := (1 + u)^26%nat - 1.
Definition g_conv2 : R := (1 + u)^151%nat - 1.
Definition g_fc1 : R := (1 + u)^401%nat - 1.
Definition g_fc2 : R := (1 + u)^121%nat - 1.
Definition g_fc3 : R := (1 + u)^85%nat - 1.

(* Per-stage accumulated uniform error bounds. *)
Definition d1_of (Wb1 Sb1 : R) : R := layer_err g_conv1 Wb1 Sb1 0.
Definition d2_of (Wb1 Sb1 Wb2 Sb2 : R) : R :=
  layer_err g_conv2 Wb2 Sb2 (d1_of Wb1 Sb1).
Definition d3_of (Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 : R) : R :=
  layer_err g_fc1 Wb3 Sb3 (d2_of Wb1 Sb1 Wb2 Sb2).
Definition d4_of (Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 : R) : R :=
  layer_err g_fc2 Wb4 Sb4 (d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3).
Definition d5_of (Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5 : R) : R :=
  layer_err g_fc3 Wb5 Sb5 (d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4).

(* Chain hypotheses, bundled:
   - nonnegativity of all bound parameters and of Lsm;
   - per-layer row bounds (weight abs-sum, exact abs-sum);
   - bound preservation across pool1+patching, pool2+flattening, and the two
     ReLU stages.  Each ub hypothesis is discharged by maxpool2x2_lipschitz
     (pooling) resp. v_pw_ub_relu (ReLU); patch extraction / flattening only
     rearrange components and never change a uniform pointwise bound. *)
Definition lenet5_hyps
    (m1 m2 m3 m4 m5 : nat)
    (W1 : vector (vector R (5*5*1)%nat) m1) (X1 : vector (vector R (5*5*1)%nat) m1)
    (W2 : vector (vector R (5*5*6)%nat) m2) (X2 X2h : vector (vector R (5*5*6)%nat) m2)
    (W3 : vector (vector R 400%nat) m3) (X3 X3h : vector (vector R 400%nat) m3)
    (W4 : vector (vector R 120%nat) m4) (X4 X4h : vector (vector R 120%nat) m4)
    (W5 : vector (vector R 84%nat) m5) (X5 X5h : vector (vector R 84%nat) m5)
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm : R) : Prop :=
  (0 <= Wb1 /\ 0 <= Wb2 /\ 0 <= Wb3 /\ 0 <= Wb4 /\ 0 <= Wb5 /\
   0 <= Sb1 /\ 0 <= Sb2 /\ 0 <= Sb3 /\ 0 <= Sb4 /\ 0 <= Sb5 /\ 0 <= Lsm) /\
  (v_pw_rel (fun w x => v_abs_sum w <= Wb1
             /\ v_abs_sum (v_pw2 Rmult (5*5*1)%nat w x) <= Sb1) m1 W1 X1 /\
   v_pw_rel (fun w x => v_abs_sum w <= Wb2
             /\ v_abs_sum (v_pw2 Rmult (5*5*6)%nat w x) <= Sb2) m2 W2 X2 /\
   v_pw_rel (fun w x => v_abs_sum w <= Wb3
             /\ v_abs_sum (v_pw2 Rmult 400%nat w x) <= Sb3) m3 W3 X3 /\
   v_pw_rel (fun w x => v_abs_sum w <= Wb4
             /\ v_abs_sum (v_pw2 Rmult 120%nat w x) <= Sb4) m4 W4 X4 /\
   v_pw_rel (fun w x => v_abs_sum w <= Wb5
             /\ v_abs_sum (v_pw2 Rmult 84%nat w x) <= Sb5) m5 W5 X5) /\
  (v_pw_rel (fun xh x => v_pw_ub (d1_of Wb1 Sb1) (5*5*6)%nat xh x) m2 X2h X2 /\
   v_pw_rel (fun xh x => v_pw_ub (d2_of Wb1 Sb1 Wb2 Sb2) 400%nat xh x) m3 X3h X3 /\
   v_pw_rel (fun xh x => v_pw_ub (d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3) 120%nat xh x) m4 X4h X4 /\
   v_pw_rel (fun xh x => v_pw_ub (d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4) 84%nat xh x) m5 X5h X5).

(* End-to-end: the approximate fc3-output vector (rounded dot products over
   the perturbed inputs) vs the exact one, followed by any softmax component
   sm with Lipschitz constant Lsm. *)
Theorem lenet5_end_to_end : forall
    (m1 m2 m3 m4 m5 : nat)
    (W1 : vector (vector R (5*5*1)%nat) m1) (X1 : vector (vector R (5*5*1)%nat) m1)
    (W2 : vector (vector R (5*5*6)%nat) m2) (X2 X2h : vector (vector R (5*5*6)%nat) m2)
    (W3 : vector (vector R 400%nat) m3) (X3 X3h : vector (vector R 400%nat) m3)
    (W4 : vector (vector R 120%nat) m4) (X4 X4h : vector (vector R 120%nat) m4)
    (W5 : vector (vector R 84%nat) m5) (X5 X5h : vector (vector R 84%nat) m5)
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm : R),
  lenet5_hyps m1 m2 m3 m4 m5 W1 X1 W2 X2 X2h W3 X3 X3h W4 X4 X4h W5 X5 X5h
              Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm ->
  forall (sm : vector R m5 -> R),
  (forall a b : vector R m5,
     v_pw_ub (d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) m5 a b ->
     Rabs (sm a - sm b)
       <= Lsm * d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) ->
  Rabs (sm (v_pw2 (fun w x => dot_rnd rnd w x) m5 W5 X5h)
         - sm (v_pw2 (fun w x => dot_exact w x) m5 W5 X5))
  <= Lsm * d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5.
Proof.
  intros m1 m2 m3 m4 m5 W1 X1 W2 X2 X2h W3 X3 X3h W4 X4 X4h W5 X5 X5h
         Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm H sm Hsm.
  destruct H as [Hnn [Hrows Hubs]].
  destruct Hnn as [HWb1 [HWb2 [HWb3 [HWb4 [HWb5
                 [HSb1 [HSb2 [HSb3 [HSb4 [HSb5 HLsm]]]]]]]]]].
  destruct Hrows as [Hr1 [Hr2 [Hr3 [Hr4 Hr5]]]].
  destruct Hubs as [Hu1 [Hu2 [Hu3 Hu4]]].
  pose proof (gamma_nonneg u Hu 26%nat) as G1.
  pose proof (gamma_nonneg u Hu 151%nat) as G2.
  pose proof (gamma_nonneg u Hu 401%nat) as G3.
  pose proof (gamma_nonneg u Hu 121%nat) as G4.
  pose proof (gamma_nonneg u Hu 85%nat) as G5.
  (* stage nonnegativity certificates *)
  assert (Hd1 : 0 <= d1_of Wb1 Sb1)
    by (unfold d1_of; apply layer_err_nonneg; auto; lra).
  assert (Hd2 : 0 <= d2_of Wb1 Sb1 Wb2 Sb2)
    by (unfold d2_of; apply layer_err_nonneg; auto).
  assert (Hd3 : 0 <= d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3)
    by (unfold d3_of; apply layer_err_nonneg; auto).
  assert (Hd4 : 0 <= d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4)
    by (unfold d4_of; apply layer_err_nonneg; auto).
  (* stage 1: conv1 (inputs exact) *)
  assert (E1 : v_pw_ub (d1_of Wb1 Sb1) m1
      (v_pw2 (fun w x => dot_rnd rnd w x) m1 W1 X1)
      (v_pw2 (fun w x => dot_exact w x) m1 W1 X1)).
  { unfold d1_of.
    apply (lin_layer_pw_ub m1 (5*5*1)%nat W1 X1 X1 Sb1 Wb1 0);
      [ lra | exact HSb1 | exact HWb1 | exact Hr1 | apply v_pw_ub_refl_rows ]. }
  (* stage 2: conv2 over pooled conv1 outputs *)
  assert (E2 : v_pw_ub (d2_of Wb1 Sb1 Wb2 Sb2) m2
      (v_pw2 (fun w x => dot_rnd rnd w x) m2 W2 X2h)
      (v_pw2 (fun w x => dot_exact w x) m2 W2 X2)).
  { unfold d2_of.
    apply (lin_layer_pw_ub m2 (5*5*6)%nat W2 X2h X2 Sb2 Wb2 (d1_of Wb1 Sb1));
      assumption. }
  (* stage 3: fc1 over pooled+flattened conv2 outputs *)
  assert (E3 : v_pw_ub (d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3) m3
      (v_pw2 (fun w x => dot_rnd rnd w x) m3 W3 X3h)
      (v_pw2 (fun w x => dot_exact w x) m3 W3 X3)).
  { unfold d3_of.
    apply (lin_layer_pw_ub m3 400%nat W3 X3h X3 Sb3 Wb3 (d2_of Wb1 Sb1 Wb2 Sb2));
      assumption. }
  (* stage 4: fc2 over ReLU(fc1) *)
  assert (E4 : v_pw_ub (d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4) m4
      (v_pw2 (fun w x => dot_rnd rnd w x) m4 W4 X4h)
      (v_pw2 (fun w x => dot_exact w x) m4 W4 X4)).
  { unfold d4_of.
    apply (lin_layer_pw_ub m4 120%nat W4 X4h X4 Sb4 Wb4
             (d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3));
      assumption. }
  (* stage 5: fc3 over ReLU(fc2) *)
  assert (E5 : v_pw_ub (d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) m5
      (v_pw2 (fun w x => dot_rnd rnd w x) m5 W5 X5h)
      (v_pw2 (fun w x => dot_exact w x) m5 W5 X5)).
  { unfold d5_of.
    apply (lin_layer_pw_ub m5 84%nat W5 X5h X5 Sb5 Wb5
             (d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4));
      assumption. }
  (* softmax component *)
  apply Hsm. exact E5.
Qed.

(* -------------------------------------------------------------------------- *)
(* 5. Compact single-gamma form: gamma_784                                    *)
(* -------------------------------------------------------------------------- *)

Lemma pow_mul_add : forall (x:R) (a b : nat),
  x ^ (a + b)%nat = x^a * x^b.
Proof.
  intros x a b; induction a as [|a IHa].
  - simpl. ring.
  - replace (S a + b)%nat with (S (a + b))%nat by lia.
    replace (x ^ S (a + b)) with (x * x ^ (a + b)) by reflexivity.
    replace (x ^ S a) with (x * x ^ a) by reflexivity.
    rewrite IHa. ring.
Qed.

(* One layer_err step, weakened to the (1+g)-weighted accumulated form. *)
Lemma layer_err_step : forall g Wb Sb Sbar d C : R,
  0 <= g -> 0 <= Wb -> Wb <= 1 -> 0 <= Sb -> Sb <= Sbar -> 0 <= d ->
  d <= C * Sbar ->
  layer_err g Wb Sb d <= (g + (1 + g) * C) * Sbar.
Proof.
  unfold layer_err. intros g Wb Sb Sbar d C Hg HW HW1 HS HSS Hd HC.
  assert (Hwd : Wb * d <= d).
  { replace d with (1 * d) at 2 by ring. apply Rmult_le_compat_r; auto. }
  assert (H1 : g * Sb <= g * Sbar) by (apply Rmult_le_compat_l; auto).
  assert (H2 : g * (Wb * d) <= g * (C * Sbar)).
  { apply Rmult_le_compat_l; auto. eapply Rle_trans; eassumption. }
  replace (g * (Sb + Wb * d)) with (g * Sb + g * (Wb * d)) by ring.
  replace ((g + (1 + g) * C) * Sbar) with (g * Sbar + C * Sbar + g * (C * Sbar))
    by ring.
  lra.
Qed.

(* With Wb <= 1 and Sb <= Sbar at every layer, the whole chain collapses to
   gamma_784 * Sbar, because prod_k (1 + g_k) = (1+u)^(26+151+401+121+85). *)
Theorem lenet5_chain_collapse : forall
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Sbar : R),
  0 <= Sbar ->
  0 <= Wb1 -> Wb1 <= 1 -> 0 <= Wb2 -> Wb2 <= 1 -> 0 <= Wb3 -> Wb3 <= 1 ->
  0 <= Wb4 -> Wb4 <= 1 -> 0 <= Wb5 -> Wb5 <= 1 ->
  0 <= Sb1 -> Sb1 <= Sbar -> 0 <= Sb2 -> Sb2 <= Sbar ->
  0 <= Sb3 -> Sb3 <= Sbar -> 0 <= Sb4 -> Sb4 <= Sbar ->
  0 <= Sb5 -> Sb5 <= Sbar ->
  d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5
  <= ((1 + u)^784%nat - 1) * Sbar.
Proof.
  intros Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Sbar
         HSbar HWb1 HWb1' HWb2 HWb2' HWb3 HWb3' HWb4 HWb4' HWb5 HWb5'
         HSb1 HSb1' HSb2 HSb2' HSb3 HSb3' HSb4 HSb4' HSb5 HSb5'.
  pose proof (gamma_nonneg u Hu 26%nat) as G1.
  pose proof (gamma_nonneg u Hu 151%nat) as G2.
  pose proof (gamma_nonneg u Hu 401%nat) as G3.
  pose proof (gamma_nonneg u Hu 121%nat) as G4.
  pose proof (gamma_nonneg u Hu 85%nat) as G5.
  assert (N1 : 0 <= d1_of Wb1 Sb1)
    by (unfold d1_of; apply layer_err_nonneg; auto; lra).
  assert (N2 : 0 <= d2_of Wb1 Sb1 Wb2 Sb2)
    by (unfold d2_of; apply layer_err_nonneg; auto).
  assert (N3 : 0 <= d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3)
    by (unfold d3_of; apply layer_err_nonneg; auto).
  assert (N4 : 0 <= d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4)
    by (unfold d4_of; apply layer_err_nonneg; auto).
  assert (A1 : d1_of Wb1 Sb1 <= (g_conv1 + (1 + g_conv1) * 0) * Sbar).
  { unfold d1_of. apply layer_err_step; auto; lra. }
  assert (A2 : d2_of Wb1 Sb1 Wb2 Sb2
        <= (g_conv2 + (1 + g_conv2) * (g_conv1 + (1 + g_conv1) * 0)) * Sbar).
  { unfold d2_of. apply layer_err_step; auto. }
  assert (A3 : d3_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3
        <= (g_fc1 + (1 + g_fc1) * (g_conv2 + (1 + g_conv2)
             * (g_conv1 + (1 + g_conv1) * 0))) * Sbar).
  { unfold d3_of. apply layer_err_step; auto. }
  assert (A4 : d4_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4
        <= (g_fc2 + (1 + g_fc2) * (g_fc1 + (1 + g_fc1) * (g_conv2
             + (1 + g_conv2) * (g_conv1 + (1 + g_conv1) * 0)))) * Sbar).
  { unfold d4_of. apply layer_err_step; auto. }
  assert (A5 : d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5
        <= (g_fc3 + (1 + g_fc3) * (g_fc2 + (1 + g_fc2) * (g_fc1 + (1 + g_fc1)
             * (g_conv2 + (1 + g_conv2) * (g_conv1 + (1 + g_conv1) * 0))))) * Sbar).
  { unfold d5_of. apply layer_err_step; auto. }
  (* collapse the nested form to prod (1+g_k) - 1 *)
  assert (Hprod :
    g_fc3 + (1 + g_fc3) * (g_fc2 + (1 + g_fc2) * (g_fc1 + (1 + g_fc1)
      * (g_conv2 + (1 + g_conv2) * (g_conv1 + (1 + g_conv1) * 0))))
    = (1 + g_fc3) * (1 + g_fc2) * (1 + g_fc1) * (1 + g_conv2) * (1 + g_conv1) - 1)
    by ring.
  assert (Hpow :
    (1 + g_fc3) * (1 + g_fc2) * (1 + g_fc1) * (1 + g_conv2) * (1 + g_conv1)
    = (1 + u)^784%nat).
  { unfold g_fc3, g_fc2, g_fc1, g_conv2, g_conv1.
    replace (1 + ((1 + u)^85%nat - 1)) with ((1 + u)^85%nat) by ring.
    replace (1 + ((1 + u)^121%nat - 1)) with ((1 + u)^121%nat) by ring.
    replace (1 + ((1 + u)^401%nat - 1)) with ((1 + u)^401%nat) by ring.
    replace (1 + ((1 + u)^151%nat - 1)) with ((1 + u)^151%nat) by ring.
    replace (1 + ((1 + u)^26%nat - 1)) with ((1 + u)^26%nat) by ring.
    rewrite <- !pow_mul_add. reflexivity. }
  rewrite Hprod, Hpow in A5. exact A5.
Qed.

(* Compact end-to-end form. *)
Corollary lenet5_end_to_end_compact : forall
    (m1 m2 m3 m4 m5 : nat)
    (W1 : vector (vector R (5*5*1)%nat) m1) (X1 : vector (vector R (5*5*1)%nat) m1)
    (W2 : vector (vector R (5*5*6)%nat) m2) (X2 X2h : vector (vector R (5*5*6)%nat) m2)
    (W3 : vector (vector R 400%nat) m3) (X3 X3h : vector (vector R 400%nat) m3)
    (W4 : vector (vector R 120%nat) m4) (X4 X4h : vector (vector R 120%nat) m4)
    (W5 : vector (vector R 84%nat) m5) (X5 X5h : vector (vector R 84%nat) m5)
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm Sbar : R),
  lenet5_hyps m1 m2 m3 m4 m5 W1 X1 W2 X2 X2h W3 X3 X3h W4 X4 X4h W5 X5 X5h
              Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm ->
  0 <= Sbar ->
  Wb1 <= 1 -> Wb2 <= 1 -> Wb3 <= 1 -> Wb4 <= 1 -> Wb5 <= 1 ->
  Sb1 <= Sbar -> Sb2 <= Sbar -> Sb3 <= Sbar -> Sb4 <= Sbar -> Sb5 <= Sbar ->
  forall (sm : vector R m5 -> R),
  (forall a b : vector R m5,
     v_pw_ub (d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) m5 a b ->
     Rabs (sm a - sm b)
       <= Lsm * d5_of Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) ->
  Rabs (sm (v_pw2 (fun w x => dot_rnd rnd w x) m5 W5 X5h)
         - sm (v_pw2 (fun w x => dot_exact w x) m5 W5 X5))
  <= Lsm * (((1 + u)^784%nat - 1) * Sbar).
Proof.
  intros m1 m2 m3 m4 m5 W1 X1 W2 X2 X2h W3 X3 X3h W4 X4 X4h W5 X5 X5h
         Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm Sbar
         H HSbar HWb1' HWb2' HWb3' HWb4' HWb5'
         HSb1' HSb2' HSb3' HSb4' HSb5' sm Hsm.
  eapply Rle_trans.
  - eapply lenet5_end_to_end; eassumption.
  - destruct H as [Hnn _].
    destruct Hnn as [HWb1 [HWb2 [HWb3 [HWb4 [HWb5
                   [HSb1 [HSb2 [HSb3 [HSb4 [HSb5 HLsm]]]]]]]]]].
    apply Rmult_le_compat_l; [exact HLsm|].
    apply lenet5_chain_collapse; assumption.
Qed.

End ChainError.

(* -------------------------------------------------------------------------- *)
(* 6. TF32 numeric table: u = 2^-11, gamma values via Q + vm_compute          *)
(* -------------------------------------------------------------------------- *)

Definition uQ_TF32 : Q := (1 # 2048)%Q.

Fixpoint Qpow_nat (q:Q) (n:nat) : Q :=
  match n with
  | 0%nat => 1%Q
  | S k => (q * Qpow_nat q k)%Q
  end.

Definition gammaQ (n:nat) : Q := (Qpow_nat (1 + uQ_TF32) n - 1)%Q.

Lemma Q2R_1 : Q2R 1%Q = 1%R.
Proof.
  unfold Q2R. cbn. unfold Rdiv. rewrite Rinv_1. apply Rmult_1_l.
Qed.

Lemma Q2R_pow_nat : forall (q:Q) (n:nat),
  Q2R (Qpow_nat q n) = (Q2R q ^ n)%R.
Proof.
  intros q n; induction n as [|n IHn].
  - apply Q2R_1.
  - cbn [Qpow_nat]. rewrite Q2R_mult, IHn. reflexivity.
Qed.

Lemma baseQ_TF32 : Q2R (1 + uQ_TF32)%Q = 1 + u_TF32.
Proof.
  rewrite Q2R_plus, Q2R_1. f_equal.
  unfold uQ_TF32, u_TF32, Q2R, Rdiv. cbn [Qnum Qden].
  rewrite !Rmult_1_l. reflexivity.
Qed.

Lemma gammaQ_R : forall n:nat,
  Q2R (gammaQ n) = (1 + u_TF32)^n%nat - 1.
Proof.
  intro n. unfold gammaQ.
  rewrite Q2R_minus, Q2R_pow_nat, baseQ_TF32, Q2R_1. reflexivity.
Qed.

(* Paper table, upper bounds by decimal rationals (ceilings of the exact
   values, cf. the header table). *)
Theorem tf32_gamma_conv1 : (1 + u_TF32)^26%nat - 1 <= Q2R (1278 # 100000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem tf32_gamma_conv2 : (1 + u_TF32)^151%nat - 1 <= Q2R (765 # 10000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem tf32_gamma_fc1 : (1 + u_TF32)^401%nat - 1 <= Q2R (2163 # 10000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem tf32_gamma_fc2 : (1 + u_TF32)^121%nat - 1 <= Q2R (6085 # 100000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem tf32_gamma_fc3 : (1 + u_TF32)^85%nat - 1 <= Q2R (4237 # 100000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

Theorem tf32_gamma_chain : (1 + u_TF32)^784%nat - 1 <= Q2R (4663 # 10000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute. reflexivity.
Qed.

(* TF32 headline: for any rounding operator satisfying the standard model at
   u_TF32, the whole LeNet-5 chain is certified by
       |out_TF32 - out_exact| <= Lsm * 0.4663 * Sbar       (worst case). *)
Corollary lenet5_tf32_chain_bound : forall (rnd : R -> R),
  (forall x:R, Rabs (rnd x - x) <= u_TF32 * Rabs x) ->
  forall
    (m1 m2 m3 m4 m5 : nat)
    (W1 : vector (vector R (5*5*1)%nat) m1) (X1 : vector (vector R (5*5*1)%nat) m1)
    (W2 : vector (vector R (5*5*6)%nat) m2) (X2 X2h : vector (vector R (5*5*6)%nat) m2)
    (W3 : vector (vector R 400%nat) m3) (X3 X3h : vector (vector R 400%nat) m3)
    (W4 : vector (vector R 120%nat) m4) (X4 X4h : vector (vector R 120%nat) m4)
    (W5 : vector (vector R 84%nat) m5) (X5 X5h : vector (vector R 84%nat) m5)
    (Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm Sbar : R),
  lenet5_hyps u_TF32 m1 m2 m3 m4 m5 W1 X1 W2 X2 X2h W3 X3 X3h W4 X4 X4h W5 X5 X5h
              Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm ->
  0 <= Sbar ->
  Wb1 <= 1 -> Wb2 <= 1 -> Wb3 <= 1 -> Wb4 <= 1 -> Wb5 <= 1 ->
  Sb1 <= Sbar -> Sb2 <= Sbar -> Sb3 <= Sbar -> Sb4 <= Sbar -> Sb5 <= Sbar ->
  forall (sm : vector R m5 -> R),
  (forall a b : vector R m5,
     v_pw_ub (d5_of u_TF32 Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) m5 a b ->
     Rabs (sm a - sm b)
       <= Lsm * d5_of u_TF32 Wb1 Sb1 Wb2 Sb2 Wb3 Sb3 Wb4 Sb4 Wb5 Sb5) ->
  Rabs (sm (v_pw2 (fun w x => dot_rnd rnd w x) m5 W5 X5h)
         - sm (v_pw2 (fun w x => dot_exact w x) m5 W5 X5))
  <= Lsm * (Q2R (4663 # 10000) * Sbar).
Proof.
  intros rnd0 Hrnd0 m1 m2 m3 m4 m5 W1 X1 W2 X2 X2h W3 X3 X3h W4 X4 X4h W5 X5 X5h
         Wb1 Wb2 Wb3 Wb4 Wb5 Sb1 Sb2 Sb3 Sb4 Sb5 Lsm Sbar
         H HSbar HWb1' HWb2' HWb3' HWb4' HWb5'
         HSb1' HSb2' HSb3' HSb4' HSb5' sm Hsm.
  eapply Rle_trans.
  - eapply (lenet5_end_to_end_compact u_TF32 u_TF32_nonneg rnd0 Hrnd0);
      eassumption.
  - destruct H as [Hnn _].
    destruct Hnn as [HWb1 [HWb2 [HWb3 [HWb4 [HWb5
                   [HSb1 [HSb2 [HSb3 [HSb4 [HSb5 HLsm]]]]]]]]]].
    pose proof tf32_gamma_chain as Ht.
    assert (H0 : 0 <= Lsm * Sbar) by (apply Rmult_le_pos; auto).
    replace (Lsm * (((1 + u_TF32)^784%nat - 1) * Sbar))
      with ((Lsm * Sbar) * ((1 + u_TF32)^784%nat - 1)) by ring.
    replace (Lsm * (Q2R (4663 # 10000) * Sbar))
      with ((Lsm * Sbar) * Q2R (4663 # 10000)) by ring.
    apply Rmult_le_compat_l; auto.
Qed.

(* Axiom audit: only the two standard classical axioms above (same set as    *)
(* the base file Opt_ApproxError.v), nothing else.                           *)
Print Assumptions lenet5_end_to_end.
Print Assumptions lenet5_end_to_end_compact.
Print Assumptions lenet5_chain_collapse.
Print Assumptions lenet5_tf32_chain_bound.
Print Assumptions tf32_gamma_chain.
