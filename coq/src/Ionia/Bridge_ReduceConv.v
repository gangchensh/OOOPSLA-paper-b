(* ========================================================================= *)
(* Bridge_ReduceConv.v                                                       *)
(*                                                                           *)
(* Route-A/route-B bridge for the reduction/convolution/pooling batch,       *)
(* following the pattern of [Ionia.Bridge_Pilot] and [Ionia.Bridge_Elementwise]. *)
(*                                                                           *)
(*   route B (code generation): AST commands [CNN_CodeGen_Core.comm] with    *)
(*     denotation [CNN_CodeGen_Semantics.eval] and operator-wise semantic    *)
(*     equivalences [Operators_Sem_Equiv.*_sem];                             *)
(*   route A (DPIA): semantic commands [Proof_CodeGen.comm] with the         *)
(*     operator-wise Leibniz equalities [LeNet5_DPIA.A_*], [Ops_PoolPad.A_*].*)
(*                                                                           *)
(* For each operator we prove                                                *)
(*   (1) a functional interpretation lemma                                   *)
(*         to_pcg_exp (CNN_OP.op e) rho = RouteA.op (to_pcg_exp e rho)       *)
(*   (2) the comm-level bridge                                               *)
(*         eval (AST op_comm) rho = op_comm (to_pcg_exp e rho) output rho    *)
(*                                                                           *)
(* Coverage:                                                                 *)
(*   Linear1d   [OSE.Linear1d_sem   + LD.A_Linear1d]                         *)
(*   Softmax1d  [OSE.Softmax1d_sem  + LD.A_Softmax1d]                        *)
(*   Maxpool4d  [OSE.Maxpool4d_sem  + Ops_PoolPad.A_Maxpool4d]               *)
(*   Maxpool3d  [OSE.Maxpool3d_sem at k=2 + LD.A_Maxpool3d]                  *)
(*   Flatten3d  [OSE.Flatten3d_sem  + LD.A_Flatten3d]                        *)
(*   Conv3d     [OSE.Conv3d_sem at s=1, n1=n2=k + LD.A_Conv3d], general      *)
(*              dimensions m1 m2 k channel filernum p with k <= m1, k <= m2. *)
(*              The route-B output type [(m1-k+2*p)/1+1] differs from the    *)
(*              route-A type [m1+2*p-k+1] only up to [Nat.div_1_r]/arith,    *)
(*              so the bridge carries the output acceptor through an         *)
(*              explicit [eq_rect] cast [conv3d_cast_out].                   *)
(*                                                                           *)
(* NOT bridged here (missing route-B or route-A counterparts):               *)
(*   Flatten4d:  route B has [Flatten4d_comm]/[OSE.Flatten4d_sem], but       *)
(*     route A (LeNet5_Functional / the Ops_ family) defines no 4-D flatten  *)
(*     or [A_Flatten4d] rule.                                                *)
(*   Conv4d: route A has [Ops_Conv.Conv4d]/[A_Conv4d], but route B only      *)
(*     ships specialized ASTs ([Conv4d_p0_k3_comm] etc.) with no general     *)
(*     [Conv4d_sem]; a general route-B semantic equivalence is missing.      *)
(*   Maxpool2d/Avgpool/GlobalAvgPool4d: route-B [*_sem] exist and route-A    *)
(*     [Ops_Reduce]/[Ops_PoolPad] rules exist; left for a follow-up batch.   *)
(*   BatchNorm4d: route B has [BatchNorm4d_equiv_sem], route A has           *)
(*     [Ops_BatchNorm.A_BatchNorm4d]; the functional forms differ (BN        *)
(*     statistics plumbing), left for a follow-up batch.                     *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

From Stdlib Require Import Reals String Arith Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.
Require Import Ionia.finType Ionia.vector Ionia.DataExp Ionia.CNN_Defs
  Ionia.CNN_CodeGen_Core Ionia.Proof_CodeGen Ionia.DPIA_Rules
  Ionia.CNN_CodeGen_Semantics Ionia.CNN_Examples_Base
  Ionia.CNN_Examples_Base_Ops Ionia.CNN_OP Ionia.Operators_Sem_Equiv
  Ionia.LeNet5_Utils Ionia.LeNet5_Functional Ionia.LeNet5_Imperative
  Ionia.LeNet5_DPIA Ionia.Ops_Conv Ionia.Ops_Reduce Ionia.Ops_PoolPad.

Module DE := Ionia.DataExp.
Module CD := Ionia.CNN_Defs.
Module CG := Ionia.CNN_CodeGen_Core.
Module PCG := Ionia.Proof_CodeGen.
Module DR := Ionia.DPIA_Rules.
Module SEM := Ionia.CNN_CodeGen_Semantics.
Module CEB := Ionia.CNN_Examples_Base.
Module CEO := Ionia.CNN_Examples_Base_Ops.
Module COP := Ionia.CNN_OP.
Module OSE := Ionia.Operators_Sem_Equiv.
Module LU := Ionia.LeNet5_Utils.
Module LF := Ionia.LeNet5_Functional.
Module LI := Ionia.LeNet5_Imperative.
Module LD := Ionia.LeNet5_DPIA.
Module OC := Ionia.Ops_Conv.
Module OR := Ionia.Ops_Reduce.
Module OP := Ionia.Ops_PoolPad.
Module V := Ionia.vector.

(* -------------------------------------------------------------------------- *)
(* Generic interpretation helpers (local copies of the [Bridge_Pilot] ones)   *)
(* -------------------------------------------------------------------------- *)

(* Pointwise extensionality for [to_pcg_exp] over [mkvSeq]. *)
Lemma to_pcg_mkvSeq_ext : forall (n : nat) (d : data)
  (f : fin n -> DE.exp d) (g : fin n -> PCG.exp d) (rho : PCG.env),
  (forall i, SEM.to_pcg_exp (f i) rho = g i) ->
  SEM.to_pcg_exp (DE.mkvSeq f) rho = PCG.mkvSeq g.
Proof.
  intros n d f g rho H.
  rewrite SEM.to_pcg_exp_mkvSeq.
  unfold PCG.mkvSeq.
  apply V.mk_vec_ext.
  exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic [sum]/[max] interpretation lemmas                                  *)
(* -------------------------------------------------------------------------- *)

(* One-step unfolding of the route-B (syntactic) sum over [mkvSeq]. *)
Lemma cd_sum_mkvSeq_Sn : forall (n : nat) (f : fin (S n) -> DE.exp num),
  CD.sum (DE.mkvSeq f) =
  CD.add (f (ltS n)) (CD.sum (DE.mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold CD.sum, DE.mkvSeq. rewrite V.mk_vec_Sn. simpl. reflexivity.
Qed.

(* One-step unfolding of the route-A (semantic) sum over [mkvSeq]. *)
Lemma pcg_sum_mkvSeq_Sn : forall (n : nat) (f : fin (S n) -> PCG.exp num),
  PCG.sum (PCG.mkvSeq f) =
  Rplus (f (ltS n)) (PCG.sum (PCG.mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold PCG.sum, PCG.mkvSeq. rewrite V.mk_vec_Sn. simpl. reflexivity.
Qed.

(* Interpretation of [CD.sum]: the syntactic sum reads as the semantic sum. *)
Lemma to_pcg_sum_mkvSeq : forall (n : nat) (f : fin n -> DE.exp num) (rho : PCG.env),
  SEM.to_pcg_exp (CD.sum (DE.mkvSeq f)) rho =
  PCG.sum (PCG.mkvSeq (fun i => SEM.to_pcg_exp (f i) rho)).
Proof.
  intros n f rho. induction n as [| n' IHn].
  - unfold CD.sum, DE.mkvSeq, PCG.sum, PCG.mkvSeq. simpl.
    rewrite SEM.to_pcg_exp_zero. reflexivity.
  - rewrite cd_sum_mkvSeq_Sn. rewrite SEM.to_pcg_exp_add.
    rewrite IHn. rewrite pcg_sum_mkvSeq_Sn. reflexivity.
Qed.

(* One-step unfolding of the route-B (syntactic) runtime max over [mkvSeq]. *)
Lemma cd_max_mkvSeq_Sn : forall (n : nat) (f : fin (S n) -> DE.exp num),
  CD.max (DE.mkvSeq f) =
  REif (CD.gtExp (f (ltS n)) (CD.max (DE.mkvSeq (fun i : fin n => f (fin2finS i)))))
       (f (ltS n))
       (CD.max (DE.mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold CD.max, DE.mkvSeq. rewrite V.mk_vec_Sn. simpl. reflexivity.
Qed.

(* One-step unfolding of the route-A (semantic) max over [mkvSeq]. *)
Lemma pcg_max_mkvSeq_Sn : forall (n : nat) (f : fin (S n) -> PCG.exp num),
  PCG.max (PCG.mkvSeq f) =
  (if PCG.gtExp (f (ltS n)) (PCG.max (PCG.mkvSeq (fun i : fin n => f (fin2finS i))))
   then f (ltS n)
   else PCG.max (PCG.mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold PCG.max, PCG.mkvSeq. rewrite V.mk_vec_Sn. simpl. reflexivity.
Qed.

(* Interpretation of [CD.max]: the runtime conditional max reads as the
   semantic max. *)
Lemma to_pcg_max_mkvSeq : forall (n : nat) (f : fin n -> DE.exp num) (rho : PCG.env),
  SEM.to_pcg_exp (CD.max (DE.mkvSeq f)) rho =
  PCG.max (PCG.mkvSeq (fun i => SEM.to_pcg_exp (f i) rho)).
Proof.
  intros n f rho. induction n as [| n' IHn].
  - unfold CD.max, DE.mkvSeq, PCG.max, PCG.mkvSeq. simpl.
    rewrite SEM.to_pcg_exp_zero. reflexivity.
  - rewrite cd_max_mkvSeq_Sn.
    rewrite SEM.to_pcg_exp_REif, SEM.to_pcg_exp_BGt, IHn.
    rewrite pcg_max_mkvSeq_Sn. unfold PCG.gtExp. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Nat-indexed forms of the semantic sum/max (mirror of the [Bridge_Pilot]    *)
(* [pcg_sum_mkvSeq_*] facts, needed for the Conv3d/Maxpool3d sum alignment)   *)
(* -------------------------------------------------------------------------- *)

Lemma pcg_sum_mkvSeq_0 : forall (f : fin 0 -> PCG.exp num),
  PCG.sum (PCG.mkvSeq f) = R0.
Proof.
  intro f. unfold PCG.sum, PCG.mkvSeq. simpl. reflexivity.
Qed.

(* Route-A counterpart of [OSE.to_pcg_exp_sum_nat]. *)
Lemma pcg_sum_mkvSeq_nat : forall (n : nat) (f : fin n -> PCG.exp num),
  n > 0 ->
  PCG.sum (PCG.mkvSeq f) = OSE.sumR_nat_fin (fun k Hk => f (nat2fin Hk)).
Proof.
  intros n f Hn. induction n as [| n' IHn].
  - inversion Hn.
  - destruct n' as [| n''].
    + rewrite pcg_sum_mkvSeq_Sn. rewrite pcg_sum_mkvSeq_0.
      rewrite (@OSE.sumR_nat_fin_S 0 (fun k Hk => f (nat2fin Hk))).
      assert (H0 : OSE.sumR_nat_fin
                     (fun k (Hk : k < 0) => f (nat2fin (Nat.lt_lt_succ_r k 0 Hk))) = R0).
      { unfold OSE.sumR_nat_fin. simpl. reflexivity. }
      rewrite H0. apply f_equal2; [ | reflexivity ].
      apply f_equal. apply fin_eq'. reflexivity.
    + rewrite pcg_sum_mkvSeq_Sn. rewrite IHn by lia.
      rewrite (@OSE.sumR_nat_fin_S (S n'') (fun k Hk => f (nat2fin Hk))).
      apply f_equal2.
      * apply f_equal. apply fin_eq'. reflexivity.
      * apply OSE.sumR_nat_fin_eq. intros k Hk.
        apply f_equal. apply fin_eq'. reflexivity.
Qed.

Lemma pcg_max_mkvSeq_0 : forall (f : fin 0 -> PCG.exp num),
  PCG.max (PCG.mkvSeq f) = R0.
Proof.
  intro f. unfold PCG.max, PCG.mkvSeq. simpl. reflexivity.
Qed.

(* The one-step max unfold in [Rmax] form. *)
Lemma pcg_max_mkvSeq_SnR : forall (n : nat) (f : fin (S n) -> PCG.exp num),
  PCG.max (PCG.mkvSeq f) =
  Rmax (f (ltS n)) (PCG.max (PCG.mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. rewrite pcg_max_mkvSeq_Sn. unfold PCG.gtExp.
  rewrite OSE.Rgt_dec_if_Rmax. reflexivity.
Qed.

(* Route-A counterpart of [OSE.to_pcg_exp_max_nat]. *)
Lemma pcg_max_mkvSeq_nat : forall (n : nat) (f : fin n -> PCG.exp num),
  n > 0 ->
  PCG.max (PCG.mkvSeq f) = OSE.maxR_nat_fin (fun k Hk => f (nat2fin Hk)).
Proof.
  intros n f Hn. induction n as [| n' IHn].
  - inversion Hn.
  - destruct n' as [| n''].
    + rewrite pcg_max_mkvSeq_SnR. rewrite pcg_max_mkvSeq_0.
      rewrite (@OSE.maxR_nat_fin_S 0 (fun k Hk => f (nat2fin Hk))).
      assert (H0 : OSE.maxR_nat_fin
                     (fun k (Hk : k < 0) => f (nat2fin (Nat.lt_lt_succ_r k 0 Hk))) = R0).
      { unfold OSE.maxR_nat_fin. simpl. reflexivity. }
      rewrite H0. apply f_equal2; [ | reflexivity ].
      apply f_equal. apply fin_eq'. reflexivity.
    + rewrite pcg_max_mkvSeq_SnR. rewrite IHn by lia.
      rewrite (@OSE.maxR_nat_fin_S (S n'') (fun k Hk => f (nat2fin Hk))).
      apply f_equal2.
      * apply f_equal. apply fin_eq'. reflexivity.
      * apply OSE.maxR_nat_fin_eq. intros k Hk.
        apply f_equal. apply fin_eq'. reflexivity.
Qed.

(* [idx_1d_to_2d] computes [fin2nat]-level division and modulus. *)
Lemma fin2nat_fst_idx_1d_to_2d : forall (m n : nat) (Hn : n > 0) (x : fin (m * n)),
  fin2nat (fst (V.idx_1d_to_2d x)) = fin2nat x / n.
Proof.
  intros m n Hn x. destruct n as [| n']; [inversion Hn|].
  destruct x as [i Hi]. reflexivity.
Qed.

Lemma fin2nat_snd_idx_1d_to_2d : forall (m n : nat) (Hn : n > 0) (x : fin (m * n)),
  fin2nat (snd (V.idx_1d_to_2d x)) = fin2nat x mod n.
Proof.
  intros m n Hn x. destruct n as [| n']; [inversion Hn|].
  destruct x as [i Hi]. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Linear1d                                                                   *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Linear1d : forall (m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{m} num)) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Linear w b input) rho =
  LF.Linear1d (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp b rho)
    (SEM.to_pcg_exp input rho).
Proof.
  intros m outnum w b input rho.
  unfold COP.Linear, LF.Linear1d.
  apply to_pcg_mkvSeq_ext; intro out.
  rewrite SEM.to_pcg_exp_add, SEM.to_pcg_exp_idx, to_pcg_sum_mkvSeq.
  apply f_equal2; [ | reflexivity ].
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_mul.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Theorem Bridge_Linear1d : forall (m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{m} num))
  (output : DE.acc (ary '{outnum} num)) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc b OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{outnum} num),
     SEM.exp_independent_of_acc input output') ->
  (forall output' : DE.acc (ary '{outnum} num),
     SEM.exp_independent_of_acc w output') ->
  (forall output' : DE.acc (ary '{outnum} num),
     SEM.exp_independent_of_acc b output') ->
  OSE.tmp_disjoint_from_output outnum output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.Linear1d_comm w b input output) rho =
  LI.Linear1d_comm (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp b rho)
    (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros m outnum w b input output rho Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  rewrite <- (OSE.Linear1d_sem Hi Hw Hb Hio Hwo Hbo Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_Linear1d m outnum (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp b rho)
    (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Linear1d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Softmax1d                                                                  *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Softmax1d : forall (n : nat)
  (input : DE.exp (ary '{n} num)) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Softmax1d input) rho =
  LF.Softmax1d (SEM.to_pcg_exp input rho).
Proof.
  intros n input rho.
  unfold COP.Softmax1d, LF.Softmax1d. cbv [CD.let_binding]. cbv beta.
  apply to_pcg_mkvSeq_ext; intro j.
  rewrite OSE.to_pcg_exp_div, OSE.to_pcg_exp_pExp, SEM.to_pcg_exp_idx,
    to_pcg_sum_mkvSeq.
  apply f_equal2; [ reflexivity | ].
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_pExp, SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Theorem Bridge_Softmax1d : forall (n : nat)
  (input : DE.exp (ary '{n} num))
  (output : DE.acc (ary '{n} num)) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{n} num),
     SEM.exp_independent_of_acc input output') ->
  (forall (p : path) (j : fin n),
     @PCG.in_acc num p OSE.tmp_scalar_acc -> ~ @PCG.in_acc num p (output |{ j})) ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.Softmax1d_comm input output) rho =
  LI.Softmax1d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros n input output rho Hi Hio Hdisj Hundef.
  rewrite <- (OSE.Softmax1d_sem Hi Hio output Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_Softmax1d n (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Softmax1d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool4d                                                                  *)
(*                                                                            *)
(*   route B: eval (Maxpool4d_comm) = eval (A(output, CNN_OP.Maxpool4d k e))  *)
(*     [Operators_Sem_Equiv.Maxpool4d_sem]                                    *)
(*   route A: A(output, Ops_PoolPad.Maxpool4d k e) = Maxpool4d_comm k e out   *)
(*     [Ops_PoolPad.A_Maxpool4d]                                              *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Maxpool4d : forall (batch filernum m1 m2 k : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Maxpool4d k input) rho =
  OP.Maxpool4d k (SEM.to_pcg_exp input rho).
Proof.
  intros batch filernum m1 m2 k input rho.
  unfold COP.Maxpool4d, OP.Maxpool4d.
  apply to_pcg_mkvSeq_ext; intro b.
  apply to_pcg_mkvSeq_ext; intro num.
  apply to_pcg_mkvSeq_ext; intro i0.
  apply to_pcg_mkvSeq_ext; intro i1.
  rewrite to_pcg_max_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j0.
  rewrite to_pcg_max_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j1.
  repeat rewrite SEM.to_pcg_exp_idx.
  apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
  apply f_equal2; [ reflexivity | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
Qed.

Theorem Bridge_Maxpool4d : forall (batch filernum m1 m2 k : nat)
  (Hb : batch > 0) (Hf : filernum > 0) (Hk : k > 0)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch}
    (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{batch}
     (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))),
     SEM.exp_independent_of_acc input output') ->
  OSE.tmp_disjoint_from_output_maxp4d batch filernum m1 m2 k output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.Maxpool4d_comm k input output) rho =
  OP.Maxpool4d_comm k (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch filernum m1 m2 k Hb Hf Hk input output rho Hi Hio Hdisj Hundef.
  rewrite <- (OSE.Maxpool4d_sem Hb Hf Hk Hi Hio Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (OP.A_Maxpool4d batch filernum m1 m2 k (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Maxpool4d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool3d (route A is the LeNet-5 2x2 non-overlapping window operator,     *)
(* so the bridge is at kernel size k = 2 with square m x m input)             *)
(*                                                                            *)
(*   route B: eval (Maxpool3d_comm) = eval (A(output, CNN_OP.Maxpool3d 2 e))  *)
(*     [Operators_Sem_Equiv.Maxpool3d_sem]                                    *)
(*   route A: A(output, LeNet5_Functional.Maxpool3d e) = Maxpool3d_comm e out *)
(*     [LeNet5_DPIA.A_Maxpool3d]                                              *)
(* -------------------------------------------------------------------------- *)

(* Bounds for flattening the 2x2 max window. *)
Lemma maxpool2_window_bounds : forall k, k < 2 * 2 -> (k / 2 < 2) /\ (k mod 2 < 2).
Proof.
  intros k Hk. split.
  - apply Nat.div_lt_upper_bound; lia.
  - apply Nat.mod_upper_bound; lia.
Qed.

Lemma interp_Maxpool3d : forall (channel m : nat)
  (input : DE.exp (ary '{channel} (ary '{m} (ary '{m} num)))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Maxpool3d 2 input) rho =
  LF.Maxpool3d (SEM.to_pcg_exp input rho).
Proof.
  intros channel m input rho.
  unfold COP.Maxpool3d, LF.Maxpool3d.
  apply to_pcg_mkvSeq_ext; intro c.
  apply to_pcg_mkvSeq_ext; intro i0.
  apply to_pcg_mkvSeq_ext; intro j0.
  rewrite to_pcg_max_mkvSeq.
  rewrite (pcg_max_mkvSeq_nat _ _ (Nat.lt_0_succ 1)).
  rewrite (@pcg_max_mkvSeq_nat 4 _ (Nat.lt_0_succ 3)).
  cbv beta.
  (* LHS: nested 2x2 max; RHS: flat 4-element max.  Flatten the LHS via
     [OSE.maxR_nat_fin_nested_flat']. *)
  assert (Hinner :
    OSE.maxR_nat_fin (fun k0 (Hk0 : k0 < 2) =>
      SEM.to_pcg_exp
        (CD.max (DE.mkvSeq (fun j1' : fin 2 =>
          DE.idx (DE.idx (DE.idx input c)
            (nat2fin (COP.fin_mul_add_lt_div m 2 i0 (nat2fin Hk0))))
            (nat2fin (COP.fin_mul_add_lt_div m 2 j0 j1'))))) rho) =
    OSE.maxR_nat_fin (fun k0 (Hk0 : k0 < 2) =>
      OSE.maxR_nat_fin (fun k1 (Hk1 : k1 < 2) =>
        SEM.to_pcg_exp
          (DE.idx (DE.idx (DE.idx input c)
            (nat2fin (COP.fin_mul_add_lt_div m 2 i0 (nat2fin Hk0))))
            (nat2fin (COP.fin_mul_add_lt_div m 2 j0 (nat2fin Hk1)))) rho))).
  { apply OSE.maxR_nat_fin_eq. intros k0 Hk0.
    rewrite to_pcg_max_mkvSeq.
    rewrite (pcg_max_mkvSeq_nat _ _ (Nat.lt_0_succ 1)).
    reflexivity. }
  rewrite Hinner. clear Hinner.
  assert (Hflat :
    OSE.maxR_nat_fin (fun k0 (Hk0 : k0 < 2) =>
      OSE.maxR_nat_fin (fun k1 (Hk1 : k1 < 2) =>
        SEM.to_pcg_exp
          (DE.idx (DE.idx (DE.idx input c)
            (nat2fin (COP.fin_mul_add_lt_div m 2 i0 (nat2fin Hk0))))
            (nat2fin (COP.fin_mul_add_lt_div m 2 j0 (nat2fin Hk1)))) rho)) =
    OSE.maxR_nat_fin (fun k (Hk : k < 2 * 2) =>
      SEM.to_pcg_exp
        (DE.idx (DE.idx (DE.idx input c)
          (nat2fin (COP.fin_mul_add_lt_div m 2 i0
            (nat2fin (proj1 (maxpool2_window_bounds k Hk))))))
          (nat2fin (COP.fin_mul_add_lt_div m 2 j0
            (nat2fin (proj2 (maxpool2_window_bounds k Hk)))))) rho)).
  { apply (OSE.maxR_nat_fin_nested_flat' (Nat.lt_0_succ 1) (Nat.lt_0_succ 1)
      (fun i j Hi Hj =>
        SEM.to_pcg_exp
          (DE.idx (DE.idx (DE.idx input c)
            (nat2fin (COP.fin_mul_add_lt_div m 2 i0 (nat2fin Hi))))
            (nat2fin (COP.fin_mul_add_lt_div m 2 j0 (nat2fin Hj)))) rho)
      (fun k Hk =>
        SEM.to_pcg_exp
          (DE.idx (DE.idx (DE.idx input c)
            (nat2fin (COP.fin_mul_add_lt_div m 2 i0
              (nat2fin (proj1 (maxpool2_window_bounds k Hk))))))
            (nat2fin (COP.fin_mul_add_lt_div m 2 j0
              (nat2fin (proj2 (maxpool2_window_bounds k Hk)))))) rho)
      maxpool2_window_bounds).
    - intros i j Hi1 Hi2 Hj1 Hj2.
      apply f_equal2; [ | reflexivity ].
      apply f_equal2.
      + apply f_equal2; [ reflexivity | ].
        apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity.
      + apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity.
    - intros k Hk. destruct (maxpool2_window_bounds k Hk) as [Hd Hm].
      reflexivity. }
  rewrite Hflat. clear Hflat.
  apply OSE.maxR_nat_fin_eq. intros k Hk.
  repeat rewrite SEM.to_pcg_exp_idx.
  apply f_equal2.
  - apply f_equal2; [ reflexivity | ].
    apply fin_eq'. rewrite !fin2nat_nat2fin.
    rewrite (fin2nat_fst_idx_1d_to_2d 2 2 (Nat.lt_0_succ 1) (nat2fin Hk)).
    rewrite fin2nat_nat2fin. lia.
  - apply fin_eq'. rewrite !fin2nat_nat2fin.
    rewrite (fin2nat_snd_idx_1d_to_2d 2 2 (Nat.lt_0_succ 1) (nat2fin Hk)).
    rewrite fin2nat_nat2fin. lia.
Qed.

Theorem Bridge_Maxpool3d : forall (channel m : nat)
  (Hf : channel > 0)
  (input : DE.exp (ary '{channel} (ary '{m} (ary '{m} num))))
  (output : DE.acc (ary '{channel} (ary '{m/2} (ary '{m/2} num))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{channel} (ary '{m/2} (ary '{m/2} num))),
     SEM.exp_independent_of_acc input output') ->
  OSE.tmp_disjoint_from_output_maxp3d channel m m 2 output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.Maxpool3d_comm 2 input output) rho =
  LI.Maxpool3d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros channel m Hf input output rho Hi Hio Hdisj Hundef.
  rewrite <- (OSE.Maxpool3d_sem Hf (Nat.lt_0_succ 1) Hi Hio Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_Maxpool3d channel m (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Maxpool3d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Flatten3d                                                                  *)
(*                                                                            *)
(*   route B: eval (Flatten3d_comm) = eval (A(output, CNN_OP.Flatten3d e))    *)
(*     [Operators_Sem_Equiv.Flatten3d_sem]                                    *)
(*   route A: A(output, LeNet5_Functional.Flatten3d e) = Flatten3d_comm e out *)
(*     [LeNet5_DPIA.A_Flatten3d]                                              *)
(* -------------------------------------------------------------------------- *)

(* Interpretation of a raw [V.mk_vec] (e.g. the body of [CD.join]): reads as
   the pointwise interpretation. *)
Lemma to_pcg_exp_vmk_vec : forall (n : nat) (d : data)
  (f : fin n -> DE.exp d) (rho : PCG.env),
  SEM.to_pcg_exp (d := ary '{n} d) (V.mk_vec f) rho =
  PCG.mkvSeq (fun i => SEM.to_pcg_exp (f i) rho).
Proof.
  intros n d f rho.
  cbv [SEM.to_pcg_exp]. unfold PCG.mkvSeq.
  apply V.mk_vec_ext. intro i.
  rewrite V.v_nth_mk_vec with (H := fin_proof i).
  rewrite nat2fin_fin2nat. reflexivity.
Qed.

(* Interpretation of [CD.join]: the syntactic [v_join] reads as the semantic
   [PCG.join] (both index through [idx_1d_to_2d]). *)
Lemma to_pcg_join : forall (t : data) (m n : nat)
  (e : DE.exp (ary '{m} (ary '{n} t))) (rho : PCG.env),
  SEM.to_pcg_exp (CD.join e) rho = PCG.join (SEM.to_pcg_exp e rho).
Proof.
  intros t m n e rho. unfold CD.join, V.v_join, PCG.join.
  rewrite to_pcg_exp_vmk_vec.
  apply V.mk_vec_ext; intro x. cbv beta. cbv [fle2nat fle_self].
  destruct (V.idx_1d_to_2d x) as [i j]. simpl.
  change (V.v_idx (DE.exp_default t) (V.v_nth (V.default_vec n (DE.exp_default t)) e i) j)
    with (DE.idx (DE.idx e i) j).
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Lemma interp_Flatten3d : forall (channel m1 m2 : nat)
  (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num)))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Flatten3d input) rho =
  LF.Flatten3d (SEM.to_pcg_exp input rho).
Proof.
  intros channel m1 m2 Hc Hm1 Hm2 input rho.
  unfold COP.Flatten3d, LF.Flatten3d.
  rewrite !to_pcg_join.
  unfold PCG.join.
  apply V.mk_vec_ext; intro x. cbv beta.
  destruct (V.idx_1d_to_2d x) as [i j]. simpl.
  assert (Hcm : channel * m1 > 0) by (apply Nat.mul_pos_pos; assumption).
  rewrite (PCG.idx_mkvSeq _ _ _ Hcm). cbv beta.
  destruct (V.idx_1d_to_2d i) as [i1 j1]. simpl.
  reflexivity.
Qed.

Theorem Bridge_Flatten3d : forall (channel m1 m2 : nat)
  (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{channel * m1 * m2} num)) (rho : PCG.env),
  (forall output' : DE.acc (ary '{channel * m1 * m2} num),
     SEM.exp_independent_of_acc input output') ->
  SEM.eval (CEB.Flatten3d_comm input output) rho =
  LI.Flatten3d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros channel m1 m2 Hc Hm1 Hm2 input output rho Hio.
  rewrite <- (OSE.Flatten3d_sem output rho Hc Hm1 Hm2 Hio).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_Flatten3d Hc Hm1 Hm2 (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Flatten3d; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv3d (general dimensions, stride 1, kernel k x k, padding p)             *)
(*                                                                            *)
(*   route B: eval (Conv3d_comm p 1) = eval (A(output, CNN_OP.Conv3d p 1))    *)
(*     [Operators_Sem_Equiv.Conv3d_sem]                                       *)
(*   route A: A(output, LeNet5_Functional.Conv3d Hk) = Conv3d_comm Hk ...     *)
(*     [LeNet5_DPIA.A_Conv3d]                                                 *)
(*                                                                            *)
(* The route-B output type [(m-k+2*p)/1+1] and the route-A output type        *)
(* [m+2*p-k+1] are equal by [Nat.div_1_r] + arithmetic but not convertible,   *)
(* so the bridge carries the output acceptor through the explicit cast        *)
(* [conv3d_cast_out]; at concrete instances (LeNet-5: p=2/k=5/m=28, p=0/k=5/  *)
(* m=14) the cast computes away.                                              *)
(* -------------------------------------------------------------------------- *)

(* The output-dimension arithmetic of the cast. *)
Lemma conv3d_out_eq : forall m k p, k <= m -> (m - k + 2 * p) / 1 + 1 = m + 2 * p - k + 1.
Proof. intros m k p H. rewrite Nat.div_1_r. lia. Qed.

(* Type-level equality of the two 3-D output shapes. *)
Lemma conv3d_type_eq : forall (oc oh1 ow1 oh2 ow2 : nat),
  oh1 = oh2 -> ow1 = ow2 ->
  ary '{oc} (ary '{oh1} (ary '{ow1} num)) = ary '{oc} (ary '{oh2} (ary '{ow2} num)).
Proof. intros. subst. reflexivity. Qed.

(* The output acceptor cast from the route-B shape to the route-A shape. *)
Definition conv3d_cast_out {m1 m2 k filernum p : nat}
  (Hk1 : k <= m1) (Hk2 : k <= m2)
  (output : DE.acc (ary '{filernum}
    (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))))
  : DE.acc (ary '{filernum}
    (ary '{m1 + 2 * p - k + 1} (ary '{m2 + 2 * p - k + 1} num))) :=
  eq_rect _ DE.acc output _
    (conv3d_type_eq filernum _ _ _ _
      (conv3d_out_eq m1 k p Hk1) (conv3d_out_eq m2 k p Hk2)).

(* Pointwise extensionality for 3-D semantic arrays. *)
Lemma exp3_ext : forall (n m l : nat)
  (v w : PCG.exp (ary '{n} (ary '{m} (ary '{l} num)))),
  (forall (i : fin n) (j : fin m) (k : fin l),
    PCG.idx (PCG.idx (PCG.idx v i) j) k = PCG.idx (PCG.idx (PCG.idx w i) j) k) ->
  v = w.
Proof.
  intros n m l v w H.
  rewrite <- (V.mk_vec_bij_fin _ (PCG.exp_default (ary '{m} (ary '{l} num))) v).
  rewrite <- (V.mk_vec_bij_fin _ (PCG.exp_default (ary '{m} (ary '{l} num))) w).
  f_equal. apply functional_extensionality; intro i.
  change (PCG.idx v i = PCG.idx w i).
  rewrite <- (V.mk_vec_bij_fin _ (PCG.exp_default (ary '{l} num)) (PCG.idx v i)).
  rewrite <- (V.mk_vec_bij_fin _ (PCG.exp_default (ary '{l} num)) (PCG.idx w i)).
  f_equal. apply functional_extensionality; intro j.
  change (PCG.idx (PCG.idx v i) j = PCG.idx (PCG.idx w i) j).
  rewrite <- (V.mk_vec_bij_fin _ (PCG.exp_default num) (PCG.idx (PCG.idx v i) j)).
  rewrite <- (V.mk_vec_bij_fin _ (PCG.exp_default num) (PCG.idx (PCG.idx w i) j)).
  f_equal. apply functional_extensionality; intro k.
  exact (H i j k).
Qed.

(* [PCG.idx] commutes with a type-level cast, up to [fin2nat]. *)
Lemma pcg_idx3_cast : forall (n1 m1 l1 n2 m2 l2 : nat)
  (Hn : n1 = n2) (Hm : m1 = m2) (Hl : l1 = l2)
  (H : ary '{n1} (ary '{m1} (ary '{l1} num)) = ary '{n2} (ary '{m2} (ary '{l2} num)))
  (v : PCG.exp (ary '{n1} (ary '{m1} (ary '{l1} num))))
  (i2 : fin n2) (j2 : fin m2) (k2 : fin l2)
  (i1 : fin n1) (j1 : fin m1) (k1 : fin l1),
  fin2nat i2 = fin2nat i1 -> fin2nat j2 = fin2nat j1 -> fin2nat k2 = fin2nat k1 ->
  PCG.idx (PCG.idx (PCG.idx (eq_rect _ PCG.exp v _ H) i2) j2) k2 =
  PCG.idx (PCG.idx (PCG.idx v i1) j1) k1.
Proof.
  intros n1 m1 l1 n2 m2 l2 Hn Hm Hl H v i2 j2 k2 i1 j1 k1 Hi Hj Hk.
  subst n2. subst m2. subst l2.
  assert (H = eq_refl) by apply proof_irrelevance. subst H.
  cbv [eq_rect].
  assert (i2 = i1) by (apply fin_eq'; exact Hi).
  assert (j2 = j1) by (apply fin_eq'; exact Hj).
  assert (k2 = k1) by (apply fin_eq'; exact Hk).
  subst. reflexivity.
Qed.

(* [PCG.assign] commutes with a type-level cast. *)
Lemma assign_cast : forall (d1 d2 : data) (H : d1 = d2)
  (o : PCG.acc d1) (e : PCG.exp d2),
  PCG.assign (eq_rect _ PCG.acc o _ H) e =
  PCG.assign o (eq_rect _ PCG.exp e _ (eq_sym H)).
Proof. intros. destruct H. reflexivity. Qed.

(* The body of [CNN_OP.Conv3d p 1] folded with the [Operators_Sem_Equiv]
   cell definitions so that [OSE.Conv3d_sum_flatten] applies directly. *)
Lemma conv3d_body : forall (m1 m2 k channel filernum p : nat)
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{k} (ary '{k} num)))))
  (bias : DE.exp (ary '{filernum} num))
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num)))),
  COP.Conv3d p 1 bias w input =
  DE.mkvSeq (fun num : fin filernum =>
    DE.mkvSeq (fun i0 : fin ((m1 - k + 2 * p) / 1 + 1) =>
      DE.mkvSeq (fun j0 : fin ((m2 - k + 2 * p) / 1 + 1) =>
        CD.add
          (CD.sum (DE.mkvSeq (fun c : fin channel =>
            CD.sum (DE.mkvSeq (fun i1 : fin k =>
              CD.sum (DE.mkvSeq (fun j1 : fin k =>
                OSE.Conv3d_idx_cell m1 m2 p 1 w input num i0 j0 c i1 j1)))))))
          (DE.idx bias num)))).
Proof. intros. reflexivity. Qed.

(* The route-B zero-padded read collapses to the route-A [pad_idx2d] read
   whenever the indices are inside the padded array. *)
Lemma interp_pad2d_read : forall (h w : nat)
  (e : DE.exp (ary '{h} (ary '{w} num)))
  (p t u : nat) (Ht : t < 2 * p + h) (Hu : u < 2 * p + w) (rho : PCG.env),
  SEM.to_pcg_exp (CD.safe_idx_nat (CD.safe_idx_nat (COP.Padding2d p e) t) u) rho =
  OC.pad_idx2d p (SEM.to_pcg_exp e rho) t u.
Proof.
  intros h w e p t u Ht Hu rho.
  rewrite (CD.safe_idx_nat_lt _ Hu).
  rewrite (CD.safe_idx_nat_lt _ Ht).
  unfold COP.Padding2d.
  repeat rewrite SEM.to_pcg_exp_idx.
  rewrite SEM.to_pcg_exp_mkvSeq.
  assert (Hpos1 : 2 * p + h > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ Hpos1).
  rewrite SEM.to_pcg_exp_mkvSeq.
  assert (Hpos2 : 2 * p + w > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ Hpos2).
  cbv zeta. rewrite !fin2nat_nat2fin.
  destruct (Nat.ltb_spec0 t p) as [Hlt_t | Hge_t].
  - (* top/left padding row *)
    change (DE.exp_default num) with CD.zero.
    rewrite SEM.to_pcg_exp_zero.
    unfold OC.pad_idx2d.
    destruct (Nat.leb_spec0 p t) as [Hle | Hnle]; [ exfalso; lia | reflexivity ].
  - destruct (Nat.ltb_spec0 t (p + h)) as [Hlt_t2 | Hge_t2].
    + destruct (Nat.ltb_spec0 u p) as [Hlt_u | Hge_u].
      * (* top/left padding column *)
        change (DE.exp_default num) with CD.zero.
        rewrite SEM.to_pcg_exp_zero.
        unfold OC.pad_idx2d.
        destruct (Nat.leb_spec0 p t) as [Hle | Hnle]; [ | exfalso; lia ].
        destruct (Nat.ltb_spec0 (t - p) h) as [Hth | Hth]; [ | exfalso; lia ].
        destruct (Nat.leb_spec0 p u) as [Hlu | Hnu]; [ exfalso; lia | reflexivity ].
      * destruct (Nat.ltb_spec0 u (p + w)) as [Hlt_u2 | Hge_u2].
        -- (* in-range read *)
           repeat rewrite SEM.to_pcg_exp_idx.
           unfold OC.pad_idx2d.
           destruct (Nat.leb_spec0 p t) as [Hle | Hnle]; [ | exfalso; lia ].
           destruct (Nat.ltb_spec0 (t - p) h) as [Hth | Hth]; [ | exfalso; lia ].
           destruct (Nat.leb_spec0 p u) as [Hlu | Hnu]; [ | exfalso; lia ].
           destruct (Nat.ltb_spec0 (u - p) w) as [Huw | Huw]; [ | exfalso; lia ].
           apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
           apply f_equal2; [ reflexivity | ].
           apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity.
        -- (* right/bottom padding column *)
           change (DE.exp_default num) with CD.zero.
           rewrite SEM.to_pcg_exp_zero.
           unfold OC.pad_idx2d.
           destruct (Nat.leb_spec0 p t) as [Hle | Hnle]; [ | exfalso; lia ].
           destruct (Nat.ltb_spec0 (t - p) h) as [Hth | Hth]; [ | exfalso; lia ].
           destruct (Nat.leb_spec0 p u) as [Hlu | Hnu]; [ | exfalso; lia ].
           destruct (Nat.ltb_spec0 (u - p) w) as [Huw | Huw]; [ exfalso; lia | reflexivity ].
    + (* right/bottom padding row *)
      change (DE.exp_default num) with CD.zero.
      rewrite SEM.to_pcg_exp_zero.
      unfold OC.pad_idx2d.
      destruct (Nat.leb_spec0 p t) as [Hle | Hnle]; [ | exfalso; lia ].
      destruct (Nat.ltb_spec0 (t - p) h) as [Hth | Hth]; [ exfalso; lia | reflexivity ].
Qed.

(* The 3-D version: the channel index is looked up before the padded read. *)
Lemma interp_pad3d_read : forall (h w channel : nat)
  (input : DE.exp (ary '{channel} (ary '{h} (ary '{w} num))))
  (p : nat) (c : fin channel) (Hc : channel > 0)
  (t u : nat) (Ht : t < 2 * p + h) (Hu : u < 2 * p + w) (rho : PCG.env),
  SEM.to_pcg_exp
    (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding3d p input)|[c]) t) u) rho =
  OC.pad_idx2d p (PCG.idx (SEM.to_pcg_exp input rho) c) t u.
Proof.
  intros h w channel input p c Hc t u Ht Hu rho.
  unfold COP.Padding3d.
  rewrite (DE.idx_mkvSeq _ _ _ Hc).
  rewrite (interp_pad2d_read h w (input|[c]) p t u Ht Hu rho).
  rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* Conv3d: pointwise functional interpretation lemma.  The two index sets
   [i0B]/[j0B] (route-B output shape) and [i0A]/[j0A] (route-A output shape)
   are related by [fin2nat]. *)
Lemma interp_Conv3d_cell : forall (m1 m2 k channel filernum p : nat)
  (Hk : k > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (Hc : channel > 0) (Hf : filernum > 0)
  (Hk1 : k <= m1) (Hk2 : k <= m2)
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{k} (ary '{k} num)))))
  (bias : DE.exp (ary '{filernum} num))
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (rho : PCG.env) (num : fin filernum)
  (i0B : fin ((m1 - k + 2 * p) / 1 + 1)) (j0B : fin ((m2 - k + 2 * p) / 1 + 1))
  (i0A : fin (m1 + 2 * p - k + 1)) (j0A : fin (m2 + 2 * p - k + 1)),
  fin2nat i0B = fin2nat i0A -> fin2nat j0B = fin2nat j0A ->
  PCG.idx (PCG.idx (PCG.idx
    (SEM.to_pcg_exp (COP.Conv3d p 1 bias w input) rho) num) i0B) j0B =
  PCG.idx (PCG.idx (PCG.idx
    (LF.Conv3d Hk (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho)
      (SEM.to_pcg_exp input rho)) num) i0A) j0A.
Proof.
  intros m1 m2 k channel filernum p Hk Hm1 Hm2 Hc Hf Hk1 Hk2
    w bias input rho num i0B j0B i0A j0A Hfi Hfj.
  rewrite conv3d_body.
  rewrite SEM.to_pcg_exp_mkvSeq.
  rewrite (PCG.idx_mkvSeq _ _ _ Hf).
  rewrite SEM.to_pcg_exp_mkvSeq.
  assert (Hoh : (m1 - k + 2 * p) / 1 + 1 > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ Hoh).
  rewrite SEM.to_pcg_exp_mkvSeq.
  assert (How : (m2 - k + 2 * p) / 1 + 1 > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ How).
  unfold LF.Conv3d.
  rewrite (PCG.idx_mkvSeq _ _ _ Hf).
  assert (HohA : m1 + 2 * p - k + 1 > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ HohA).
  assert (HowA : m2 + 2 * p - k + 1 > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ HowA).
  unfold LF.Conv3dCell.
  rewrite SEM.to_pcg_exp_add, SEM.to_pcg_exp_idx.
  apply f_equal2; [ | reflexivity ].
  (* sum alignment: route-B nested sums = route-A flat sum *)
  assert (Hflat :
    SEM.to_pcg_exp
      (CD.sum (DE.mkvSeq (fun c : fin channel =>
        CD.sum (DE.mkvSeq (fun i1 : fin k =>
          CD.sum (DE.mkvSeq (fun j1 : fin k =>
            OSE.Conv3d_idx_cell m1 m2 p 1 w input num i0B j0B c i1 j1))))))) rho =
    SEM.to_pcg_exp
      (CD.sum (DE.mkvSeq
        (OSE.Conv3d_flat_cell m1 m2 k k channel p 1 w input num i0B j0B))) rho).
  { apply (OSE.Conv3d_sum_flatten p w input); lia. }
  rewrite Hflat.
  assert (Hn : channel * k * k > 0) by nia.
  rewrite (OSE.to_pcg_exp_sum_nat _ rho Hn).
  rewrite (pcg_sum_mkvSeq_nat _ _ Hn).
  apply OSE.sumR_nat_fin_eq. intros kk Hkk. cbv beta.
  unfold OSE.Conv3d_flat_cell. cbv zeta.
  rewrite OSE.to_pcg_exp_mul.
  rewrite !Nat.mul_1_r.
  apply f_equal2.
  - (* padded input cell *)
    pose proof (LU.conv_flat_di_bound (nat2fin Hkk) Hk) as Hdi.
    pose proof (LU.conv_flat_dj_bound (nat2fin Hkk) Hk) as Hdj.
    rewrite fin2nat_nat2fin in Hdi, Hdj.
    pose proof (fin_proof i0B) as Hi0.
    pose proof (fin_proof j0B) as Hj0.
    assert (Hle1 : (m1 - k + 2 * p) / 1 + 1 <= m1 + 2 * p - k + 1)
      by (rewrite Nat.div_1_r; lia).
    assert (Hle2 : (m2 - k + 2 * p) / 1 + 1 <= m2 + 2 * p - k + 1)
      by (rewrite Nat.div_1_r; lia).
    change (fin2nat (nat2fin Hkk)) with kk.
    rewrite (interp_pad3d_read m1 m2 channel input p
      (@nat2fin channel (Nat.div kk (k * k)) (CEO.conv3d_flat_c_bound (nat2fin Hkk))) Hc
      (fin2nat i0B + Nat.div (Nat.modulo kk (k * k)) k)
      (fin2nat j0B + Nat.modulo kk k)
      ltac:(lia) ltac:(lia) rho).
    assert (Hcfin : @nat2fin channel (Nat.div kk (k * k))
                      (CEO.conv3d_flat_c_bound (nat2fin Hkk)) =
                    nat2fin (LU.conv_flat_c_bound (nat2fin Hkk) Hk)).
    { apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity. }
    rewrite Hcfin, Hfi, Hfj.
    reflexivity.
  - (* kernel cell *)
    repeat rewrite SEM.to_pcg_exp_idx.
    apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
    apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
    apply f_equal2; [ reflexivity | ].
    apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity.
Qed.

(* Conv3d: functional interpretation lemma (cast form). *)
Lemma interp_Conv3d : forall (m1 m2 k channel filernum p : nat)
  (Hk : k > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (Hc : channel > 0) (Hf : filernum > 0)
  (Hk1 : k <= m1) (Hk2 : k <= m2)
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{k} (ary '{k} num)))))
  (bias : DE.exp (ary '{filernum} num))
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (rho : PCG.env)
  (Hdims : ary '{filernum}
             (ary '{m1 + 2 * p - k + 1} (ary '{m2 + 2 * p - k + 1} num)) =
           ary '{filernum}
             (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))),
  eq_rect _ PCG.exp
    (LF.Conv3d Hk (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho)
      (SEM.to_pcg_exp input rho)) _ Hdims =
  SEM.to_pcg_exp (COP.Conv3d p 1 bias w input) rho.
Proof.
  intros m1 m2 k channel filernum p Hk Hm1 Hm2 Hc Hf Hk1 Hk2
    w bias input rho Hdims.
  apply exp3_ext. intros num i0 j0.
  assert (Hoh : (m1 - k + 2 * p) / 1 + 1 = m1 + 2 * p - k + 1)
    by (rewrite Nat.div_1_r; lia).
  assert (How : (m2 - k + 2 * p) / 1 + 1 = m2 + 2 * p - k + 1)
    by (rewrite Nat.div_1_r; lia).
  assert (Hi0 : fin2nat i0 < m1 + 2 * p - k + 1).
  { pose proof (fin_proof i0) as Hi. lia. }
  assert (Hj0 : fin2nat j0 < m2 + 2 * p - k + 1).
  { pose proof (fin_proof j0) as Hj. lia. }
  rewrite (pcg_idx3_cast filernum (m1 + 2 * p - k + 1) (m2 + 2 * p - k + 1)
    filernum ((m1 - k + 2 * p) / 1 + 1) ((m2 - k + 2 * p) / 1 + 1)
    eq_refl (eq_sym Hoh) (eq_sym How) Hdims
    (LF.Conv3d Hk (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho)
      (SEM.to_pcg_exp input rho))
    num i0 j0 num (nat2fin Hi0) (nat2fin Hj0)
    eq_refl (eq_sym (fin2nat_nat2fin Hi0)) (eq_sym (fin2nat_nat2fin Hj0))).
  symmetry.
  apply (interp_Conv3d_cell m1 m2 k channel filernum p
    Hk Hm1 Hm2 Hc Hf Hk1 Hk2 w bias input rho num i0 j0 (nat2fin Hi0) (nat2fin Hj0)
    (eq_sym (fin2nat_nat2fin Hi0)) (eq_sym (fin2nat_nat2fin Hj0))).
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv3d: comm-level bridge                                                  *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Conv3d : forall (m1 m2 k channel filernum p : nat)
  (Hk : k > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (Hc : channel > 0) (Hf : filernum > 0)
  (Hk1 : k <= m1) (Hk2 : k <= m2)
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{k} (ary '{k} num)))))
  (bias : DE.exp (ary '{filernum} num))
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{filernum}
    (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc bias OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{filernum}
     (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))),
     SEM.exp_independent_of_acc input output') ->
  (forall output' : DE.acc (ary '{filernum}
     (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))),
     SEM.exp_independent_of_acc w output') ->
  (forall output' : DE.acc (ary '{filernum}
     (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))),
     SEM.exp_independent_of_acc bias output') ->
  OSE.tmp_disjoint_from_output_conv3d m1 m2 k k filernum p 1 output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.Conv3d_comm p 1 bias w input output) rho =
  LI.Conv3d_comm Hk (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho)
    (SEM.to_pcg_exp input rho) (conv3d_cast_out Hk1 Hk2 output) rho.
Proof.
  intros m1 m2 k channel filernum p Hk Hm1 Hm2 Hc Hf Hk1 Hk2
    w bias input output rho Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  assert (Hoh_pos : (m1 - k + 2 * p) / 1 + 1 > 0) by lia.
  assert (How_pos : (m2 - k + 2 * p) / 1 + 1 > 0) by lia.
  rewrite <- (OSE.Conv3d_sem Hm1 Hm2 Hk Hk Hc Hf (Nat.lt_0_succ 0)
    Hoh_pos How_pos Hi Hw Hb Hio Hwo Hbo Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_Conv3d m1 m2 channel filernum p Hk
    (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho) (SEM.to_pcg_exp input rho)
    (conv3d_cast_out Hk1 Hk2 output)).
  cbv [DR.A].
  unfold conv3d_cast_out.
  rewrite assign_cast.
  do 2 f_equal.
  symmetry.
  apply interp_Conv3d; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions Bridge_Linear1d.
Print Assumptions Bridge_Softmax1d.
Print Assumptions Bridge_Maxpool4d.
Print Assumptions Bridge_Maxpool3d.
Print Assumptions Bridge_Flatten3d.
Print Assumptions Bridge_Conv3d.
