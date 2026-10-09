(* ========================================================================= *)
(* Bridge_Pilot.v                                                            *)
(*                                                                           *)
(* Pilot for the route-A/route-B bridge:                                     *)
(*                                                                           *)
(*   route B (code generation): AST commands [CNN_CodeGen_Core.comm] with    *)
(*     denotation [CNN_CodeGen_Semantics.eval : CG.comm -> PCG.comm],        *)
(*     operator-wise equivalences [Operators_Sem_Equiv] relating             *)
(*     [eval (AST op)] to [eval (A(output, CNN_OP.op ...))];                 *)
(*   route A (DPIA): semantic commands [Proof_CodeGen.comm = env -> env]     *)
(*     with Leibniz rules [DPIA_Rules], operator-wise equalities             *)
(*     [LeNet5_DPIA.A_<op> : A(output, LeNet5_Functional.op ...) = op_comm]. *)
(*                                                                           *)
(* Both routes share the semantic domain [Proof_CodeGen.comm].  The only     *)
(* missing middle link is an interpretation lemma for the functional layer:  *)
(*                                                                           *)
(*   to_pcg_exp (CNN_OP.op e) rho  =  LeNet5_Functional.op (to_pcg_exp e rho)*)
(*                                                                           *)
(* This file proves that link for ReLU3d (fully general) and for Conv3d      *)
(* (the LeNet-5 C3 instance: 6->16 channels, 14x14 input, 5x5 kernel,        *)
(* padding 0, stride 1), and assembles the comm-level bridge theorems        *)
(*                                                                           *)
(*   eval (relu3d_AST) rho      = ReLU3d_comm (to_pcg_exp input rho) out rho *)
(*   eval (conv3d_C3_AST) rho   = Conv3d_comm ... (to_pcg_exp ...) rho       *)
(*                                                                           *)
(* For padding p > 0 both routes now agree: route A's [Conv3d] zero-pads
   through [Ops_Conv.pad_idx2d] (bool boundary tests, out-of-range reads
   [zero]), matching route B's [Padding2d].  The earlier clamping semantics
   (nat-truncated [i0 + di - p] reading the edge value) was removed; the
   lemmas [routeA_pad_zero] and [routeB_pad_zero] at the end witness that
   both routes read zero at padded positions.                              *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

From Stdlib Require Import Reals String Arith Lia Bool.
Require Import Ionia.finType Ionia.vector Ionia.DataExp Ionia.CNN_Defs
  Ionia.CNN_CodeGen_Core Ionia.Proof_CodeGen Ionia.DPIA_Rules
  Ionia.CNN_CodeGen_Semantics Ionia.CNN_Examples_Base
  Ionia.CNN_Examples_Base_Ops Ionia.CNN_OP Ionia.Operators_Sem_Equiv
  Ionia.LeNet5_Utils Ionia.LeNet5_Functional Ionia.LeNet5_Imperative
  Ionia.LeNet5_DPIA.

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
Module V := Ionia.vector.

(* Variable lookup used by [SEM.to_pcg_exp] and [SEM.eval]. *)
Definition env_val (rho : PCG.env) (s : string) : R :=
  match rho (DE.Var s) with Some r => r | None => R0 end.

(* -------------------------------------------------------------------------- *)
(* Generic interpretation helpers                                             *)
(* -------------------------------------------------------------------------- *)

(* Runtime evaluation of a static [<=] test agrees with the semantic [leExp]
   on the interpreted operands.  Mirror of [SEM.to_pcg_exp_BGt]. *)
Lemma to_pcg_exp_BLe : forall (x y : DE.exp num) (rho : PCG.env),
  DE.eval_bexp (env_val rho) (CD.leExp x y) =
  PCG.leExp (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho).
Proof.
  intros x y rho. cbv [SEM.to_pcg_exp CD.leExp env_val PCG.leExp].
  simpl. reflexivity.
Qed.

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
(* ReLU3d: functional interpretation lemma                                    *)
(* -------------------------------------------------------------------------- *)

Lemma interp_ReLU3d : forall (filernum m1 m2 : nat)
  (input : DE.exp (ary '{filernum} (ary '{m1} (ary '{m2} num)))) (rho : PCG.env),
  (forall (c : fin filernum) (i0 : fin m1) (i1 : fin m2),
     DE.eval_bexp (env_val rho)
       (CD.leExp (DE.idx (DE.idx (DE.idx input c) i0) i1) CD.zero) =
     DE.bexp2bool
       (CD.leExp (DE.idx (DE.idx (DE.idx input c) i0) i1) CD.zero)) ->
  SEM.to_pcg_exp (COP.ReLU3d input) rho =
  LF.ReLU3d (SEM.to_pcg_exp input rho).
Proof.
  intros filernum m1 m2 input rho Hb.
  unfold COP.ReLU3d, LF.ReLU3d.
  apply to_pcg_mkvSeq_ext; intro c.
  apply to_pcg_mkvSeq_ext; intro i0.
  apply to_pcg_mkvSeq_ext; intro i1.
  rewrite <- (Hb c i0 i1).
  remember (DE.eval_bexp (env_val rho)
              (CD.leExp (DE.idx (DE.idx (DE.idx input c) i0) i1) CD.zero)) as b eqn:E.
  rewrite to_pcg_exp_BLe in E.
  rewrite SEM.to_pcg_exp_zero in E.
  repeat rewrite SEM.to_pcg_exp_idx in E.
  unfold PCG.zero.
  destruct b; rewrite <- E.
  - reflexivity.
  - repeat rewrite SEM.to_pcg_exp_idx. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* ReLU3d: comm-level bridge                                                  *)
(*                                                                            *)
(*   route B: eval (ReLU3d_comm_AST) = eval (A(output, CNN_OP.ReLU3d input))  *)
(*     [CNN_Examples_Base.ReLU3d_equiv_sem]                                   *)
(*   route A: A(output, LeNet5_Functional.ReLU3d e) = ReLU3d_comm e output    *)
(*     [LeNet5_DPIA.A_ReLU3d]                                                 *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_ReLU3d : forall (filernum m1 m2 : nat)
  (input : DE.exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input output ->
  (forall (c : fin filernum) (i0 : fin m1) (i1 : fin m2),
     DE.eval_bexp (env_val rho)
       (CD.leExp (DE.idx (DE.idx (DE.idx input c) i0) i1) CD.zero) =
     DE.bexp2bool
       (CD.leExp (DE.idx (DE.idx (DE.idx input c) i0) i1) CD.zero)) ->
  SEM.eval (CEB.ReLU3d_comm input output) rho =
  LI.ReLU3d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros filernum m1 m2 input output rho Hindep Hb.
  rewrite <- (CEB.ReLU3d_equiv_sem rho Hindep Hb).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_ReLU3d filernum m1 m2 (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_ReLU3d.
  exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv3d: semantic sum facts on the route-A (PCG) side                       *)
(* -------------------------------------------------------------------------- *)

Lemma pcg_sum_mkvSeq_0 : forall (f : fin 0 -> PCG.exp num),
  PCG.sum (PCG.mkvSeq f) = R0.
Proof.
  intro f. unfold PCG.sum, PCG.mkvSeq. simpl. reflexivity.
Qed.

Lemma pcg_sum_mkvSeq_Sn : forall (n : nat) (f : fin (S n) -> PCG.exp num),
  PCG.sum (PCG.mkvSeq f) =
  Rplus (f (ltS n)) (PCG.sum (PCG.mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold PCG.sum, PCG.mkvSeq. rewrite V.mk_vec_Sn. simpl. reflexivity.
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

(* -------------------------------------------------------------------------- *)
(* Conv3d (LeNet-5 C3 instance: 6->16 channels, 14x14, 5x5 kernel, p=0, s=1)  *)
(* -------------------------------------------------------------------------- *)

(* The body of [CNN_OP.Conv3d 0 1] at the C3 size, folded with the
   [Operators_Sem_Equiv] cell definitions so that [OSE.Conv3d_sum_flatten]
   applies directly. *)
Lemma conv3d_C3_body : forall
  (w : DE.exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (bias : DE.exp (ary '{16} num))
  (input : DE.exp (ary '{6} (ary '{14} (ary '{14} num)))),
  COP.Conv3d 0 1 bias w input =
  DE.mkvSeq (fun num : fin 16 =>
    DE.mkvSeq (fun i0 : fin 10 =>
      DE.mkvSeq (fun j0 : fin 10 =>
        CD.add
          (CD.sum (DE.mkvSeq (fun c : fin 6 =>
            CD.sum (DE.mkvSeq (fun i1 : fin 5 =>
              CD.sum (DE.mkvSeq (fun j1 : fin 5 =>
                OSE.Conv3d_idx_cell 14 14 0 1 w input num i0 j0 c i1 j1)))))))
          (DE.idx bias num)))).
Proof. intros. reflexivity. Qed.

(* At padding 0 the route-B padded read collapses to the route-A safe read
   whenever the indices are in bounds. *)
Lemma interp_pad0_cell : forall
  (input : DE.exp (ary '{6} (ary '{14} (ary '{14} num))))
  (ci : nat) (Hc : ci < 6) (t u : nat) (Ht : t < 14) (Hu : u < 14) (rho : PCG.env),
  SEM.to_pcg_exp
    (CD.safe_idx_nat
      (CD.safe_idx_nat (DE.idx (COP.Padding3d 0 input) (nat2fin Hc)) t) u) rho =
  LU.safe_idx2d (PCG.idx (SEM.to_pcg_exp input rho) (nat2fin Hc)) t u.
Proof.
  intros input ci Hc t u Ht Hu rho.
  rewrite (CD.safe_idx_nat_lt _ Hu).
  rewrite (CD.safe_idx_nat_lt _ Ht).
  repeat rewrite SEM.to_pcg_exp_idx.
  unfold COP.Padding3d.
  rewrite SEM.to_pcg_exp_mkvSeq.
  rewrite (PCG.idx_mkvSeq _ _ _ (Nat.lt_0_succ _)).
  unfold COP.Padding2d.
  rewrite SEM.to_pcg_exp_mkvSeq.
  rewrite (PCG.idx_mkvSeq _ _ _ (Nat.lt_0_succ 13)).
  rewrite SEM.to_pcg_exp_mkvSeq.
  rewrite (PCG.idx_mkvSeq _ _ _ (Nat.lt_0_succ 13)).
  cbv zeta.
  rewrite !fin2nat_nat2fin.
  destruct (Nat.ltb_spec0 t 0) as [Habs | Hge_i]; [exfalso; lia |].
  destruct (Nat.ltb_spec0 t (0 + 14)) as [Hlt_i | Habs]; [ | exfalso; lia].
  destruct (Nat.ltb_spec0 u 0) as [Habs | Hge_j]; [exfalso; lia |].
  destruct (Nat.ltb_spec0 u (0 + 14)) as [Hlt_j | Habs]; [ | exfalso; lia].
  repeat rewrite SEM.to_pcg_exp_idx.
  unfold LU.safe_idx2d.
  destruct (Nat.ltb_spec0 t 14) as [Hi | Habs]; [ | exfalso; lia].
  destruct (Nat.ltb_spec0 u 14) as [Hj | Habs]; [ | exfalso; lia].
  f_equal; [ | apply fin_eq'; rewrite !fin2nat_nat2fin, Nat.sub_0_r; reflexivity ].
  f_equal; apply fin_eq'; rewrite !fin2nat_nat2fin, Nat.sub_0_r; reflexivity.
Qed.

(* At padding 0 the zero-padding read [pad_idx2d] collapses to the plain
   bound-checked read [safe_idx2d]. *)
Lemma safe_idx2d_eq_pad_idx2d_0 : forall (h w : nat)
  (img : PCG.exp (ary '{h} (ary '{w} num))) (t u : nat),
  LU.safe_idx2d img t u = OC.pad_idx2d 0 img t u.
Proof.
  intros h w img t u. unfold LU.safe_idx2d, OC.pad_idx2d.
  rewrite !Nat.sub_0_r.
  destruct (Nat.leb_spec0 0 t) as [_ | Habs]; [ | exfalso; lia].
  destruct (Nat.leb_spec0 0 u) as [_ | Habs]; [ | exfalso; lia].
  destruct (Nat.ltb_spec0 t h) as [Ht | Ht];
  destruct (Nat.ltb_spec0 u w) as [Hu | Hu];
  try reflexivity;
  f_equal; apply fin_eq'; reflexivity.
Qed.

(* Conv3d: functional interpretation lemma at the C3 instance. *)
Lemma interp_Conv3d_C3 : forall
  (w : DE.exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (bias : DE.exp (ary '{16} num))
  (input : DE.exp (ary '{6} (ary '{14} (ary '{14} num))))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Conv3d 0 1 bias w input) rho =
  LF.Conv3d (p:=0) LF.H5 (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho)
    (SEM.to_pcg_exp input rho).
Proof.
  intros w bias input rho.
  rewrite conv3d_C3_body.
  unfold LF.Conv3d, LF.Conv3dCell.
  apply to_pcg_mkvSeq_ext; intro cout.
  apply to_pcg_mkvSeq_ext; intro i0.
  apply to_pcg_mkvSeq_ext; intro j0.
  rewrite SEM.to_pcg_exp_add.
  rewrite SEM.to_pcg_exp_idx.
  unfold PCG.add.
  apply f_equal2; cycle 1.
  - reflexivity.
  - (* sum alignment: route-B nested sums = route-A flat sum *)
    assert (Hflat :
      SEM.to_pcg_exp
        (CD.sum (DE.mkvSeq (fun c : fin 6 =>
          CD.sum (DE.mkvSeq (fun i1 : fin 5 =>
            CD.sum (DE.mkvSeq (fun j1 : fin 5 =>
              OSE.Conv3d_idx_cell 14 14 0 1 w input cout i0 j0 c i1 j1))))))) rho =
      SEM.to_pcg_exp
        (CD.sum (DE.mkvSeq
          (OSE.Conv3d_flat_cell 14 14 5 5 6 0 1 w input cout i0 j0))) rho).
    { apply (OSE.Conv3d_sum_flatten 0 w input); lia. }
    rewrite Hflat.
    assert (H150 : 6 * 5 * 5 > 0) by lia.
    rewrite (OSE.to_pcg_exp_sum_nat _ rho H150).
    rewrite (pcg_sum_mkvSeq_nat _ _ H150).
    apply OSE.sumR_nat_fin_eq. intros k Hk.
    unfold OSE.Conv3d_flat_cell. cbv zeta.
    rewrite OSE.to_pcg_exp_mul.
    rewrite !Nat.mul_1_r.
    unfold PCG.mul.
    apply f_equal2.
    + (* padded input cell vs safe_idx2d *)
      assert (Hdi : Nat.div (Nat.modulo (fin2nat (nat2fin Hk)) (5 * 5)) 5 < 5)
        by apply (LU.conv_flat_di_bound (nat2fin Hk) LF.H5).
      assert (Hdj : Nat.modulo (fin2nat (nat2fin Hk)) 5 < 5)
        by apply (LU.conv_flat_dj_bound (nat2fin Hk) LF.H5).
      assert (Ht : fin2nat i0 + Nat.div (Nat.modulo (fin2nat (nat2fin Hk)) (5 * 5)) 5 < 14)
        by (pose proof (fin_proof i0); lia).
      assert (Hu : fin2nat j0 + Nat.modulo (fin2nat (nat2fin Hk)) 5 < 14)
        by (pose proof (fin_proof j0); lia).
      transitivity
        (LU.safe_idx2d
          (PCG.idx (SEM.to_pcg_exp input rho)
            (nat2fin (CEO.conv3d_flat_c_bound (nat2fin Hk))))
          (fin2nat i0 + Nat.div (Nat.modulo (fin2nat (nat2fin Hk)) (5 * 5)) 5)
          (fin2nat j0 + Nat.modulo (fin2nat (nat2fin Hk)) 5)).
      * apply (interp_pad0_cell input _ (CEO.conv3d_flat_c_bound (nat2fin Hk)) _ _ Ht Hu rho).
      * assert (Hcfin : nat2fin (CEO.conv3d_flat_c_bound (nat2fin Hk)) =
                        nat2fin (LU.conv_flat_c_bound (nat2fin Hk) LF.H5)).
        { apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity. }
        rewrite Hcfin. apply safe_idx2d_eq_pad_idx2d_0.
    + (* kernel cell *)
      repeat rewrite SEM.to_pcg_exp_idx.
      assert (HA1 : nat2fin (CEO.conv3d_flat_c_bound (nat2fin Hk)) =
                    nat2fin (LU.conv_flat_c_bound (nat2fin Hk) LF.H5)).
      { apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity. }
      assert (HA2 : nat2fin (CEO.conv3d_flat_i1_bound (nat2fin Hk)) =
                    nat2fin (LU.conv_flat_di_bound (nat2fin Hk) LF.H5)).
      { apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity. }
      assert (HA3 : nat2fin (CEO.conv3d_flat_j1_bound (nat2fin Hk)) =
                    nat2fin (LU.conv_flat_dj_bound (nat2fin Hk) LF.H5)).
      { apply fin_eq'. rewrite !fin2nat_nat2fin. reflexivity. }
      rewrite HA1, HA2, HA3. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv3d: comm-level bridge at the C3 instance                               *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Conv3d_C3 : forall
  (w : DE.exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (bias : DE.exp (ary '{16} num))
  (input : DE.exp (ary '{6} (ary '{14} (ary '{14} num))))
  (output : DE.acc (ary '{16} (ary '{10} (ary '{10} num))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc bias OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{16} (ary '{10} (ary '{10} num))),
     SEM.exp_independent_of_acc input output') ->
  (forall output' : DE.acc (ary '{16} (ary '{10} (ary '{10} num))),
     SEM.exp_independent_of_acc w output') ->
  (forall output' : DE.acc (ary '{16} (ary '{10} (ary '{10} num))),
     SEM.exp_independent_of_acc bias output') ->
  OSE.tmp_disjoint_from_output_conv3d 14 14 5 5 16 0 1 output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.Conv3d_comm 0 1 bias w input output) rho =
  LI.Conv3d_comm (p:=0) LF.H5 (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho)
    (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros w bias input output rho Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  rewrite <- (OSE.Conv3d_sem (m1:=14) (m2:=14) (n1:=5) (n2:=5)
    (channel:=6) (filernum:=16) (p:=0) (s:=1) (w:=w) (bias:=bias) (input:=input)
    (output:=output) (rho:=rho)
    (Nat.lt_0_succ 13) (Nat.lt_0_succ 13) (Nat.lt_0_succ 4) (Nat.lt_0_succ 4)
    (Nat.lt_0_succ 5) (Nat.lt_0_succ 15) (Nat.lt_0_succ 0)
    (Nat.lt_0_succ 9) (Nat.lt_0_succ 9)
    Hi Hw Hb Hio Hwo Hbo Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (LD.A_Conv3d 14 14 6 16 0 LF.H5
    (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp bias rho) (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Conv3d_C3.
Qed.

(* -------------------------------------------------------------------------- *)
(* Padding p > 0: both routes zero-pad                                        *)
(*                                                                            *)
(* Route A's [Conv3d] reads padded positions through [OC.pad_idx2d] (bool    *)
(* boundary tests, out-of-range read [zero]); route B's [Padding2d] yields   *)
(* [exp_default] (zero) there.  The earlier clamping semantics of route A    *)
(* (nat-truncated [i0 + di - p] reading the edge value) was removed.         *)
(* -------------------------------------------------------------------------- *)

(* Route A zero-pads: the padded position (0,0) of a 2-padded window reads
   [zero]. *)
Lemma routeA_pad_zero : forall (img : PCG.exp (ary '{28} (ary '{28} num))),
  OC.pad_idx2d 2 img (0 + 0) (0 + 0) = PCG.zero.
Proof.
  intro img. unfold OC.pad_idx2d.
  destruct (Nat.leb_spec0 2 (0 + 0)) as [Habs | _]; [exfalso; lia |].
  reflexivity.
Qed.

(* Route B zero-pads: position (0,0) of the 2-padded array is the default. *)
Lemma routeB_pad_zero : forall (e : DE.exp (ary '{28} (ary '{28} num)))
  (i j : fin (2 * 2 + 28)),
  fin2nat i = 0 -> fin2nat j = 0 ->
  DE.idx (DE.idx (COP.Padding2d 2 e) i) j = DE.exp_default num.
Proof.
  intros e i j Hi Hj.
  unfold COP.Padding2d.
  rewrite (DE.idx_mkvSeq _ _ _ (Nat.lt_0_succ 31)).
  rewrite (DE.idx_mkvSeq _ _ _ (Nat.lt_0_succ 31)).
  cbv zeta.
  rewrite Hi, Hj.
  destruct (Nat.ltb_spec0 0 2) as [_ | Habs]; [ | exfalso; lia].
  reflexivity.
Qed.

Print Assumptions Bridge_ReLU3d.
Print Assumptions Bridge_Conv3d_C3.
