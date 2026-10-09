(* ========================================================================= *)
(* Bridge_Elementwise.v                                                      *)
(*                                                                           *)
(* Route-A/route-B bridge for the pointwise (elementwise) batch, following   *)
(* the pattern of [Ionia.Bridge_Pilot]:                                      *)
(*                                                                           *)
(*   route B (code generation): AST commands [CNN_CodeGen_Core.comm] with    *)
(*     denotation [CNN_CodeGen_Semantics.eval] and operator-wise semantic    *)
(*     equivalences [* _equiv_sem];                                          *)
(*   route A (DPIA): semantic commands [Proof_CodeGen.comm] with the         *)
(*     operator-wise Leibniz equalities [Ops_Elementwise.A_<op>].            *)
(*                                                                           *)
(* For each operator we prove                                                *)
(*   (1) a functional interpretation lemma                                   *)
(*         to_pcg_exp (CNN_OP.op e) rho = Ops_Elementwise.op (to_pcg_exp e rho) *)
(*   (2) the comm-level bridge                                               *)
(*         eval (AST op_comm) rho = op_comm (to_pcg_exp e rho) output rho    *)
(*                                                                           *)
(* Coverage: route B only ships AST versions (with a proved [* _equiv_sem],  *)
(* or an AST [*_comm] we can prove one for locally) for 4 of the 15          *)
(* elementwise operators of [Ops_Elementwise]:                               *)
(*   ReLU4d   [CNN_Examples_Base_Ops.ReLU4d_equiv_sem]                       *)
(*   Add4d    [CNN_Examples_Base.Add4d_equiv_sem]                            *)
(*   Mul2d    [CNN_Examples_LeNet5.Mul2d_equiv_sem]                          *)
(*   Add2d    [CNN_Examples_Base.Add2d_comm, no equiv_sem -> proved locally] *)
(*                                                                           *)
(* The remaining 11 route-A operators have NO route-B AST counterpart        *)
(* (only 1-D or functional forms exist) and are therefore NOT bridged here:  *)
(*   Sigmoid2d Sigmoid4d Tanh2d Tanh4d LeakyReLU4d Sub2d Add3d               *)
(*   Addc2d Mulc2d Exp2d Fill2d                                              *)
(* (CNN_Examples_LeNet5 only provides Sigmoid1d/Tanh1d/LeakyReLU1d, whose    *)
(* arity matches no route-A operator; CNN_Model uses the functional forms    *)
(* of Sigmoid2d/Tanh2d/etc. but defines no AST [*_comm] for them.)           *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* It deliberately avoids importing LeNet5_Functional/Imperative/DPIA: the   *)
(* route-A side here is [Ops_Elementwise], which is self-contained.          *)
(* ========================================================================= *)

From Stdlib Require Import Reals String Arith Lia Bool.
Require Import Ionia.finType Ionia.vector Ionia.DataExp Ionia.CNN_Defs
  Ionia.CNN_CodeGen_Core Ionia.Proof_CodeGen Ionia.DPIA_Rules
  Ionia.CNN_CodeGen Ionia.CNN_CodeGen_Semantics
  Ionia.CNN_Examples_Base Ionia.CNN_Examples_Base_Ops
  Ionia.CNN_Examples_LeNet5 Ionia.CNN_OP Ionia.Operators_Sem_Equiv
  Ionia.Ops_Elementwise.

Module DE := Ionia.DataExp.
Module CD := Ionia.CNN_Defs.
Module CG := Ionia.CNN_CodeGen_Core.
Module CCG := Ionia.CNN_CodeGen.
Module PCG := Ionia.Proof_CodeGen.
Module DR := Ionia.DPIA_Rules.
Module SEM := Ionia.CNN_CodeGen_Semantics.
Module CEB := Ionia.CNN_Examples_Base.
Module CEO := Ionia.CNN_Examples_Base_Ops.
Module CEL := Ionia.CNN_Examples_LeNet5.
Module COP := Ionia.CNN_OP.
Module OSE := Ionia.Operators_Sem_Equiv.
Module OE := Ionia.Ops_Elementwise.
Module V := Ionia.vector.

(* Variable lookup used by [SEM.to_pcg_exp] and [SEM.eval].
   (Local copy of the helper in [Bridge_Pilot], which is not imported.) *)
Definition env_val (rho : PCG.env) (s : string) : R :=
  match rho (DE.Var s) with Some r => r | None => R0 end.

(* -------------------------------------------------------------------------- *)
(* Generic interpretation helpers (mirrors of the [Bridge_Pilot] helpers)     *)
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
(* ReLU4d: functional interpretation lemma                                    *)
(* -------------------------------------------------------------------------- *)

Lemma interp_ReLU4d : forall (batch channel m1 m2 : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  (forall (b : fin batch) (c : fin channel) (i0 : fin m1) (i1 : fin m2),
     DE.eval_bexp (env_val rho)
       (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx input b) c) i0) i1) CD.zero) =
     DE.bexp2bool
       (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx input b) c) i0) i1) CD.zero)) ->
  SEM.to_pcg_exp (COP.ReLU4d input) rho =
  OE.ReLU4d (SEM.to_pcg_exp input rho).
Proof.
  intros batch channel m1 m2 input rho Hb.
  unfold COP.ReLU4d, OE.ReLU4d.
  apply to_pcg_mkvSeq_ext; intro b.
  apply to_pcg_mkvSeq_ext; intro c.
  apply to_pcg_mkvSeq_ext; intro i0.
  apply to_pcg_mkvSeq_ext; intro i1.
  rewrite <- (Hb b c i0 i1).
  remember (DE.eval_bexp (env_val rho)
              (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx input b) c) i0) i1)
                 CD.zero)) as bcond eqn:E.
  rewrite to_pcg_exp_BLe in E.
  rewrite SEM.to_pcg_exp_zero in E.
  repeat rewrite SEM.to_pcg_exp_idx in E.
  unfold PCG.zero.
  destruct bcond; rewrite <- E.
  - reflexivity.
  - repeat rewrite SEM.to_pcg_exp_idx. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* ReLU4d: comm-level bridge                                                  *)
(*                                                                            *)
(*   route B: eval (ReLU4d_comm) = eval (A(output, CNN_OP.ReLU4d input))      *)
(*     [CNN_Examples_Base_Ops.ReLU4d_equiv_sem]                               *)
(*   route A: A(output, Ops_Elementwise.ReLU4d e) = ReLU4d_comm e output      *)
(*     [Ops_Elementwise.A_ReLU4d]                                             *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_ReLU4d : forall (batch channel m1 m2 : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input output ->
  (forall (b : fin batch) (c : fin channel) (i0 : fin m1) (i1 : fin m2),
     DE.eval_bexp (env_val rho)
       (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx input b) c) i0) i1) CD.zero) =
     DE.bexp2bool
       (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx input b) c) i0) i1) CD.zero)) ->
  SEM.eval (CEO.ReLU4d_comm input output) rho =
  OE.ReLU4d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch channel m1 m2 input output rho Hindep Hb.
  rewrite <- (CEO.ReLU4d_equiv_sem rho Hindep Hb).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- OE.A_ReLU4d.
  cbv [DR.A].
  f_equal.
  apply interp_ReLU4d.
  exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* Add4d: functional interpretation lemma                                     *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Add4d : forall (batch channel m1 m2 : nat)
  (x y : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Add4d x y) rho =
  OE.Add4d (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho).
Proof.
  intros batch channel m1 m2 x y rho.
  unfold COP.Add4d, OE.Add4d.
  apply to_pcg_mkvSeq_ext; intro b.
  apply to_pcg_mkvSeq_ext; intro c.
  apply to_pcg_mkvSeq_ext; intro i.
  apply to_pcg_mkvSeq_ext; intro j.
  rewrite SEM.to_pcg_exp_add.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Add4d: comm-level bridge                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Add4d : forall (batch channel m1 m2 : nat)
  (x y : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc x output ->
  SEM.exp_independent_of_acc y output ->
  SEM.eval (CEB.Add4d_comm x y output) rho =
  OE.Add4d_comm (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho) output rho.
Proof.
  intros batch channel m1 m2 x y output rho Hx Hy.
  rewrite <- (CEB.Add4d_equiv_sem rho Hx Hy).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- OE.A_Add4d.
  cbv [DR.A].
  f_equal.
  apply interp_Add4d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mul2d: functional interpretation lemma                                     *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Mul2d : forall (m1 m2 : nat)
  (x y : DE.exp (ary '{m1} (ary '{m2} num))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Mul2d x y) rho =
  OE.Mul2d (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho).
Proof.
  intros m1 m2 x y rho.
  unfold COP.Mul2d, OE.Mul2d.
  apply to_pcg_mkvSeq_ext; intro i.
  apply to_pcg_mkvSeq_ext; intro j.
  rewrite OSE.to_pcg_exp_mul.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mul2d: comm-level bridge                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Mul2d : forall (m1 m2 : nat)
  (x y : DE.exp (ary '{m1} (ary '{m2} num)))
  (output : DE.acc (ary '{m1} (ary '{m2} num)))
  (rho : PCG.env),
  SEM.exp_independent_of_acc x output ->
  SEM.exp_independent_of_acc y output ->
  SEM.eval (CEL.Mul2d_comm x y output) rho =
  OE.Mul2d_comm (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho) output rho.
Proof.
  intros m1 m2 x y output rho Hx Hy.
  rewrite <- (CEL.Mul2d_equiv_sem rho Hx Hy).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- OE.A_Mul2d.
  cbv [DR.A].
  f_equal.
  apply interp_Mul2d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Add2d: the route-B side [CNN_Examples_Base.Add2d_comm] has no proved       *)
(* [Add2d_equiv_sem]; we prove it here (verbatim analog of                    *)
(* [CNN_Examples_LeNet5.Mul2d_equiv_sem] with [add] in place of [mul]).       *)
(* -------------------------------------------------------------------------- *)

Lemma Add2d_equiv_sem : forall (m1 m2 : nat)
  (x y : DE.exp (ary '{m1} (ary '{m2} num)))
  (output : DE.acc (ary '{m1} (ary '{m2} num)))
  (rho : PCG.env),
  SEM.exp_independent_of_acc x output ->
  SEM.exp_independent_of_acc y output ->
  SEM.eval (CG.A (output, COP.Add2d x y)) rho =
  SEM.eval (CEB.Add2d_comm x y output) rho.
Proof.
  intros m1 m2 x y output rho Hx Hy.
  unfold COP.Add2d, CEB.Add2d_comm.
  rewrite CCG.AmkvSeq_sem.
  - unfold CG.mkvSeql. rewrite SEM.eval_seqfor.
    apply CEB.seqfor_congr. intros i0 eta0.
    rewrite CCG.AmkvSeq_sem.
    + unfold CG.mkvSeql. rewrite SEM.eval_seqfor.
      apply CEB.seqfor_congr. intros i1 eta1. reflexivity.
    + intros i1. apply SEM.exp_independent_of_acc_add;
        [ apply SEM.exp_independent_of_acc_idx;
          apply CEB.exp_independent_of_acc_weaken_ary;
          apply SEM.exp_independent_of_acc_idx; auto
        | apply SEM.exp_independent_of_acc_idx;
          apply CEB.exp_independent_of_acc_weaken_ary;
          apply SEM.exp_independent_of_acc_idx; auto ].
  - intros i0. apply SEM.exp_independent_of_acc_mkvSeq; intros i1.
    apply SEM.exp_independent_of_acc_add;
      [ apply SEM.exp_independent_of_acc_idx;
        apply SEM.exp_independent_of_acc_idx; auto
      | apply SEM.exp_independent_of_acc_idx;
        apply SEM.exp_independent_of_acc_idx; auto ].
Qed.

(* -------------------------------------------------------------------------- *)
(* Add2d: functional interpretation lemma                                     *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Add2d : forall (m1 m2 : nat)
  (x y : DE.exp (ary '{m1} (ary '{m2} num))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Add2d x y) rho =
  OE.Add2d (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho).
Proof.
  intros m1 m2 x y rho.
  unfold COP.Add2d, OE.Add2d.
  apply to_pcg_mkvSeq_ext; intro i.
  apply to_pcg_mkvSeq_ext; intro j.
  rewrite SEM.to_pcg_exp_add.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Add2d: comm-level bridge                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Add2d : forall (m1 m2 : nat)
  (x y : DE.exp (ary '{m1} (ary '{m2} num)))
  (output : DE.acc (ary '{m1} (ary '{m2} num)))
  (rho : PCG.env),
  SEM.exp_independent_of_acc x output ->
  SEM.exp_independent_of_acc y output ->
  SEM.eval (CEB.Add2d_comm x y output) rho =
  OE.Add2d_comm (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho) output rho.
Proof.
  intros m1 m2 x y output rho Hx Hy.
  rewrite <- (Add2d_equiv_sem m1 m2 x y output rho Hx Hy).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- OE.A_Add2d.
  cbv [DR.A].
  f_equal.
  apply interp_Add2d.
Qed.

Print Assumptions Bridge_ReLU4d.
Print Assumptions Bridge_Add4d.
Print Assumptions Bridge_Mul2d.
Print Assumptions Bridge_Add2d.
