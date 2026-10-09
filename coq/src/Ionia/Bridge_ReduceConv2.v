(* ========================================================================= *)
(* Bridge_ReduceConv2.v                                                      *)
(*                                                                           *)
(* Route-A/route-B operator bridges for the AlexNet/VGG16/ResNet18 whole-    *)
(* net batch, following the pattern of [Ionia.Bridge_ReduceConv] (whose      *)
(* generic interpretation helpers are reused via [BRC]).                     *)
(*                                                                           *)
(* Coverage:                                                                 *)
(*   Conv4d     GENERAL (any batch m1 m2 n1 n2 channel filernum p s):        *)
(*              route B ships no proved [Conv4d_sem] (the specialized        *)
(*              [CNN_Examples_Base.Conv4d_*_equiv] are Axioms or             *)
(*              reflexivity placeholders), so this file supplies a general   *)
(*              AST command [Conv4d_ast_comm] — the direct 4-D lift of       *)
(*              [CNN_Examples_Base_Ops.Conv3d_comm], reading                 *)
(*              [CNN_OP.Padding4d] expression-level — and proves             *)
(*              [Conv4d_sem : eval (A(output, CNN_OP.Conv4d p s ...)) =      *)
(*              eval (Conv4d_ast_comm ...)] from scratch, mirroring          *)
(*              [Operators_Sem_Equiv.Conv3d_sem].  Bridged to route A        *)
(*              [Ops_Conv.Conv4d_comm] via [Ops_Conv.A_Conv4d].              *)
(*   Flatten4d  [OSE.Flatten4d_sem  + AlexNet_DPIA.A_Flatten4d]              *)
(*   GlobalAvgPool4d [OSE.GlobalAvgPool4d_sem + Ops_Reduce.A_GlobalAvgPool4d]*)
(*   Avgpool4d  route B has no AST command; [Avgpool4d_ast_comm] is          *)
(*              supplied here (loopacc style, like [GlobalAvgPool4d_comm])   *)
(*              with a fresh [Avgpool4d_sem]; route A [Ops_Reduce.Avgpool4d].*)
(*   Maxpool4d_pad route B has no proved padded-maxpool equivalence         *)
(*              ([MaxPool4d_pad_equiv] is a reflexivity placeholder); the     *)
(*              file supplies [maxp4dp_exp]/[Maxpool4d_pad_ast_comm]/         *)
(*              [Maxpool4d_pad_sem] and bridges to                            *)
(*              [AlexNet_DPIA.Maxpool4d_pad_comm].                            *)
(*   BatchNorm4d SEMANTIC ALIGNMENT NOTE: route B ([CNN_OP.BatchNorm4d_      *)
(*              inference] + the proved [CNN_Examples_Base.BatchNorm4d_      *)
(*              equiv_sem]) is INFERENCE mode with per-channel mean/var      *)
(*              given as inputs, while route A ([Ops_BatchNorm.BatchNorm4d]) *)
(*              COMPUTES per-(batch,channel)-slice statistics.  The two are  *)
(*              bridged at [batch = 1] (the shape used by the ResNet18       *)
(*              examples) by instantiating route B's mean/var inputs with    *)
(*              the slice statistics [bn1_mean]/[bn1_var]; for batch > 1 the *)
(*              per-slice statistics of route A have no per-channel route-B  *)
(*              counterpart, so no general-batch bridge exists.              *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

From Stdlib Require Import Reals String Arith Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.
Require Import Ionia.finType Ionia.vector Ionia.DataExp Ionia.CNN_Defs
  Ionia.CNN_CodeGen_Core Ionia.Proof_CodeGen Ionia.DPIA_Rules
  Ionia.CNN_CodeGen_Semantics Ionia.CNN_Examples_Base
  Ionia.CNN_Examples_Base_Ops Ionia.CNN_OP Ionia.Operators_Sem_Equiv
  Ionia.LeNet5_Functional Ionia.LeNet5_Imperative Ionia.LeNet5_DPIA
  Ionia.FusionTactics Ionia.Bridge_ReduceConv.
Require Ionia.Ops_BatchNorm Ionia.AlexNet_DPIA.

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
Module OC := Ionia.Ops_Conv.
Module OR := Ionia.Ops_Reduce.
Module OP := Ionia.Ops_PoolPad.
Module OB := Ionia.Ops_BatchNorm.
Module AD := Ionia.AlexNet_DPIA.
Module V := Ionia.vector.
Module BRC := Ionia.Bridge_ReduceConv.
Module FTac := Ionia.FusionTactics.

(* -------------------------------------------------------------------------- *)
(* Flatten4d                                                                  *)
(*                                                                            *)
(*   route B: eval (Flatten4d_comm) = eval (A(output, CNN_OP.Flatten4d e))    *)
(*     [Operators_Sem_Equiv.Flatten4d_sem]                                    *)
(*   route A: A(output, AlexNet_DPIA.Flatten4d e) = Flatten4d_comm e out      *)
(*     [AlexNet_DPIA.A_Flatten4d]                                             *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Flatten4d : forall (batch channel m1 m2 : nat)
  (Hb : batch > 0) (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Flatten4d input) rho =
  AD.Flatten4d (SEM.to_pcg_exp input rho).
Proof.
  intros batch channel m1 m2 Hb Hc Hm1 Hm2 input rho.
  unfold COP.Flatten4d, AD.Flatten4d.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  rewrite !BRC.to_pcg_join.
  rewrite SEM.to_pcg_exp_idx.
  unfold PCG.join.
  apply V.mk_vec_ext; intro x. cbv beta.
  destruct (V.idx_1d_to_2d x) as [ci j]. simpl.
  assert (Hcm : channel * m1 > 0) by (apply Nat.mul_pos_pos; assumption).
  rewrite (PCG.idx_mkvSeq _ _ _ Hcm). cbv beta.
  destruct (V.idx_1d_to_2d ci) as [c i]. simpl.
  reflexivity.
Qed.

Theorem Bridge_Flatten4d : forall (batch channel m1 m2 : nat)
  (Hb : batch > 0) (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel * m1 * m2} num)))
  (rho : PCG.env),
  (forall output' : DE.acc (ary '{batch} (ary '{channel * m1 * m2} num)),
     SEM.exp_independent_of_acc input output') ->
  OSE.tmp_disjoint_from_output2d batch (channel * m1 * m2) output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEB.Flatten4d_comm input output) rho =
  AD.Flatten4d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch channel m1 m2 Hb Hc Hm1 Hm2 input output rho Hio Hdisj Hundef.
  rewrite <- (OSE.Flatten4d_sem Hc Hm1 Hm2 Hio Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (AD.A_Flatten4d batch channel m1 m2 (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Flatten4d; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* GlobalAvgPool4d                                                            *)
(*                                                                            *)
(*   route B: eval (GlobalAvgPool4d_comm)                                     *)
(*              = eval (A(output, CNN_OP.GlobalAvgPool4d e))                  *)
(*     [Operators_Sem_Equiv.GlobalAvgPool4d_sem]                              *)
(*   route A: A(output, Ops_Reduce.GlobalAvgPool4d e) = ..._comm e out        *)
(*     [Ops_Reduce.A_GlobalAvgPool4d]                                         *)
(* -------------------------------------------------------------------------- *)

Lemma interp_GlobalAvgPool4d : forall (batch channel m1 m2 : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.GlobalAvgPool4d input) rho =
  OR.GlobalAvgPool4d (SEM.to_pcg_exp input rho).
Proof.
  intros batch channel m1 m2 input rho.
  unfold COP.GlobalAvgPool4d, OR.GlobalAvgPool4d.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  apply BRC.to_pcg_mkvSeq_ext; intro c.
  rewrite OSE.to_pcg_exp_div_n.
  apply f_equal2; [ | reflexivity ].
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Theorem Bridge_GlobalAvgPool4d : forall (batch channel m1 m2 : nat)
  (Hb : batch > 0) (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel} num)))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{batch} (ary '{channel} num)),
     SEM.exp_independent_of_acc input output') ->
  (forall p b c, @PCG.in_acc num p OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num p (output |{ b} |{ c})) ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CEO.GlobalAvgPool4d_comm input output) rho =
  OR.GlobalAvgPool4d_comm (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch channel m1 m2 Hb Hc Hm1 Hm2 input output rho Hi Hio Hdisj Hundef.
  rewrite <- (OSE.GlobalAvgPool4d_sem Hb Hc Hm1 Hm2 Hi Hio Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (OR.A_GlobalAvgPool4d batch channel m1 m2 (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_GlobalAvgPool4d.
Qed.

(* -------------------------------------------------------------------------- *)
(* BatchNorm4d (batch = 1; see the header note on the semantic difference)    *)
(*                                                                            *)
(*   route B: eval (BatchNorm4d_comm)                                         *)
(*              = eval (A(output, CNN_OP.BatchNorm4d_inference ...))          *)
(*     [CNN_Examples_Base.BatchNorm4d_equiv_sem]                              *)
(*   route A: A(output, Ops_BatchNorm.BatchNorm4d ...) = BatchNorm4d_comm ... *)
(*     [Ops_BatchNorm.A_BatchNorm4d]                                          *)
(* -------------------------------------------------------------------------- *)

(* The sole batch index at [batch = 1]. *)
Definition bn1_b0 : fin 1 := ltS 0.

(* Route-B expression computing the route-A slice mean of batch element 0. *)
Definition bn1_mean {channel m1 m2 : nat}
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : DE.exp (ary '{channel} num) :=
  DE.mkvSeq (fun c : fin channel =>
    CD.div_n (CD.sum (DE.mkvSeq (fun i : fin m1 =>
      CD.sum (DE.mkvSeq (fun j : fin m2 =>
        input|[bn1_b0]|[c]|[i]|[j]))))) (m1 * m2)).

(* Route-B expression computing the route-A slice variance of batch element 0. *)
Definition bn1_var {channel m1 m2 : nat}
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : DE.exp (ary '{channel} num) :=
  DE.mkvSeq (fun c : fin channel =>
    CD.div_n (CD.sum (DE.mkvSeq (fun i : fin m1 =>
      CD.sum (DE.mkvSeq (fun j : fin m2 =>
        CD.mul (CD.sub input|[bn1_b0]|[c]|[i]|[j] (bn1_mean input)|[c])
               (CD.sub input|[bn1_b0]|[c]|[i]|[j] (bn1_mean input)|[c])
      ))))) (m1 * m2)).

(* [CD.sub] reads as [Rminus] (local counterpart of [OSE.to_pcg_exp_mul]). *)
Lemma to_pcg_exp_sub : forall (x y : DE.exp num) (rho : PCG.env),
  SEM.to_pcg_exp (CD.sub x y) rho =
  Rminus (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho).
Proof. intros. unfold CD.sub. cbv [SEM.to_pcg_exp]. simpl. reflexivity. Qed.

(* [CD.sqrt] reads as [PCG.sqrt]. *)
Lemma to_pcg_exp_sqrt : forall (x : DE.exp num) (rho : PCG.env),
  SEM.to_pcg_exp (CD.sqrt x) rho = PCG.sqrt (SEM.to_pcg_exp x rho).
Proof. intros. unfold CD.sqrt, PCG.sqrt. cbv [SEM.to_pcg_exp]. simpl. reflexivity. Qed.

Lemma interp_bn1_mean : forall (channel m1 m2 : nat)
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (bn1_mean input) rho =
  PCG.mkvSeq (fun c : fin channel =>
    OB.BNmean (PCG.idx (PCG.idx (SEM.to_pcg_exp input rho) bn1_b0) c)).
Proof.
  intros channel m1 m2 input rho.
  unfold bn1_mean, OB.BNmean, OB.BNmeanSum.
  apply BRC.to_pcg_mkvSeq_ext; intro c.
  rewrite OSE.to_pcg_exp_div_n.
  apply f_equal2; [ | reflexivity ].
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Lemma interp_bn1_var : forall (channel m1 m2 : nat) (Hc : channel > 0)
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (bn1_var input) rho =
  PCG.mkvSeq (fun c : fin channel =>
    OB.BNvar (PCG.idx (PCG.idx (SEM.to_pcg_exp input rho) bn1_b0) c)
             (OB.BNmean (PCG.idx (PCG.idx (SEM.to_pcg_exp input rho) bn1_b0) c))).
Proof.
  intros channel m1 m2 Hc input rho.
  unfold bn1_var, OB.BNvar, OB.BNvarSum.
  apply BRC.to_pcg_mkvSeq_ext; intro c.
  rewrite OSE.to_pcg_exp_div_n.
  apply f_equal2; [ | reflexivity ].
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j.
  rewrite OSE.to_pcg_exp_mul, !to_pcg_exp_sub.
  repeat rewrite SEM.to_pcg_exp_idx.
  rewrite interp_bn1_mean.
  rewrite (PCG.idx_mkvSeq _ _ _ Hc).
  reflexivity.
Qed.

Lemma interp_BatchNorm4d : forall (channel m1 m2 : nat) (Hc : channel > 0)
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : DE.exp (ary '{channel} num))
  (eps : DE.exp num) (rho : PCG.env),
  SEM.to_pcg_exp
    (COP.BatchNorm4d_inference input (bn1_mean input) (bn1_var input)
       gamma beta eps) rho =
  OB.BatchNorm4d (SEM.to_pcg_exp input rho) (SEM.to_pcg_exp gamma rho)
    (SEM.to_pcg_exp beta rho) (SEM.to_pcg_exp eps rho).
Proof.
  intros channel m1 m2 Hc input gamma beta eps rho.
  unfold COP.BatchNorm4d_inference, OB.BatchNorm4d.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  assert (Hb0 : bn1_b0 = b).
  { apply fin_eq'. unfold bn1_b0. destruct b as [x Hx]. simpl in *. lia. }
  apply BRC.to_pcg_mkvSeq_ext; intro c.
  apply BRC.to_pcg_mkvSeq_ext; intro i.
  apply BRC.to_pcg_mkvSeq_ext; intro j.
  unfold OB.BNcell. cbv zeta.
  rewrite OSE.to_pcg_exp_add, OSE.to_pcg_exp_mul, OSE.to_pcg_exp_div,
    to_pcg_exp_sub, to_pcg_exp_sqrt, OSE.to_pcg_exp_add.
  repeat rewrite SEM.to_pcg_exp_idx.
  rewrite interp_bn1_mean, interp_bn1_var by assumption.
  rewrite Hb0.
  rewrite (PCG.idx_mkvSeq _ _ _ Hc).
  rewrite (PCG.idx_mkvSeq _ _ _ Hc).
  reflexivity.
Qed.

(* Independence of the computed statistics from the output acceptor. *)
Lemma bn1_mean_independent : forall (channel m1 m2 : nat)
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc (bn1_mean input) output.
Proof.
  intros channel m1 m2 input output Hi.
  unfold bn1_mean.
  apply SEM.exp_independent_of_acc_mkvSeq; intro c.
  apply OSE.exp_independent_of_acc_div_n.
  apply OSE.exp_independent_of_acc_sum; intro i.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum; intro j.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply SEM.exp_independent_of_acc_idx.
  exact Hi.
Qed.

Lemma bn1_var_independent : forall (channel m1 m2 : nat)
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc (bn1_var input) output.
Proof.
  intros channel m1 m2 input output Hi.
  unfold bn1_var.
  apply SEM.exp_independent_of_acc_mkvSeq; intro c.
  apply OSE.exp_independent_of_acc_div_n.
  apply OSE.exp_independent_of_acc_sum; intro i.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum; intro j.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply SEM.exp_independent_of_acc_mul;
  apply SEM.exp_independent_of_acc_sub.
  - repeat apply SEM.exp_independent_of_acc_idx. exact Hi.
  - apply SEM.exp_independent_of_acc_idx.
    apply bn1_mean_independent. exact Hi.
  - repeat apply SEM.exp_independent_of_acc_idx. exact Hi.
  - apply SEM.exp_independent_of_acc_idx.
    apply bn1_mean_independent. exact Hi.
Qed.

Theorem Bridge_BatchNorm4d : forall (channel m1 m2 : nat)
  (Hc : channel > 0)
  (input : DE.exp (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (gamma beta : DE.exp (ary '{channel} num))
  (eps : DE.exp num)
  (output : DE.acc (ary '{1} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc gamma output ->
  SEM.exp_independent_of_acc beta output ->
  SEM.exp_independent_of_acc eps output ->
  SEM.eval (CEB.BatchNorm4d_comm input (bn1_mean input) (bn1_var input)
              gamma beta eps output) rho =
  OB.BatchNorm4d_comm (SEM.to_pcg_exp input rho) (SEM.to_pcg_exp gamma rho)
    (SEM.to_pcg_exp beta rho) (SEM.to_pcg_exp eps rho) output rho.
Proof.
  intros channel m1 m2 Hc input gamma beta eps output rho Hi Hg Hb He.
  rewrite <- (CEB.BatchNorm4d_equiv_sem rho
    Hi (bn1_mean_independent _ _ _ _ _ Hi) (bn1_var_independent _ _ _ _ _ Hi)
    Hg Hb He).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (OB.A_BatchNorm4d 1 channel m1 m2 (SEM.to_pcg_exp input rho)
    (SEM.to_pcg_exp gamma rho) (SEM.to_pcg_exp beta rho)
    (SEM.to_pcg_exp eps rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_BatchNorm4d. exact Hc.
Qed.

(* -------------------------------------------------------------------------- *)
(* Avgpool4d                                                                  *)
(*                                                                            *)
(*   route B has no Avgpool4d AST command; [Avgpool4d_ast_comm] is the        *)
(*   loopacc-style 4-D average pool supplied here (mirroring                  *)
(*   [CNN_Examples_Base_Ops.GlobalAvgPool4d_comm]), with a fresh semantic     *)
(*   equivalence [Avgpool4d_sem] proved along the lines of                    *)
(*   [Operators_Sem_Equiv.GlobalAvgPool4d_sem].                               *)
(*   route A: A(output, Ops_Reduce.Avgpool4d k e) = Avgpool4d_comm k e out    *)
(*     [Ops_Reduce.A_Avgpool4d]                                               *)
(* -------------------------------------------------------------------------- *)

Definition Avgpool4d_ast_comm {batch filernum m1 m2 : nat} (k : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch}
    (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))) : CG.comm :=
  CG.seqfor (fun b : fin batch => CG.seqfor (fun nu : fin filernum =>
    CG.seqfor (fun i0 : fin (m1/k) => CG.seqfor (fun i1 : fin (m2/k) =>
      @CG.loopacc num (fun tmp =>
        (CG.vwt tmp |:= CD.zero) ';
        CG.seqfor (fun kk : fin (k * k) =>
          CG.vwt tmp |:= CD.add
            (CD.safe_idx_nat (CD.safe_idx_nat input|[b]|[nu]
               (fin2nat i0 * k + Nat.div (fin2nat kk) k))
               (fin2nat i1 * k + Nat.modulo (fin2nat kk) k))
            (CG.vrd tmp)) ';
        output|{b}|{nu}|{i0}|{i1} |:= CD.div_n (CG.vrd tmp) (k * k)))))).

Section Avgpool4d_Sem.

Variables (batch filernum m1 m2 k : nat)
          (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))).
Hypothesis Hbatch : batch > 0.
Hypothesis Hfilernum : filernum > 0.
Hypothesis Hk : k > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Hypothesis Hinput_out : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))),
  SEM.exp_independent_of_acc input output.

Definition tmp_disjoint_from_output_avg4
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))))
  : Prop :=
  forall pth b nu i0 i1, @PCG.in_acc num pth OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num pth (output |{ b} |{ nu} |{ i0} |{ i1}).

(* Flat window index bounds. *)
Lemma avg4_window_bounds : forall (kk : fin (k * k)),
  Nat.div (fin2nat kk) k < k /\ Nat.modulo (fin2nat kk) k < k.
Proof.
  intro kk. destruct kk as [x Hx]. simpl. split.
  - apply Nat.div_lt_upper_bound; [lia | exact Hx].
  - apply Nat.mod_upper_bound. lia.
Qed.

(* Window base + offset stays inside the input (mirror of
   [Ops_Reduce.avgpool_index_lt] on raw nats). *)
Lemma avg4_win_i_bound : forall (m : nat) (i0 : fin (m / k)) (x : nat),
  x < k -> fin2nat i0 * k + x < m.
Proof.
  intros m i0 x Hx.
  destruct k as [| k']; [inversion Hx |].
  assert (Hi : fin2nat i0 < m / S k') by apply (fin_proof i0).
  assert (Hle : S k' * (m / S k') <= m).
  { pose proof (Nat.div_mod_eq m (S k')) as Heq. lia. }
  assert (Hik : fin2nat i0 * S k' <= (m / S k' - 1) * S k').
  { apply Nat.mul_le_mono_r. lia. }
  assert (Hle2 : (m / S k' - 1) * S k' + S k' <= m / S k' * S k').
  { destruct (m / S k'); lia. }
  lia.
Qed.

(* Flat window cell, matching the loop body of [Avgpool4d_ast_comm]. *)
Definition avg4_flat_cell (b : fin batch) (nu : fin filernum)
  (i0 : fin (m1 / k)) (i1 : fin (m2 / k)) (kk : fin (k * k)) : DE.exp num :=
  CD.safe_idx_nat (CD.safe_idx_nat input|[b]|[nu]
    (fin2nat i0 * k + Nat.div (fin2nat kk) k))
    (fin2nat i1 * k + Nat.modulo (fin2nat kk) k).

(* The functional k x k window sum equals the flattened sum. *)
Lemma avg4_nested_sum_flat : forall (b : fin batch) (nu : fin filernum)
  (i0 : fin (m1 / k)) (i1 : fin (m2 / k)) (rho : PCG.env),
  SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun j0 : fin k =>
    CD.sum (DE.mkvSeq (fun j1 : fin k =>
      input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                   |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) rho =
  SEM.to_pcg_exp (CD.sum (DE.mkvSeq (avg4_flat_cell b nu i0 i1))) rho.
Proof.
  intros b nu i0 i1 rho.
  set (idx_cell := fun (di dj : nat) (Hdi : di < k) (Hdj : dj < k) =>
    input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 (nat2fin Hdi))]
                 |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 (nat2fin Hdj))]).
  assert (Heq_lhs :
    SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun j0 : fin k =>
      CD.sum (DE.mkvSeq (fun j1 : fin k =>
        input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                     |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) rho =
    OSE.sumR_nat_fin (fun di Hdi => OSE.sumR_nat_fin (fun dj Hdj =>
      SEM.to_pcg_exp (idx_cell di dj Hdi Hdj) rho))).
  { rewrite OSE.to_pcg_exp_sum_nat by lia.
    apply OSE.sumR_nat_fin_eq. intros di Hdi.
    rewrite OSE.to_pcg_exp_sum_nat by lia.
    apply OSE.sumR_nat_fin_eq. intros dj Hdj.
    reflexivity. }
  assert (Heq_rhs :
    SEM.to_pcg_exp (CD.sum (DE.mkvSeq (avg4_flat_cell b nu i0 i1))) rho =
    OSE.sumR_nat_fin (fun kk Hkk =>
      SEM.to_pcg_exp (avg4_flat_cell b nu i0 i1 (nat2fin Hkk)) rho)).
  { rewrite OSE.to_pcg_exp_sum_nat by nia. reflexivity. }
  rewrite Heq_lhs, Heq_rhs.
  pose (lemma := @OSE.sumR_nat_fin_nested_flat' k k Hk Hk
    (fun di dj Hdi Hdj => SEM.to_pcg_exp (idx_cell di dj Hdi Hdj) rho)
    (fun kk Hkk => SEM.to_pcg_exp (avg4_flat_cell b nu i0 i1 (nat2fin Hkk)) rho)
    (fun kk Hkk => avg4_window_bounds (nat2fin Hkk))).
  apply lemma.
  - intros di dj Hdi1 Hdi2 Hdj1 Hdj2.
    unfold idx_cell. repeat rewrite SEM.to_pcg_exp_idx.
    apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
    apply f_equal2; [ reflexivity | ].
    apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity.
  - intros kk Hkk.
    unfold avg4_flat_cell, idx_cell.
    destruct (avg4_window_bounds (nat2fin Hkk)) as [Hdi Hdj].
    rewrite (CD.safe_idx_nat_lt _ (avg4_win_i_bound _ i0 _ Hdi)).
    rewrite (CD.safe_idx_nat_lt _ (avg4_win_i_bound _ i1 _ Hdj)).
    repeat rewrite SEM.to_pcg_exp_idx.
    apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
    apply f_equal2; [ reflexivity | ].
    apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity.
Qed.

Lemma avg4_cell_independent_of_output : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))))
  (b : fin batch) (nu : fin filernum) (i0 : fin (m1/k)) (i1 : fin (m2/k)),
  SEM.exp_independent_of_acc
    (CD.div_n (CD.sum (DE.mkvSeq (fun j0 : fin k =>
      CD.sum (DE.mkvSeq (fun j1 : fin k =>
        input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                     |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))
    output.
Proof.
  intros output b nu i0 i1.
  apply OSE.exp_independent_of_acc_div_n.
  apply OSE.exp_independent_of_acc_sum; intro j0.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply SEM.exp_independent_of_acc_idx.
  apply Hinput_out.
Qed.

Lemma avg4_cell_independent_of_tmp : forall
  (b : fin batch) (nu : fin filernum) (i0 : fin (m1/k)) (i1 : fin (m2/k)),
  SEM.exp_independent_of_acc
    (CD.sum (DE.mkvSeq (fun j0 : fin k =>
      CD.sum (DE.mkvSeq (fun j1 : fin k =>
        input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                     |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)])))))
    OSE.tmp_scalar_acc.
Proof.
  intros b nu i0 i1.
  apply OSE.exp_independent_of_acc_sum; intro j0.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply SEM.exp_independent_of_acc_idx.
  exact Hinput_indep.
Qed.

Lemma avg4_cell_continuation_ok : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))))
  (b : fin batch) (nu : fin filernum) (i0 : fin (m1/k)) (i1 : fin (m2/k)),
  tmp_disjoint_from_output_avg4 output ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => output|{b}|{nu}|{i0}|{i1} |:= CD.div_n r (k * k))
    (CD.sum (DE.mkvSeq (avg4_flat_cell b nu i0 i1))).
Proof.
  intros output b nu i0 i1 Hdisj.
  apply OSE.scalar_assign_continuation_ok.
  - intros p Hp Hout. apply (Hdisj p b nu i0 i1 Hp). exact Hout.
  - apply OSE.exp_independent_of_acc_sum; intro kk.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold avg4_flat_cell.
    repeat apply OSE.safe_idx_nat_independent.
    repeat apply SEM.exp_independent_of_acc_idx.
    exact Hinput_indep.
  - apply OSE.exp_independent_of_acc_div_n.
    apply OSE.exp_independent_of_acc_sum; intro kk.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold avg4_flat_cell.
    repeat apply OSE.safe_idx_nat_independent.
    repeat apply SEM.exp_independent_of_acc_idx.
    exact Hinput_indep.
  - intros rho eta v Hv Heta.
    rewrite !OSE.to_pcg_exp_div_n.
    f_equal.
    rewrite SEM.to_pcg_exp_REvar_tmp'.
    rewrite SEM.value_at_update_same.
    symmetry. exact Hv.
Qed.

Theorem Avgpool4d_sem : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))))
  (rho : PCG.env),
  tmp_disjoint_from_output_avg4 output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CG.A (output, COP.Avgpool4d k input)) rho =
  SEM.eval (Avgpool4d_ast_comm k input output) rho.
Proof.
  intros output rho Hdisj Hundef.
  unfold CG.A, COP.Avgpool4d, Avgpool4d_ast_comm.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin (m1 / k) =>
        DE.mkvSeq (fun i1 : fin (m2 / k) =>
          CD.div_n (CD.sum (DE.mkvSeq (fun j0 : fin k =>
            CD.sum (DE.mkvSeq (fun j1 : fin k =>
              input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                           |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i1.
    apply avg4_cell_independent_of_output. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* batch slice b *)
    assert (Hcell_b : forall nu i0 i1,
      SEM.exp_independent_of_acc
        (CD.div_n (CD.sum (DE.mkvSeq (fun j0 : fin k =>
          CD.sum (DE.mkvSeq (fun j1 : fin k =>
            input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                         |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))
        (output |{ b})).
    { intros nu i0 i1 p0 Hp.
      apply (avg4_cell_independent_of_output output b nu i0 i1).
      apply SEM.in_acc_ary_inv with (i := b). exact Hp. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros nu;
      apply SEM.exp_independent_of_acc_mkvSeq; intros i0;
      apply SEM.exp_independent_of_acc_mkvSeq; intros i1; apply Hcell_b ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros nu eta' HPeta'. split.
    + (* channel slice num *)
      assert (Hcell_nu : forall i0 i1,
        SEM.exp_independent_of_acc
          (CD.div_n (CD.sum (DE.mkvSeq (fun j0 : fin k =>
            CD.sum (DE.mkvSeq (fun j1 : fin k =>
              input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                           |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))
          ((output |{ b}) |{ nu})).
      { intros i0 i1 p0 Hp.
        apply (avg4_cell_independent_of_output output b nu i0 i1).
        apply SEM.in_acc_ary_inv with (i := b).
        apply SEM.in_acc_ary_inv with (i := nu).
        exact Hp. }
      rewrite SEM.eval_mkvSeq; [ | intros i0;
        apply SEM.exp_independent_of_acc_mkvSeq; intros i1; apply Hcell_nu ].
      rewrite !SEM.eval_seqfor.
      apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros i0 eta'' HPeta''. split.
      * (* row i0 *)
        assert (Hcell_i0 : forall i1,
          SEM.exp_independent_of_acc
            (CD.div_n (CD.sum (DE.mkvSeq (fun j0 : fin k =>
              CD.sum (DE.mkvSeq (fun j1 : fin k =>
                input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                             |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))
            (((output |{ b}) |{ nu}) |{ i0})).
        { intros i1 p0 Hp.
          apply (avg4_cell_independent_of_output output b nu i0 i1).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
          exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros i1; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros i1 eta''' HPeta'''. split.
        -- (* the cell: loopacc elimination *)
           set (e := DE.mkvSeq (avg4_flat_cell b nu i0 i1)).
           set (c := fun r : DE.exp num =>
             (((output |{ b}) |{ nu}) |{ i0}) |{ i1} |:= CD.div_n r (k * k)).
           rewrite (FTac.reduce_loopacc_named_sem _ _ (fun tmp : string =>
             (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (k * k) =>
               CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp)) eta''').
           2: { intros tmp. apply functional_extensionality. intro rho1.
                cbn beta zeta iota. repeat f_equal.
                all: try reflexivity.
                all: try (apply functional_extensionality; intro kk; repeat f_equal;
                  assert (Heq : CD.safe_idx_nat (CD.safe_idx_nat input|[b]|[nu]
                                    (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                                    (fin2nat i1 * k + Nat.modulo (fin2nat kk) k) =
                                DE.idx e kk)
                    by (unfold e, DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec; reflexivity);
                  rewrite Heq; reflexivity). }
           rewrite SEM.eval_assign.
           rewrite <- (SEM.eval_assign_aux 1 num _ _ eta''').
           change (SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun j0 : fin k =>
             CD.sum (DE.mkvSeq (fun j1 : fin k =>
               input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                            |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)])))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (k * k) =>
                 CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp))) eta''').
           assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun j0 : fin k =>
             CD.sum (DE.mkvSeq (fun j1 : fin k =>
               input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                            |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)]))))) eta''' =
             SEM.to_pcg_exp (CD.sum e) eta''').
           { unfold e. apply avg4_nested_sum_flat. }
           assert (Heq_aux : SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun j0 : fin k =>
             CD.sum (DE.mkvSeq (fun j1 : fin k =>
               input|[b]|[nu]|[nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)]
                            |[nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)])))))) 1 eta''' =
             SEM.eval_aux (c (CD.sum e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal.
             rewrite !OSE.to_pcg_exp_div_n. f_equal. exact Hsum_eq. }
           rewrite Heq_aux.
           apply SEM.eval_csum_equiv.
           ++ exact HPeta'''.
           ++ unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              unfold avg4_flat_cell.
              repeat apply OSE.safe_idx_nat_independent.
              repeat apply SEM.exp_independent_of_acc_idx.
              exact Hinput_indep.
           ++ apply avg4_cell_continuation_ok. exact Hdisj.
        -- rewrite SEM.eval_assign.
           apply OSE.assign_preserves_StructUndefined_tmp.
           ++ intros pth Hp Hout. apply (Hdisj pth b nu i0 i1 Hp). exact Hout.
           ++ exact HPeta'''.
      * rewrite SEM.eval_assign.
        apply PCG.StructUndefined_num.
        apply eq_trans with (y := eta'' OSE.tmp_path).
        -- rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
           apply PCG.seqfor_pointwise. intros i1 rho'.
           apply PCG.assign_not_in_acc.
           intros Hin. apply (Hdisj OSE.tmp_path b nu i0 i1 OSE.in_acc_tmp_scalar_acc).
           exact Hin.
        -- apply PCG.StructUndefined_num in HPeta''. exact HPeta''.
    + rewrite SEM.eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta' OSE.tmp_path).
      * rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros i0 rho'.
        rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros i1 rho''.
        apply PCG.assign_not_in_acc.
        intros Hin. apply (Hdisj OSE.tmp_path b nu i0 i1 OSE.in_acc_tmp_scalar_acc).
        exact Hin.
      * apply PCG.StructUndefined_num in HPeta'. exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros nu rho'.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros i0 rho''.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros i1 rho'''.
      apply PCG.assign_not_in_acc.
      intros Hin. apply (Hdisj OSE.tmp_path b nu i0 i1 OSE.in_acc_tmp_scalar_acc).
      exact Hin.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

End Avgpool4d_Sem.

(* Avgpool4d: functional interpretation lemma. *)
Lemma interp_Avgpool4d : forall (batch filernum m1 m2 k : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Avgpool4d k input) rho =
  OR.Avgpool4d k (SEM.to_pcg_exp input rho).
Proof.
  intros batch filernum m1 m2 k input rho.
  unfold COP.Avgpool4d, OR.Avgpool4d.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  apply BRC.to_pcg_mkvSeq_ext; intro num.
  apply BRC.to_pcg_mkvSeq_ext; intro i0.
  apply BRC.to_pcg_mkvSeq_ext; intro i1.
  rewrite OSE.to_pcg_exp_div_n.
  apply f_equal2; [ | reflexivity ].
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j0.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j1.
  repeat rewrite SEM.to_pcg_exp_idx.
  apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
  apply f_equal2; [ reflexivity | ].
  apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity.
Qed.

Theorem Bridge_Avgpool4d : forall (batch filernum m1 m2 k : nat)
  (Hb : batch > 0) (Hf : filernum > 0) (Hk : k > 0)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch}
    (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{batch}
     (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))),
     SEM.exp_independent_of_acc input output') ->
  (forall p b nu i0 i1, @PCG.in_acc num p OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num p (output |{ b} |{ nu} |{ i0} |{ i1})) ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (Avgpool4d_ast_comm k input output) rho =
  OR.Avgpool4d_comm k (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch filernum m1 m2 k Hb Hf Hk input output rho Hi Hio Hdisj Hundef.
  rewrite <- (Avgpool4d_sem batch filernum m1 m2 k input Hb Hf Hk Hi Hio
    output rho Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (OR.A_Avgpool4d batch filernum m1 m2 k (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Avgpool4d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv4d (GENERAL: any batch m1 m2 n1 n2 channel filernum p s with s > 0)    *)
(*                                                                            *)
(*   Route B ships no proved [Conv4d_sem]: [CNN_Examples_Base.Conv4d_p1_k3_   *)
(*   s2_equiv] and its siblings are Axioms (and [MaxPool4d_pad_equiv] /       *)
(*   [Conv4d_p0_k1_s1_equiv] are reflexivity placeholders), so this file      *)
(*   supplies a general AST command [Conv4d_ast_comm] — the direct 4-D lift   *)
(*   of [CNN_Examples_Base_Ops.Conv3d_comm], reading the expression-level     *)
(*   [CNN_OP.Padding4d] — and proves [Conv4d_sem] from scratch by replaying   *)
(*   the [Operators_Sem_Equiv.Conv3d_sem] argument with one more loop level.  *)
(*   The bridge then targets route A [Ops_Conv.Conv4d_comm] via               *)
(*   [Ops_Conv.A_Conv4d], covering every Conv4d shape used by AlexNet         *)
(*   (11x11 p2 s4, 5x5 p2 s1, 3x3 p1 s1), VGG16 (3x3 p1 s1) and ResNet18     *)
(*   (7x7 p3 s2, 3x3 p1 s1/s2, 1x1 p0 s2).                                    *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_ast_comm {batch m1 m2 n1 n2 channel filernum : nat}
  (p s : nat)
  (bias : DE.exp (ary '{filernum} num))
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))) : CG.comm :=
  CG.seqfor (fun b : fin batch => CG.seqfor (fun nu : fin filernum =>
    CG.seqfor (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
      CG.seqfor (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
        @CG.loopacc num (fun tmp =>
          (CG.vwt tmp |:= CD.zero) ';
          CG.seqfor (fun kk : fin (channel * n1 * n2) =>
            CG.vwt tmp |:= CD.add (CD.mul (CD.safe_idx_nat (CD.safe_idx_nat (COP.Padding4d p input)|[b]|[nat2fin (CEO.conv3d_flat_c_bound kk)] (fin2nat i0 * s + Nat.div (Nat.modulo (fin2nat kk) (n1 * n2)) n2)) (fin2nat j0 * s + Nat.modulo (fin2nat kk) n2)) w|[nu]|[nat2fin (CEO.conv3d_flat_c_bound kk)]|[nat2fin (CEO.conv3d_flat_i1_bound kk)]|[nat2fin (CEO.conv3d_flat_j1_bound kk)]) (CG.vrd tmp)) ';
          output|{b}|{nu}|{i0}|{j0} |:= CD.add (CG.vrd tmp) (DE.idx bias nu)))))).

(* Window coordinate bound: the strided window base plus the kernel offset
   stays inside the 2*p + m padded array (needs n0 <= m). *)
Lemma conv4d_win_bound : forall (m n0 p s : nat) (Hs : s > 0) (Hn : n0 > 0)
  (Hnm : n0 <= m) (i0 : fin ((m - n0 + 2 * p) / s + 1)) (i1 : fin n0),
  fin2nat i0 * s + fin2nat i1 < 2 * p + m.
Proof.
  intros m n0 p s Hs Hn Hnm i0 i1.
  pose proof (fin_proof i0) as Hi0. pose proof (fin_proof i1) as Hi1.
  assert (Hle : fin2nat i0 <= (m - n0 + 2 * p) / s) by lia.
  assert (Hmul : s * fin2nat i0 <= m - n0 + 2 * p).
  { apply Nat.le_trans with (s * ((m - n0 + 2 * p) / s)).
    - apply Nat.mul_le_mono_l. exact Hle.
    - pose proof (Nat.div_mod_eq (m - n0 + 2 * p) s) as Hdm. lia. }
  lia.
Qed.

(* The 4-D padded read collapses to the route-A [pad_idx2d] read. *)
Lemma interp_pad4d_read : forall (h wd channel batch : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{h} (ary '{wd} num)))))
  (p : nat) (b : fin batch) (Hb : batch > 0) (ch : fin channel) (Hc : channel > 0)
  (t u : nat) (Ht : t < 2 * p + h) (Hu : u < 2 * p + wd) (rho : PCG.env),
  SEM.to_pcg_exp
    (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d p input)|[b]|[ch]) t) u) rho =
  OC.pad_idx2d p (PCG.idx (PCG.idx (SEM.to_pcg_exp input rho) b) ch) t u.
Proof.
  intros h wd channel batch input p b Hb ch Hc t u Ht Hu rho.
  unfold COP.Padding4d.
  rewrite (DE.idx_mkvSeq _ _ _ Hb).
  rewrite (BRC.interp_pad3d_read h wd channel (input|[b]) p ch Hc t u Ht Hu rho).
  rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Section Conv4d_Sem.

Variables (batch m1 m2 n1 n2 channel filernum p s : nat)
  (bias : DE.exp (ary '{filernum} num))
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))).
Hypothesis Hs : s > 0.
Hypothesis Hbatch : batch > 0.
Hypothesis Hchannel : channel > 0.
Hypothesis Hfilernum : filernum > 0.
Hypothesis Hn1 : n1 > 0.
Hypothesis Hn2 : n2 > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Hypothesis Hw_indep : SEM.exp_independent_of_acc w OSE.tmp_scalar_acc.
Hypothesis Hb_indep : SEM.exp_independent_of_acc bias OSE.tmp_scalar_acc.
Hypothesis Hinput_out : forall (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  SEM.exp_independent_of_acc input output.
Hypothesis Hw_out : forall (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  SEM.exp_independent_of_acc w output.
Hypothesis Hb_out : forall (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  SEM.exp_independent_of_acc bias output.

Let out_h := ((m1 - n1 + 2 * p) / s + 1).
Let out_w := ((m2 - n2 + 2 * p) / s + 1).

Definition tmp_disjoint_from_output_conv4d
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))) : Prop :=
  forall pth b nu i0 j0, @PCG.in_acc num pth OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num pth (output |{ b} |{ nu} |{ i0} |{ j0}).

(* Padding4d preserves independence (via the proved 3-D version). *)
Lemma Padding4d_independent : forall (d' : data) (a : DE.acc d'),
  SEM.exp_independent_of_acc input a ->
  SEM.exp_independent_of_acc (COP.Padding4d p input) a.
Proof.
  intros d' a Hin. unfold COP.Padding4d.
  apply SEM.exp_independent_of_acc_mkvSeq; intro b.
  apply OSE.Padding3d_independent.
  apply SEM.exp_independent_of_acc_idx. exact Hin.
Qed.

(* Bounds helpers for the sum-flattening proof (local copies of the
   [Operators_Sem_Equiv] Conv3d-section helpers, whose generalized forms
   drag in all of that section's positivity hypotheses). *)
Lemma conv4d_inner_i1_bound : forall (k2 : nat), k2 < n1 * n2 -> Nat.div k2 n2 < n1.
Proof.
  intros k2 Hk2. apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm. exact Hk2.
Qed.

Lemma conv4d_inner_j1_bound : forall (k2 : nat), k2 < n1 * n2 -> Nat.modulo k2 n2 < n2.
Proof.
  intros k2 Hk2. apply Nat.mod_upper_bound. lia.
Qed.

Lemma conv4d_outer_c_bound : forall (kk : nat),
  kk < channel * (n1 * n2) -> Nat.div kk (n1 * n2) < channel.
Proof.
  intros kk Hkk. apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm. exact Hkk.
Qed.

Lemma conv4d_outer_k2_bound : forall (kk : nat),
  kk < channel * (n1 * n2) -> Nat.modulo kk (n1 * n2) < n1 * n2.
Proof.
  intros kk Hkk. apply Nat.mod_upper_bound. lia.
Qed.

(* Functional and flat cell expressions. *)
Definition conv4d_idx_cell (b : fin batch) (nu : fin filernum)
  (i0 : fin out_h) (j0 : fin out_w)
  (ch : fin channel) (i1 : fin n1) (j1 : fin n2) : DE.exp num :=
  CD.mul (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d p input)|[b]|[ch])
             (fin2nat i0 * s + fin2nat i1)) (fin2nat j0 * s + fin2nat j1))
         w|[nu]|[ch]|[i1]|[j1].

Definition conv4d_flat_cell (b : fin batch) (nu : fin filernum)
  (i0 : fin out_h) (j0 : fin out_w) (kk : fin (channel * n1 * n2)) : DE.exp num :=
  let ch := Nat.div (fin2nat kk) (n1 * n2) in
  let i1 := Nat.div (Nat.modulo (fin2nat kk) (n1 * n2)) n2 in
  let j1 := Nat.modulo (fin2nat kk) n2 in
  CD.mul (CD.safe_idx_nat (CD.safe_idx_nat (COP.Padding4d p input)|[b]|[nat2fin (CEO.conv3d_flat_c_bound kk)]
             (fin2nat i0 * s + i1)) (fin2nat j0 * s + j1))
         w|[nu]|[nat2fin (CEO.conv3d_flat_c_bound kk)]
                |[nat2fin (CEO.conv3d_flat_i1_bound kk)]
                |[nat2fin (CEO.conv3d_flat_j1_bound kk)].

Lemma conv4d_flat_cell_unfold : forall b nu i0 j0 kk,
  conv4d_flat_cell b nu i0 j0 kk =
  conv4d_idx_cell b nu i0 j0 (nat2fin (CEO.conv3d_flat_c_bound kk))
                             (nat2fin (CEO.conv3d_flat_i1_bound kk))
                             (nat2fin (CEO.conv3d_flat_j1_bound kk)).
Proof.
  intros. unfold conv4d_flat_cell, conv4d_idx_cell.
  repeat f_equal;
    apply fin_eq'; simpl; rewrite ?fin2nat_nat2fin; reflexivity.
Qed.

(* The channel/kernel-window triple sum flattens to the single flat sum
   (mirror of [Operators_Sem_Equiv.Conv3d_sum_flatten]). *)
Lemma conv4d_sum_flatten : forall (b : fin batch) (nu : fin filernum)
  (i0 : fin out_h) (j0 : fin out_w) (rho : PCG.env),
  SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) rho =
  SEM.to_pcg_exp (CD.sum (DE.mkvSeq (conv4d_flat_cell b nu i0 j0))) rho.
Proof.
  intros b nu i0 j0 rho.
  set (idx_cell := fun (ch : nat) (Hc : ch < channel) (i1 : nat) (Hi1 : i1 < n1) (j1 : nat) (Hj1 : j1 < n2) =>
    SEM.to_pcg_exp (conv4d_idx_cell b nu i0 j0 (nat2fin Hc) (nat2fin Hi1) (nat2fin Hj1)) rho).
  set (g_inner := fun (ch : nat) (Hc : ch < channel) (k2 : nat) (Hk2 : k2 < n1 * n2) =>
    SEM.to_pcg_exp (conv4d_idx_cell b nu i0 j0 (nat2fin Hc)
      (nat2fin (conv4d_inner_i1_bound _ Hk2))
      (nat2fin (conv4d_inner_j1_bound _ Hk2))) rho).
  set (g_outer := fun (kk : nat) (Hkk : kk < channel * n1 * n2) =>
    SEM.to_pcg_exp (conv4d_flat_cell b nu i0 j0 (nat2fin Hkk)) rho).
  assert (Heq_lhs : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) rho =
    OSE.sumR_nat_fin (fun ch Hcc => OSE.sumR_nat_fin (fun i1 Hi1 => OSE.sumR_nat_fin (fun j1 Hj1 =>
      idx_cell ch Hcc i1 Hi1 j1 Hj1)))).
  { rewrite OSE.to_pcg_exp_sum_nat by nia.
    apply OSE.sumR_nat_fin_eq; intros ch Hcc.
    rewrite OSE.to_pcg_exp_sum_nat by nia.
    apply OSE.sumR_nat_fin_eq; intros i1 Hi1.
    rewrite OSE.to_pcg_exp_sum_nat by nia.
    apply OSE.sumR_nat_fin_eq; intros j1 Hj1.
    reflexivity. }
  assert (Heq_rhs : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (conv4d_flat_cell b nu i0 j0))) rho =
    OSE.sumR_nat_fin (fun kk Hkk => g_outer kk Hkk)).
  { rewrite OSE.to_pcg_exp_sum_nat by nia.
    apply OSE.sumR_nat_fin_eq; intros kk Hkk.
    reflexivity. }
  rewrite Heq_lhs, Heq_rhs.
  assert (Hinner :
    OSE.sumR_nat_fin (fun ch Hcc => OSE.sumR_nat_fin (fun i1 Hi1 => OSE.sumR_nat_fin (fun j1 Hj1 =>
      idx_cell ch Hcc i1 Hi1 j1 Hj1))) =
    OSE.sumR_nat_fin (fun ch Hcc => OSE.sumR_nat_fin (fun k2 Hk2 => g_inner ch Hcc k2 Hk2))).
  { apply OSE.sumR_nat_fin_eq; intros ch Hcc.
    pose (lemma := @OSE.sumR_nat_fin_nested_flat' n1 n2 Hn1 Hn2
      (fun i1 j1 Hi1 Hj1 => idx_cell ch Hcc i1 Hi1 j1 Hj1)
      (fun k2 Hk2 => g_inner ch Hcc k2 Hk2)
      (fun k2 Hk2 => conj (conv4d_inner_i1_bound _ Hk2) (conv4d_inner_j1_bound _ Hk2))).
    apply lemma;
      [ intros i1 j1 Hi1 Hi1' Hj1 Hj1'; unfold idx_cell;
        repeat rewrite SEM.to_pcg_exp_idx; f_equal; apply fin_eq';
        rewrite !fin2nat_nat2fin; reflexivity
      | intros k2 Hk2; unfold g_inner, idx_cell; reflexivity ]. }
  assert (Houter :
    OSE.sumR_nat_fin (fun ch Hc => OSE.sumR_nat_fin (fun k2 Hk2 => g_inner ch Hc k2 Hk2)) =
    OSE.sumR_nat_fin (fun kk Hkk => g_outer kk Hkk)).
  { assert (Houter' :
      OSE.sumR_nat_fin (fun ch Hc => OSE.sumR_nat_fin (fun k2 Hk2 => g_inner ch Hc k2 Hk2)) =
      OSE.sumR_nat_fin (fun kk Hkk => g_outer kk (eq_rect _ (fun x => kk < x) Hkk _ (Nat.mul_assoc channel n1 n2)))).
    { refine (@OSE.sumR_nat_fin_nested_flat' channel (n1 * n2) Hchannel (Nat.mul_pos_pos n1 n2 Hn1 Hn2)
        (fun ch k2 Hc Hk2 =>
           SEM.to_pcg_exp (conv4d_idx_cell b nu i0 j0 (nat2fin Hc)
             (nat2fin (conv4d_inner_i1_bound _ Hk2))
             (nat2fin (conv4d_inner_j1_bound _ Hk2))) rho)
        (fun kk Hkk =>
           SEM.to_pcg_exp (conv4d_flat_cell b nu i0 j0
             (nat2fin (eq_rect _ (fun x => kk < x) Hkk _ (Nat.mul_assoc channel n1 n2)))) rho)
        (fun kk Hkk => conj (conv4d_outer_c_bound _ Hkk) (conv4d_outer_k2_bound _ Hkk)) _ _).
      - intros ch k2 Hc1 Hc2 Hk1 Hk2.
        repeat rewrite SEM.to_pcg_exp_idx; f_equal; apply fin_eq';
        rewrite !fin2nat_nat2fin; reflexivity.
      - intros kk Hkk.
        rewrite conv4d_flat_cell_unfold.
        assert (Hc_eq : nat2fin (CEO.conv3d_flat_c_bound
          (nat2fin (eq_rect _ (fun x => kk < x) Hkk _ (Nat.mul_assoc channel n1 n2)))) =
          nat2fin (conv4d_outer_c_bound _ Hkk)).
        { apply fin_eq'; cbn; reflexivity. }
        assert (Hi1_eq : nat2fin (CEO.conv3d_flat_i1_bound
          (nat2fin (eq_rect _ (fun x => kk < x) Hkk _ (Nat.mul_assoc channel n1 n2)))) =
          nat2fin (conv4d_inner_i1_bound _ (conv4d_outer_k2_bound _ Hkk))).
        { apply fin_eq'; cbn; reflexivity. }
        assert (Hj1_eq : nat2fin (CEO.conv3d_flat_j1_bound
          (nat2fin (eq_rect _ (fun x => kk < x) Hkk _ (Nat.mul_assoc channel n1 n2)))) =
          nat2fin (conv4d_inner_j1_bound _ (conv4d_outer_k2_bound _ Hkk))).
        { apply fin_eq'; cbn; rewrite OSE.mod_mul_r_mod_self by lia; reflexivity. }
        rewrite Hc_eq, Hi1_eq, Hj1_eq.
        reflexivity. }
    rewrite Houter'.
    apply OSE.sumR_nat_fin_proof_irrelevance_bound.
    exact (Nat.mul_assoc channel n1 n2).
    intros kk H1 H2. unfold g_outer.
    repeat f_equal; apply proof_irrelevance. }
  rewrite Hinner, Houter. reflexivity.
Qed.

Lemma conv4d_cell_independent_of_output : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  SEM.exp_independent_of_acc (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu)) output.
Proof.
  intros output b nu i0 j0.
  apply SEM.exp_independent_of_acc_add.
  - apply OSE.exp_independent_of_acc_sum; intro ch.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold conv4d_idx_cell.
    apply SEM.exp_independent_of_acc_mul.
    + repeat apply OSE.safe_idx_nat_independent.
      apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx.
      apply Padding4d_independent.
      apply Hinput_out.
    + repeat apply SEM.exp_independent_of_acc_idx.
      apply Hw_out.
  - apply SEM.exp_independent_of_acc_idx.
    apply Hb_out.
Qed.

Lemma conv4d_cell_independent_of_tmp : forall
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  SEM.exp_independent_of_acc (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) OSE.tmp_scalar_acc.
Proof.
  intros b nu i0 j0.
  apply OSE.exp_independent_of_acc_sum; intro ch.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum; intro i1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  unfold conv4d_idx_cell.
  apply SEM.exp_independent_of_acc_mul.
  - repeat apply OSE.safe_idx_nat_independent.
    apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_idx.
    apply Padding4d_independent.
    exact Hinput_indep.
  - repeat apply SEM.exp_independent_of_acc_idx.
    exact Hw_indep.
Qed.

Lemma conv4d_cell_continuation_ok : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  tmp_disjoint_from_output_conv4d output ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => output|{b}|{nu}|{i0}|{j0} |:= CD.add r (DE.idx bias nu))
    (CD.sum (DE.mkvSeq (conv4d_flat_cell b nu i0 j0))).
Proof.
  intros output b nu i0 j0 Hdisj.
  apply OSE.scalar_assign_continuation_ok.
  - intros p0 Hp Hout. apply (Hdisj p0 b nu i0 j0 Hp). exact Hout.
  - apply OSE.exp_independent_of_acc_sum; intro kk.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold conv4d_flat_cell.
    apply SEM.exp_independent_of_acc_mul.
    + repeat apply OSE.safe_idx_nat_independent.
      apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx.
      apply Padding4d_independent.
      exact Hinput_indep.
    + repeat apply SEM.exp_independent_of_acc_idx.
      exact Hw_indep.
  - apply SEM.exp_independent_of_acc_add.
    + apply OSE.exp_independent_of_acc_sum; intro kk.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      unfold conv4d_flat_cell.
      apply SEM.exp_independent_of_acc_mul.
      * repeat apply OSE.safe_idx_nat_independent.
        apply SEM.exp_independent_of_acc_idx.
        apply SEM.exp_independent_of_acc_idx.
        apply Padding4d_independent.
        exact Hinput_indep.
      * repeat apply SEM.exp_independent_of_acc_idx.
        exact Hw_indep.
    + apply SEM.exp_independent_of_acc_idx.
      exact Hb_indep.
  - intros rho eta v Hv Heta.
    rewrite !OSE.to_pcg_exp_add; f_equal.
    + unfold CG.vrd. simpl. rewrite SEM.to_pcg_exp_REvar.
      rewrite PCG.update_eq by reflexivity.
      symmetry. exact Hv.
    + apply SEM.exp_independent_of_acc_eval with (a := OSE.tmp_scalar_acc).
      * apply SEM.exp_independent_of_acc_idx.
        exact Hb_indep.
      * intros q Hq. rewrite PCG.update_neq by (intro Hc0; apply Hq; simpl; auto).
        apply Heta. intro Hc0. apply Hq. simpl. auto.
Qed.


Theorem Conv4d_sem : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))) (rho : PCG.env),
  tmp_disjoint_from_output_conv4d output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CG.A (output, COP.Conv4d p s bias w input)) rho =
  SEM.eval (Conv4d_ast_comm p s bias w input output) rho.
Proof.
  intros output rho Hdisj Hundef.
  unfold CG.A, COP.Conv4d, CD.let_binding, Conv4d_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin out_h =>
        DE.mkvSeq (fun j0 : fin out_w =>
          CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply conv4d_cell_independent_of_output. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* batch slice b *)
          assert (Hcell_b : forall nu i0 j0,
        SEM.exp_independent_of_acc
          (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
          (output |{ b})).
      { intros nu i0 j0 p0 Hp.
        apply (conv4d_cell_independent_of_output output b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
        exact Hp. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros nu;
      apply SEM.exp_independent_of_acc_mkvSeq; intros i0;
      apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_b ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros nu eta' HPeta'. split.
    + (* channel slice nu *)
            assert (Hcell_nu : forall i0 j0,
        SEM.exp_independent_of_acc
          (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
          ((output |{ b}) |{ nu})).
      { intros i0 j0 p0 Hp.
        apply (conv4d_cell_independent_of_output output b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
        exact Hp. }
      rewrite SEM.eval_mkvSeq; [ | intros i0;
        apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_nu ].
      rewrite !SEM.eval_seqfor.
      apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros i0 eta'' HPeta''. split.
      * (* row i0 *)
              assert (Hcell_i0 : forall j0,
        SEM.exp_independent_of_acc
          (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
          (((output |{ b}) |{ nu}) |{ i0})).
      { intros j0 p0 Hp.
        apply (conv4d_cell_independent_of_output output b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
        exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- (* the cell: loopacc elimination *)
           set (e := DE.mkvSeq (conv4d_flat_cell b nu i0 j0)).
           set (c := fun r : DE.exp num =>
             (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= CD.add r (DE.idx bias nu)).
           rewrite (FTac.reduce_loopacc_named_sem _ _ (fun tmp : string =>
             (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * n1 * n2) =>
               CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp)) eta''').
           2: { intros tmp. apply functional_extensionality. intro rho1.
                cbn beta zeta iota. repeat f_equal.
                all: try reflexivity.
                all: try (apply functional_extensionality; intro kk; repeat f_equal;
                  assert (Heq : CD.mul (CD.safe_idx_nat (CD.safe_idx_nat (COP.Padding4d p input)|[b]|[nat2fin (CEO.conv3d_flat_c_bound kk)] (fin2nat i0 * s + Nat.div (Nat.modulo (fin2nat kk) (n1 * n2)) n2)) (fin2nat j0 * s + Nat.modulo (fin2nat kk) n2)) w|[nu]|[nat2fin (CEO.conv3d_flat_c_bound kk)]|[nat2fin (CEO.conv3d_flat_i1_bound kk)]|[nat2fin (CEO.conv3d_flat_j1_bound kk)] = DE.idx e kk)
                    by (unfold e, DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec; reflexivity);
                  rewrite Heq; reflexivity). }
           rewrite SEM.eval_assign.
           rewrite <- (SEM.eval_assign_aux 1 num _ _ eta''').
           change (SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
             (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * n1 * n2) =>
               CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp))) eta''').
           assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) eta''' =
             SEM.to_pcg_exp (CD.sum e) eta''').
           { unfold e. apply conv4d_sum_flatten. }
           assert (Heq_aux : SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval_aux (c (CD.sum e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal.
             rewrite !OSE.to_pcg_exp_add. f_equal.
             { exact Hsum_eq. } }
           rewrite Heq_aux.
           apply SEM.eval_csum_equiv.
           ++ exact HPeta'''.
           ++ unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              unfold conv4d_flat_cell.
              apply SEM.exp_independent_of_acc_mul.
              ** repeat apply OSE.safe_idx_nat_independent.
                 apply SEM.exp_independent_of_acc_idx.
                 apply SEM.exp_independent_of_acc_idx.
                 apply Padding4d_independent.
                 exact Hinput_indep.
              ** repeat apply SEM.exp_independent_of_acc_idx.
                 exact Hw_indep.
           ++ apply conv4d_cell_continuation_ok. exact Hdisj.
        -- rewrite SEM.eval_assign.
           apply OSE.assign_preserves_StructUndefined_tmp.
           ++ intros pth Hp Hout. apply (Hdisj pth b nu i0 j0 Hp). exact Hout.
           ++ exact HPeta'''.
      * rewrite SEM.eval_assign.
        apply PCG.StructUndefined_num.
        apply eq_trans with (y := eta'' OSE.tmp_path).
        -- rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
           apply PCG.seqfor_pointwise. intros j0 rho'.
           apply PCG.assign_not_in_acc.
           intros Hin. apply (Hdisj OSE.tmp_path b nu i0 j0 OSE.in_acc_tmp_scalar_acc).
           exact Hin.
        -- apply PCG.StructUndefined_num in HPeta''. exact HPeta''.
    + rewrite SEM.eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta' OSE.tmp_path).
      * rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros i0 rho'.
        rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros j0 rho''.
        apply PCG.assign_not_in_acc.
        intros Hin. apply (Hdisj OSE.tmp_path b nu i0 j0 OSE.in_acc_tmp_scalar_acc).
        exact Hin.
      * apply PCG.StructUndefined_num in HPeta'. exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros nu rho'.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros i0 rho''.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j0 rho'''.
      apply PCG.assign_not_in_acc.
      intros Hin. apply (Hdisj OSE.tmp_path b nu i0 j0 OSE.in_acc_tmp_scalar_acc).
      exact Hin.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

(* The body of [CNN_OP.Conv4d p s] folded with the cell definition. *)
Lemma conv4d_body :
  COP.Conv4d p s bias w input =
  DE.mkvSeq (fun b : fin batch => DE.mkvSeq (fun nu : fin filernum =>
    DE.mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
      DE.mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
        CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => conv4d_idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))))).
Proof. reflexivity. Qed.

(* Conv4d: pointwise functional interpretation lemma. *)
Lemma interp_Conv4d : forall (Hk1 : n1 <= m1) (Hk2 : n2 <= m2) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Conv4d p s bias w input) rho =
  OC.Conv4d p s (SEM.to_pcg_exp bias rho) (SEM.to_pcg_exp w rho)
    (SEM.to_pcg_exp input rho).
Proof.
  intros Hk1 Hk2 rho.
  rewrite conv4d_body. unfold OC.Conv4d.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  apply BRC.to_pcg_mkvSeq_ext; intro nu.
  apply BRC.to_pcg_mkvSeq_ext; intro i0.
  apply BRC.to_pcg_mkvSeq_ext; intro j0.
  unfold OC.Conv4dCell.
  rewrite SEM.to_pcg_exp_add, SEM.to_pcg_exp_idx.
  apply f_equal2; [ | reflexivity ].
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro ch.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i1.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j1.
  unfold conv4d_idx_cell. rewrite OSE.to_pcg_exp_mul.
  cbv [out_h out_w].
  rewrite (interp_pad4d_read m1 m2 channel batch input p b Hbatch ch Hchannel
    (fin2nat i0 * s + fin2nat i1) (fin2nat j0 * s + fin2nat j1)
    (conv4d_win_bound m1 n1 p s Hs Hn1 Hk1 i0 i1)
    (conv4d_win_bound m2 n2 p s Hs Hn2 Hk2 j0 j1) rho).
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

End Conv4d_Sem.



(* -------------------------------------------------------------------------- *)
(* Conv4d: comm-level bridge                                                  *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Conv4d : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hs : s > 0) (Hb : batch > 0) (Hc : channel > 0) (Hf : filernum > 0)
  (Hn1 : n1 > 0) (Hn2 : n2 > 0) (Hk1 : n1 <= m1) (Hk2 : n2 <= m2)
  (bias : DE.exp (ary '{filernum} num))
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc bias OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))),
     SEM.exp_independent_of_acc input output') ->
  (forall output' : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))),
     SEM.exp_independent_of_acc w output') ->
  (forall output' : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))),
     SEM.exp_independent_of_acc bias output') ->
  (forall pth b nu i0 j0, @PCG.in_acc num pth OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num pth (output |{ b} |{ nu} |{ i0} |{ j0})) ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (Conv4d_ast_comm p s bias w input output) rho =
  OC.Conv4d_comm p s (SEM.to_pcg_exp bias rho) (SEM.to_pcg_exp w rho)
    (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s Hs Hb Hc Hf Hn1 Hn2 Hk1 Hk2
    bias w input output rho Hi Hw Hbias Hio Hwo Hbo Hdisj Hundef.
  rewrite <- (Conv4d_sem batch m1 m2 n1 n2 channel filernum p s bias w input
    Hs Hb Hc Hf Hn1 Hn2 Hi Hw Hbias Hio Hwo Hbo output rho Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (OC.A_Conv4d batch m1 m2 n1 n2 channel filernum p s
    (SEM.to_pcg_exp bias rho) (SEM.to_pcg_exp w rho)
    (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Conv4d; assumption.
Qed.


(* -------------------------------------------------------------------------- *)
(* Maxpool4d_pad (general kernel/stride/padding; AlexNet overlapping pools)   *)
(*                                                                            *)
(*   Route B has no proved padded-maxpool semantic equivalence                *)
(*   ([CNN_Examples_Base.MaxPool4d_pad_equiv] is a reflexivity placeholder),  *)
(*   so this file supplies the loopacc-style AST command                      *)
(*   [Maxpool4d_pad_ast_comm] (mirroring [CNN_Examples_Base_Ops.Maxpool2d_    *)
(*   comm] with two more loop levels and [CNN_OP.Padding4d] reads) and proves *)
(*   [Maxpool4d_pad_sem] along the lines of [Operators_Sem_Equiv.Maxpool2d_   *)
(*   sem].  The functional interpretation reuses the route-A padding cell     *)
(*   [Ops_PoolPad.pad_expr]; the bridge targets [AlexNet_DPIA.Maxpool4d_      *)
(*   pad_comm] via [AlexNet_DPIA.A_Maxpool4d_pad].                            *)
(* -------------------------------------------------------------------------- *)

(* Route-B functional form (mirror of [AlexNet_DPIA.Maxpool4d_pad] in the     *)
(* syntactic [DataExp] model). *)
Definition maxp4dp_exp {batch filernum m1 m2 : nat}
  (kersize stride padding : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : DE.exp (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))) :=
  CD.let_binding (COP.Padding4d padding input) (fun pad =>
    DE.mkvSeq (fun b : fin batch => DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin ((m1 - kersize + 2 * padding) / stride + 1) =>
        DE.mkvSeq (fun j0 : fin ((m2 - kersize + 2 * padding) / stride + 1) =>
          CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize =>
            CD.safe_idx_nat (CD.safe_idx_nat pad|[b]|[nu]
              (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))))))).

Definition Maxpool4d_pad_ast_comm {batch filernum m1 m2 : nat}
  (kersize stride padding : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))) : CG.comm :=
  CG.seqfor (fun b : fin batch => CG.seqfor (fun nu : fin filernum =>
    CG.seqfor (fun i0 : fin ((m1 - kersize + 2 * padding) / stride + 1) =>
      CG.seqfor (fun j0 : fin ((m2 - kersize + 2 * padding) / stride + 1) =>
        @CG.loopacc num (fun tmp =>
          (CG.vwt tmp |:= CD.zero) ';
          CG.seqfor (fun kk : fin (kersize * kersize) =>
            If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (CG.vrd tmp))
              (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
          output|{b}|{nu}|{i0}|{j0} |:= (CG.vrd tmp : DE.exp num)))))).

Section Maxpool4d_pad_Sem.

Variables (batch filernum m1 m2 kersize stride padding : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))).
Hypothesis Hs : stride > 0.
Hypothesis Hbatch : batch > 0.
Hypothesis Hfilernum : filernum > 0.
Hypothesis Hk : kersize > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Hypothesis Hinput_out : forall (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))),
  SEM.exp_independent_of_acc input output.

Let out_h := ((m1 - kersize + 2 * padding) / stride + 1).
Let out_w := ((m2 - kersize + 2 * padding) / stride + 1).

Definition tmp_disjoint_from_output_maxp4dp
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))) : Prop :=
  forall pth b nu i0 j0, @PCG.in_acc num pth OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num pth (output |{ b} |{ nu} |{ i0} |{ j0}).

(* Flat window index bounds. *)
Lemma maxp4dp_window_bounds : forall (kk : fin (kersize * kersize)),
  Nat.div (fin2nat kk) kersize < kersize /\ Nat.modulo (fin2nat kk) kersize < kersize.
Proof.
  intro kk. destruct kk as [x Hx]. simpl. split.
  - apply Nat.div_lt_upper_bound; [lia | exact Hx].
  - apply Nat.mod_upper_bound. lia.
Qed.

(* Flat window cell, matching the loop body of [Maxpool4d_pad_ast_comm]. *)
Definition maxp4dp_flat_cell (b : fin batch) (nu : fin filernum)
  (i0 : fin out_h) (j0 : fin out_w) (kk : fin (kersize * kersize)) : DE.exp num :=
  CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize).

(* The nested functional window max equals the flattened max; both sides use
   the same [safe_idx_nat] reads, so the alignment is index arithmetic only. *)
Lemma maxp4dp_nested_max_flat : forall (b : fin batch) (nu : fin filernum)
  (i0 : fin out_h) (j0 : fin out_w) (rho : PCG.env),
  SEM.to_pcg_exp (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))) rho =
  SEM.to_pcg_exp (CD.max (DE.mkvSeq (maxp4dp_flat_cell b nu i0 j0))) rho.
Proof.
  intros b nu i0 j0 rho.
  set (idx_cell := fun (di dj : nat) (Hdi : di < kersize) (Hdj : dj < kersize) =>
    CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu])
      (fin2nat i0 * stride + fin2nat (nat2fin Hdi)))
      (fin2nat j0 * stride + fin2nat (nat2fin Hdj))).
  assert (Heq_lhs :
    SEM.to_pcg_exp (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))) rho =
    OSE.maxR_nat_fin (fun di Hdi => OSE.maxR_nat_fin (fun dj Hdj =>
      SEM.to_pcg_exp (idx_cell di dj Hdi Hdj) rho))).
  { rewrite OSE.to_pcg_exp_max_nat by exact Hk.
    apply OSE.maxR_nat_fin_eq. intros di Hdi.
    rewrite OSE.to_pcg_exp_max_nat by exact Hk.
    apply OSE.maxR_nat_fin_eq. intros dj Hdj.
    reflexivity. }
  assert (Heq_rhs :
    SEM.to_pcg_exp (CD.max (DE.mkvSeq (maxp4dp_flat_cell b nu i0 j0))) rho =
    OSE.maxR_nat_fin (fun kk (Hkk : kk < kersize * kersize) =>
      SEM.to_pcg_exp (maxp4dp_flat_cell b nu i0 j0 (nat2fin Hkk)) rho)).
  { rewrite OSE.to_pcg_exp_max_nat by nia. reflexivity. }
  rewrite Heq_lhs, Heq_rhs.
  pose (lemma := @OSE.maxR_nat_fin_nested_flat' kersize kersize Hk Hk
    (fun di dj Hdi Hdj => SEM.to_pcg_exp (idx_cell di dj Hdi Hdj) rho)
    (fun kk Hkk => SEM.to_pcg_exp (maxp4dp_flat_cell b nu i0 j0 (nat2fin Hkk)) rho)
    (fun kk Hkk => maxp4dp_window_bounds (nat2fin Hkk))).
  apply lemma.
  - intros di dj Hdi1 Hdi2 Hdj1 Hdj2.
    unfold idx_cell. rewrite !fin2nat_nat2fin. reflexivity.
  - intros kk Hkk.
    unfold maxp4dp_flat_cell, idx_cell.
    destruct (maxp4dp_window_bounds (nat2fin Hkk)) as [Hdi Hdj].
    rewrite !fin2nat_nat2fin. reflexivity.
Qed.

Lemma maxp4dp_cell_independent_of_output : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))))
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  SEM.exp_independent_of_acc (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))) output.
Proof.
  intros output b nu i0 j0.
  apply OSE.exp_independent_of_acc_max; intro i1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_max; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply OSE.safe_idx_nat_independent.
  apply SEM.exp_independent_of_acc_idx.
  apply SEM.exp_independent_of_acc_idx.
  apply Padding4d_independent.
  apply Hinput_out.
Qed.

Lemma maxp4dp_cell_continuation_ok : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))))
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  tmp_disjoint_from_output_maxp4dp output ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => output|{b}|{nu}|{i0}|{j0} |:= r)
    (CD.max (DE.mkvSeq (maxp4dp_flat_cell b nu i0 j0))).
Proof.
  intros output b nu i0 j0 Hdisj.
  apply OSE.scalar_assign_continuation_ok.
  - intros p0 Hp Hout. apply (Hdisj p0 b nu i0 j0 Hp). exact Hout.
  - apply OSE.exp_independent_of_acc_max; intro kk.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold maxp4dp_flat_cell.
    repeat apply OSE.safe_idx_nat_independent.
    apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_idx.
    apply Padding4d_independent.
    exact Hinput_indep.
  - apply OSE.exp_independent_of_acc_max; intro kk.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold maxp4dp_flat_cell.
    repeat apply OSE.safe_idx_nat_independent.
    apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_idx.
    apply Padding4d_independent.
    exact Hinput_indep.
  - intros rho eta v Hv Heta. cbv beta.
    rewrite SEM.to_pcg_exp_REvar_tmp'.
    rewrite SEM.value_at_update_same.
    symmetry. exact Hv.
Qed.

Theorem Maxpool4d_pad_sem : forall
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))) (rho : PCG.env),
  tmp_disjoint_from_output_maxp4dp output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CG.A (output, maxp4dp_exp kersize stride padding input)) rho =
  SEM.eval (Maxpool4d_pad_ast_comm kersize stride padding input output) rho.
Proof.
  intros output rho Hdisj Hundef.
  unfold CG.A, maxp4dp_exp, CD.let_binding, Maxpool4d_pad_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin out_h =>
        DE.mkvSeq (fun j0 : fin out_w =>
          CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply maxp4dp_cell_independent_of_output. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* batch slice b *)
          assert (Hcell_b : forall (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
        SEM.exp_independent_of_acc
          (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
          (output |{ b})).
      { intros nu i0 j0 p0 Hp.
        apply (maxp4dp_cell_independent_of_output output b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
        exact Hp. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros nu;
      apply SEM.exp_independent_of_acc_mkvSeq; intros i0;
      apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_b ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros nu eta' HPeta'. split.
    + (* channel slice nu *)
            assert (Hcell_nu : forall (i0 : fin out_h) (j0 : fin out_w),
        SEM.exp_independent_of_acc
          (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
          ((output |{ b}) |{ nu})).
      { intros i0 j0 p0 Hp.
        apply (maxp4dp_cell_independent_of_output output b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
        exact Hp. }
      rewrite SEM.eval_mkvSeq; [ | intros i0;
        apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_nu ].
      rewrite !SEM.eval_seqfor.
      apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros i0 eta'' HPeta''. split.
      * (* row i0 *)
              assert (Hcell_i0 : forall (j0 : fin out_w),
        SEM.exp_independent_of_acc
          (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
          (((output |{ b}) |{ nu}) |{ i0})).
      { intros j0 p0 Hp.
        apply (maxp4dp_cell_independent_of_output output b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
        exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- (* the cell: loopacc elimination *)
           set (e := DE.mkvSeq (maxp4dp_flat_cell b nu i0 j0)).
           set (c := fun r : DE.exp num =>
             (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= r).
           assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (kersize * kersize) =>
                 If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (CG.vrd tmp))
                   (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
               (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= (CG.vrd tmp : DE.exp num)))
             = (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (kersize * kersize) =>
                 If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                   (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
               (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= (CG.vrd tmp : DE.exp num)))).
           { f_equal. apply functional_extensionality; intro tmp.
             assert (Hfor : CG.seqfor (fun kk : fin (kersize * kersize) =>
                       If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (CG.vrd tmp))
                         (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))
                     = CG.seqfor (fun kk : fin (kersize * kersize) =>
                       If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                         (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))).
             { apply FTac.seqfor_extensionality; intro kk.
               assert (Heq : CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize) = DE.idx e kk).
               { unfold e, maxp4dp_flat_cell, DE.idx, DE.mkvSeq.
                 rewrite V.v_idx_mk_vec. reflexivity. }
               rewrite Heq. reflexivity. }
             rewrite Hfor. reflexivity. }
           rewrite Hrhs.
           rewrite SEM.eval_assign.
           rewrite <- (SEM.eval_assign_aux 1 num _ _ eta''').
           change (SEM.eval_aux (c (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (kersize * kersize) =>
                 If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                   (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
               c (CG.vrd tmp))) eta''').
           assert (Hmax_eq : SEM.to_pcg_exp (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))) eta''' =
             SEM.to_pcg_exp (CD.max e) eta''').
           { unfold e. apply maxp4dp_nested_max_flat. }
           assert (Heq_aux : SEM.eval_aux (c (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))) 1 eta''' =
             SEM.eval_aux (c (CD.max e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal. exact Hmax_eq. }
           rewrite Heq_aux.
           apply SEM.eval_cmax_equiv.
           ++ exact HPeta'''.
           ++ unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              unfold maxp4dp_flat_cell.
              repeat apply OSE.safe_idx_nat_independent.
              apply SEM.exp_independent_of_acc_idx.
              apply SEM.exp_independent_of_acc_idx.
              apply Padding4d_independent.
              exact Hinput_indep.
           ++ apply maxp4dp_cell_continuation_ok. exact Hdisj.
        -- rewrite SEM.eval_assign.
           apply OSE.assign_preserves_StructUndefined_tmp.
           ++ intros pth Hp Hout. apply (Hdisj pth b nu i0 j0 Hp). exact Hout.
           ++ exact HPeta'''.
      * rewrite SEM.eval_assign.
        apply PCG.StructUndefined_num.
        apply eq_trans with (y := eta'' OSE.tmp_path).
        -- rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
           apply PCG.seqfor_pointwise. intros j0 rho'.
           apply PCG.assign_not_in_acc.
           intros Hin. apply (Hdisj OSE.tmp_path b nu i0 j0 OSE.in_acc_tmp_scalar_acc).
           exact Hin.
        -- apply PCG.StructUndefined_num in HPeta''. exact HPeta''.
    + rewrite SEM.eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta' OSE.tmp_path).
      * rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros i0 rho'.
        rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros j0 rho''.
        apply PCG.assign_not_in_acc.
        intros Hin. apply (Hdisj OSE.tmp_path b nu i0 j0 OSE.in_acc_tmp_scalar_acc).
        exact Hin.
      * apply PCG.StructUndefined_num in HPeta'. exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros nu rho'.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros i0 rho''.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j0 rho'''.
      apply PCG.assign_not_in_acc.
      intros Hin. apply (Hdisj OSE.tmp_path b nu i0 j0 OSE.in_acc_tmp_scalar_acc).
      exact Hin.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

End Maxpool4d_pad_Sem.


(* The route-A in-bounds read via [Ops_PoolPad.safe_idx_nat]. *)
Lemma op_safe_idx_nat_lt : forall (n : nat) (t0 : data)
  (e : PCG.exp (ary '{n} t0)) (i : nat) (H : i < n),
  OP.safe_idx_nat e i = PCG.idx e (nat2fin H).
Proof.
  intros n t0 e i H. unfold OP.safe_idx_nat.
  destruct (Nat.ltb_spec0 i n) as [H1 | H1].
  - f_equal. apply fin_eq'. rewrite fin2nat_nat2fin. reflexivity.
  - contradiction.
Qed.

(* The [CNN_OP.Padding2d] cell as a standalone definition (mirrors the body
   of [CNN_OP.Padding2d] so that the interpretation lemma can name it). *)
Definition cop_pad_cell {n1 n2 : nat} (p : nat)
  (e : DE.exp (ary '{n1} (ary '{n2} num))) (x y : nat) : DE.exp num :=
  match Nat.ltb_spec0 x p with
  | ReflectT _ _ => DE.exp_default num
  | ReflectF _ H_ge_i =>
    match Nat.ltb_spec0 x (p + n1) with
    | ReflectT _ H_lt_i =>
      match Nat.ltb_spec0 y p with
      | ReflectT _ _ => DE.exp_default num
      | ReflectF _ H_ge_j =>
        match Nat.ltb_spec0 y (p + n2) with
        | ReflectT _ H_lt_j =>
          e|[nat2fin (@V.offset_proof_concise x p n1 H_lt_i H_ge_i)]
           |[nat2fin (@V.offset_proof_concise y p n2 H_lt_j H_ge_j)]
        | ReflectF _ _ => DE.exp_default num
        end
      end
    | ReflectF _ _ => DE.exp_default num
    end
  end.

(* [CNN_OP.Padding2d] folded with the cell definition. *)
Lemma cop_padding2d_body : forall (n1 n2 : nat) (p : nat)
  (e : DE.exp (ary '{n1} (ary '{n2} num))),
  COP.Padding2d p e =
  DE.mkvSeq (fun i : fin (2 * p + n1) =>
    DE.mkvSeq (fun j : fin (2 * p + n2) =>
      cop_pad_cell p e (fin2nat i) (fin2nat j))).
Proof. intros. reflexivity. Qed.

(* The syntactic padding cell reads as the route-A [pad_expr]. *)
Lemma interp_pad_expr : forall (n1 n2 : nat) (p x y : nat)
  (e : DE.exp (ary '{n1} (ary '{n2} num))) (rho : PCG.env),
  SEM.to_pcg_exp (cop_pad_cell p e x y) rho =
  OP.pad_expr (SEM.to_pcg_exp e rho) p x y.
Proof.
  intros n1 n2 p x y e rho.
  unfold cop_pad_cell, OP.pad_expr.
  destruct (Nat.ltb_spec0 x p) as [Hx | Hx].
  - change (DE.exp_default num) with CD.zero.
    rewrite SEM.to_pcg_exp_zero. reflexivity.
  - destruct (Nat.ltb_spec0 x (p + n1)) as [Hx2 | Hx2].
    + destruct (Nat.ltb_spec0 y p) as [Hy | Hy].
      * change (DE.exp_default num) with CD.zero.
        rewrite SEM.to_pcg_exp_zero. reflexivity.
      * destruct (Nat.ltb_spec0 y (p + n2)) as [Hy2 | Hy2].
        -- repeat rewrite SEM.to_pcg_exp_idx.
           apply f_equal2; [ | apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity ].
           apply f_equal2; [ reflexivity | ].
           apply fin_eq'; rewrite !fin2nat_nat2fin; reflexivity.
        -- change (DE.exp_default num) with CD.zero.
           rewrite SEM.to_pcg_exp_zero. reflexivity.
    + change (DE.exp_default num) with CD.zero.
      rewrite SEM.to_pcg_exp_zero. reflexivity.
Qed.

Lemma interp_padding2d : forall (n1 n2 : nat) (p : nat)
  (e : DE.exp (ary '{n1} (ary '{n2} num))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Padding2d p e) rho =
  OP.Padding2d p (SEM.to_pcg_exp e rho).
Proof.
  intros n1 n2 p e rho.
  rewrite cop_padding2d_body. unfold OP.Padding2d.
  apply BRC.to_pcg_mkvSeq_ext; intro i.
  apply BRC.to_pcg_mkvSeq_ext; intro j.
  apply interp_pad_expr.
Qed.

Lemma interp_padding3d : forall (channel n1 n2 : nat) (p : nat)
  (e : DE.exp (ary '{channel} (ary '{n1} (ary '{n2} num)))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Padding3d p e) rho =
  OP.Padding3d p (SEM.to_pcg_exp e rho).
Proof.
  intros channel n1 n2 p e rho.
  unfold COP.Padding3d, OP.Padding3d.
  apply BRC.to_pcg_mkvSeq_ext; intro c.
  rewrite (interp_padding2d n1 n2 p (e|[c]) rho).
  rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Lemma interp_padding4d : forall (batch channel n1 n2 : nat) (p : nat)
  (e : DE.exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Padding4d p e) rho =
  OP.Padding4d p (SEM.to_pcg_exp e rho).
Proof.
  intros batch channel n1 n2 p e rho.
  unfold COP.Padding4d, OP.Padding4d.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  rewrite (interp_padding3d channel n1 n2 p (e|[b]) rho).
  rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* The 2-D padded read, in-range case. *)
Lemma interp_safe2d_padding2d : forall (n1 n2 : nat) (p t u : nat)
  (e : DE.exp (ary '{n1} (ary '{n2} num)))
  (Ht : t < 2 * p + n1) (Hu : u < 2 * p + n2) (rho : PCG.env),
  SEM.to_pcg_exp (CD.safe_idx_nat (CD.safe_idx_nat (COP.Padding2d p e) t) u) rho =
  OP.safe_idx_nat (OP.safe_idx_nat (OP.Padding2d p (SEM.to_pcg_exp e rho)) t) u.
Proof.
  intros n1 n2 p t u e Ht Hu rho.
  rewrite (CD.safe_idx_nat_lt _ Ht). rewrite (CD.safe_idx_nat_lt _ Hu).
  rewrite (op_safe_idx_nat_lt _ _ _ _ Ht). rewrite (op_safe_idx_nat_lt _ _ _ _ Hu).
  rewrite cop_padding2d_body.
  rewrite !SEM.to_pcg_exp_idx. rewrite SEM.to_pcg_exp_mkvSeq.
  assert (Hpos1 : 2 * p + n1 > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ Hpos1). cbv beta.
  rewrite SEM.to_pcg_exp_mkvSeq.
  assert (Hpos2 : 2 * p + n2 > 0) by lia.
  rewrite (PCG.idx_mkvSeq _ _ _ Hpos2). cbv beta.
  unfold OP.Padding2d.
  rewrite (PCG.idx_mkvSeq _ _ _ Hpos1). cbv beta.
  rewrite (PCG.idx_mkvSeq _ _ _ Hpos2). cbv beta.
  rewrite !fin2nat_nat2fin.
  apply interp_pad_expr.
Qed.

(* The 4-D padded read at a strided window coordinate. *)
Lemma interp_maxp4dp_read : forall (batch channel n1 n2 : nat) (p t u : nat)
  (Hb : batch > 0) (Hc : channel > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (b : fin batch) (c : fin channel)
  (Ht : t < 2 * p + n1) (Hu : u < 2 * p + n2) (rho : PCG.env),
  SEM.to_pcg_exp
    (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d p input)|[b]|[c]) t) u) rho =
  OP.safe_idx_nat (OP.safe_idx_nat
    (PCG.idx (PCG.idx (OP.Padding4d p (SEM.to_pcg_exp input rho)) b) c) t) u.
Proof.
  intros batch channel n1 n2 p t u Hb Hc input b c Ht Hu rho.
  unfold COP.Padding4d, OP.Padding4d.
  rewrite (DE.idx_mkvSeq _ _ _ Hb).
  rewrite (PCG.idx_mkvSeq _ _ _ Hb).
  unfold COP.Padding3d, OP.Padding3d.
  rewrite (DE.idx_mkvSeq _ _ _ Hc).
  rewrite (PCG.idx_mkvSeq _ _ _ Hc).
  rewrite (interp_safe2d_padding2d n1 n2 p t u (input|[b]|[c]) Ht Hu rho).
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* Maxpool4d_pad: functional interpretation lemma. *)
Lemma interp_Maxpool4d_pad : forall (batch filernum m1 m2 kersize stride padding : nat)
  (Hbatch : batch > 0) (Hfilernum : filernum > 0)
  (Hk : kersize > 0) (Hs : stride > 0) (Hk1 : kersize <= m1) (Hk2 : kersize <= m2)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (rho : PCG.env),
  SEM.to_pcg_exp (maxp4dp_exp kersize stride padding input) rho =
  AD.Maxpool4d_pad kersize stride padding (SEM.to_pcg_exp input rho).
Proof.
  intros batch filernum m1 m2 kersize stride padding Hbatch Hfilernum Hk Hs
    Hk1 Hk2 input rho.
  unfold maxp4dp_exp, AD.Maxpool4d_pad.
  cbv [CD.let_binding PCG.let_binding]. cbv beta.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  apply BRC.to_pcg_mkvSeq_ext; intro nu.
  apply BRC.to_pcg_mkvSeq_ext; intro i0.
  apply BRC.to_pcg_mkvSeq_ext; intro j0.
  rewrite BRC.to_pcg_max_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i1.
  rewrite BRC.to_pcg_max_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro j1.
  apply (interp_maxp4dp_read batch filernum m1 m2 padding
    (fin2nat i0 * stride + fin2nat i1) (fin2nat j0 * stride + fin2nat j1)
    Hbatch Hfilernum input b nu
    (conv4d_win_bound m1 kersize padding stride Hs Hk Hk1 i0 i1)
    (conv4d_win_bound m2 kersize padding stride Hs Hk Hk2 j0 j1) rho).
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool4d_pad: comm-level bridge                                           *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_Maxpool4d_pad : forall
  (batch filernum m1 m2 kersize stride padding : nat)
  (Hb : batch > 0) (Hf : filernum > 0)
  (Hk : kersize > 0) (Hs : stride > 0) (Hk1 : kersize <= m1) (Hk2 : kersize <= m2)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum}
    (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
    (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  (forall output' : DE.acc (ary '{batch} (ary '{filernum}
     (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
     (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))),
     SEM.exp_independent_of_acc input output') ->
  (forall pth b nu i0 j0, @PCG.in_acc num pth OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num pth (output |{ b} |{ nu} |{ i0} |{ j0})) ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (Maxpool4d_pad_ast_comm kersize stride padding input output) rho =
  AD.Maxpool4d_pad_comm kersize stride padding (SEM.to_pcg_exp input rho) output rho.
Proof.
  intros batch filernum m1 m2 kersize stride padding Hb Hf Hk Hs Hk1 Hk2
    input output rho Hi Hio Hdisj Hundef.
  rewrite <- (Maxpool4d_pad_sem batch filernum m1 m2 kersize stride padding
    input Hs Hb Hf Hk Hi Hio output rho Hdisj Hundef).
  cbv [CG.A].
  rewrite SEM.eval_assign.
  rewrite <- (AD.A_Maxpool4d_pad batch filernum m1 m2 kersize stride padding
    (SEM.to_pcg_exp input rho) output).
  cbv [DR.A].
  f_equal.
  apply interp_Maxpool4d_pad; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions Bridge_Conv4d.
Print Assumptions Bridge_Flatten4d.
Print Assumptions Bridge_GlobalAvgPool4d.
Print Assumptions Bridge_Avgpool4d.
Print Assumptions Bridge_BatchNorm4d.
Print Assumptions Bridge_Maxpool4d_pad.
