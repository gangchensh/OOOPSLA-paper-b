(* ========================================================================= *)
(* Bridge_VGG16.v                                                            *)
(*                                                                           *)
(* Whole-network route-A/route-B bridge for VGG16:                           *)
(*                                                                           *)
(*   eval (AST-level VGG16) rho p  =  vgg16_comm (route A) ... rho p         *)
(*                                                                           *)
(* pointwise at every path [p] inside the output accumulator.                *)
(*                                                                           *)
(* Route B (code generation): the sequential composition of per-layer AST    *)
(*   commands ([Bridge_ReduceConv2.Conv4d_ast_comm] at p=1 s=1 k=3,          *)
(*   [CEO.ReLU4d_comm], [CEO.Maxpool4d_comm] at k=2, [CEB.Flatten4d_comm],   *)
(*   [CEO.Linear2d_comm], [CEB.ReLU2d_comm], [CEO.Softmax2d_comm]) writing   *)
(*   the named buffers "conv1_1_out" "relu1_1_out" ... "pool5_out"           *)
(*   "flatten_out" "fc1_out" "fc1_relu_out" "fc2_out" "fc2_relu_out"         *)
(*   "fc3_out" "output" (the buffer names of [CNN_Examples_VGG16], with a    *)
(*   final softmax stage appended so that the net matches route A).          *)
(* Route A (DPIA): [VGG16_DPIA.vgg16_comm] with its proved whole-network     *)
(*   collapse [VGG16_DPIA.A_VGG16].                                          *)
(*                                                                           *)
(* As in [Bridge_LeNet5], the route-B operator theorems                      *)
(*   ([Operators_Sem_Equiv.*_sem], [Bridge_ReduceConv2.Conv4d_sem])          *)
(*   universally quantify the output acceptor in their independence side     *)
(*   conditions ([forall output', exp_independent_of_acc input output']),    *)
(*   which is unsatisfiable for buffer-read inputs such as [vrd "pool1_out"] *)
(*   (take [output'] to be an acceptor covering the buffer's own paths).     *)
(*   This file therefore re-proves the route-B equivalences with             *)
(*   single-output side conditions ([Conv4d_sem_single],                     *)
(*   [Maxpool4d_sem_single], [Flatten4d_sem_single], [Linear2d_sem_single],  *)
(*   [Softmax2d_sem_single]) by replaying the original proofs with the       *)
(*   universally quantified independence premises replaced by the concrete   *)
(*   ones.  The heavy machinery is reused: [Bridge_ReduceConv2]'s conv4d     *)
(*   cell/sum-flattening/continuation lemmas and [interp_Conv4d], and        *)
(*   [Bridge_LeNet5]'s single-output 3d/1d variants                          *)
(*   ([Maxpool3d_sem_single], [Linear1d_sem_single], [Softmax1d_sem_single], *)
(*   [flatten_batch_sem_single]) plus its buffer-name infrastructure.        *)
(*                                                                           *)
(* The ReLU layers reuse [CEO.ReLU4d_equiv_sem]/[CEB.ReLU2d_equiv_sem]       *)
(*   (already single-output); as in [Bridge_LeNet5], the conversion of the   *)
(*   runtime boolean side condition to the static [bexp2bool] form is        *)
(*   packaged as a clean [Rle] premise on the functional pre-activation      *)
(*   values of each ReLU layer.                                              *)
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
  Ionia.Ops_Conv Ionia.Ops_Elementwise Ionia.Ops_PoolPad Ionia.Ops_Reduce
  Ionia.AlexNet_DPIA Ionia.VGG16_DPIA Ionia.FusionTactics
  Ionia.Bridge_ReduceConv Ionia.Bridge_ReduceConv2 Ionia.Bridge_Elementwise
  Ionia.Bridge_LeNet5.

Open Scope string_scope.

(* The buffer name types are local [Definition]s; see the note in
   [Bridge_LeNet5] on keyed unification. *)
Set Keyed Unification.

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
Module LF := Ionia.LeNet5_Functional.
Module OC := Ionia.Ops_Conv.
Module OE := Ionia.Ops_Elementwise.
Module OP := Ionia.Ops_PoolPad.
Module OR := Ionia.Ops_Reduce.
Module AD := Ionia.AlexNet_DPIA.
Module VD := Ionia.VGG16_DPIA.
Module BRC := Ionia.Bridge_ReduceConv.
Module B2 := Ionia.Bridge_ReduceConv2.
Module BEL := Ionia.Bridge_Elementwise.
Module BL := Ionia.Bridge_LeNet5.
Module V := Ionia.vector.
Module FTac := Ionia.FusionTactics.

(* String name-clash solvers for the concrete buffer names of the net. *)
Ltac str_neq_tac := intros u v Heq; discriminate.
Ltac str_neq1_tac := intros u Heq; discriminate.

(* Discharge [StructUndefined tmp] at any stage env. *)
Ltac su_tmp_tac :=
  repeat (apply BL.SU_tmp_after_assign_vwt; [ intros u Heq; discriminate | ]);
  assumption.

(* -------------------------------------------------------------------------- *)
(* tmp disjointness of 2d/4d output buffers (mirrors of [BL.tmp_disj_vwt1])   *)
(* -------------------------------------------------------------------------- *)

Lemma tmp_neq_vwt2 : forall (n1 n2 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (i : fin n1) (j : fin n2),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p ((@CG.vwt (ary '{n1} (ary '{n2} num)) s) |{ i} |{ j}).
Proof.
  intros n1 n2 s Hneq p i j Hp Hin.
  apply BL.in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

Lemma tmp_neq_vwt4 : forall (n1 n2 n3 n4 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (i1 : fin n1) (i2 : fin n2) (i3 : fin n3) (i4 : fin n4),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p
        ((@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} (ary '{n4} num)))) s)
           |{ i1} |{ i2} |{ i3} |{ i4}).
Proof.
  intros n1 n2 n3 n4 s Hneq p i1 i2 i3 i4 Hp Hin.
  apply BL.in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv4d: single-output semantic equivalence                                 *)
(* (replay of [Bridge_ReduceConv2.Conv4d_sem] with the universally            *)
(*  quantified independence hypotheses replaced by single-output ones)        *)
(* -------------------------------------------------------------------------- *)

Section Conv4d_Single.

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

Let out_h := ((m1 - n1 + 2 * p) / s + 1).
Let out_w := ((m2 - n2 + 2 * p) / s + 1).
Let idx_cell := B2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input.
Let flat_cell := B2.conv4d_flat_cell batch m1 m2 n1 n2 channel filernum p s w input.

Variable output : DE.acc (ary '{batch} (ary '{filernum} (ary '{out_h} (ary '{out_w} num)))).
Hypothesis Hinput_out : SEM.exp_independent_of_acc input output.
Hypothesis Hw_out : SEM.exp_independent_of_acc w output.
Hypothesis Hb_out : SEM.exp_independent_of_acc bias output.

(* Single-output analogue of [Bridge_ReduceConv2.conv4d_cell_independent_of_output]. *)
Lemma conv4d_cell_indep_single : forall
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  SEM.exp_independent_of_acc
    (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel =>
      (CD.sum (DE.mkvSeq (fun i1 : fin n1 =>
        (CD.sum (DE.mkvSeq (fun j1 : fin n2 =>
          idx_cell b nu i0 j0 ch i1 j1)))))))))
      (DE.idx bias nu))
    output.
Proof.
  intros b nu i0 j0.
  apply SEM.exp_independent_of_acc_add.
  - apply OSE.exp_independent_of_acc_sum; intro ch.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold idx_cell, B2.conv4d_idx_cell.
    apply SEM.exp_independent_of_acc_mul.
    + repeat apply OSE.safe_idx_nat_independent.
      apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx.
      apply B2.Padding4d_independent.
      exact Hinput_out.
    + repeat apply SEM.exp_independent_of_acc_idx.
      exact Hw_out.
  - apply SEM.exp_independent_of_acc_idx.
    exact Hb_out.
Qed.

Theorem Conv4d_sem_single : forall (rho : PCG.env),
  B2.tmp_disjoint_from_output_conv4d batch m1 m2 n1 n2 filernum p s output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CG.A (output, COP.Conv4d p s bias w input)) rho =
  SEM.eval (B2.Conv4d_ast_comm p s bias w input output) rho.
Proof.
  intros rho Hdisj Hundef.
  unfold CG.A, COP.Conv4d, CD.let_binding, B2.Conv4d_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin out_h =>
        DE.mkvSeq (fun j0 : fin out_w =>
          CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply conv4d_cell_indep_single. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* batch slice b *)
    assert (Hcell_b : forall nu i0 j0,
      SEM.exp_independent_of_acc
        (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
        (output |{ b})).
    { intros nu i0 j0 p0 Hp.
      apply (conv4d_cell_indep_single b nu i0 j0).
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
          (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
          ((output |{ b}) |{ nu})).
      { intros i0 j0 p0 Hp.
        apply (conv4d_cell_indep_single b nu i0 j0).
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
            (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
            (((output |{ b}) |{ nu}) |{ i0})).
        { intros j0 p0 Hp.
          apply (conv4d_cell_indep_single b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
          exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- (* the cell: loopacc elimination *)
           set (e := DE.mkvSeq (flat_cell b nu i0 j0)).
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
                    by (unfold e, flat_cell, B2.conv4d_flat_cell, DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec; reflexivity);
                  rewrite Heq; reflexivity). }
           rewrite SEM.eval_assign.
           rewrite <- (SEM.eval_assign_aux 1 num _ _ eta''').
           change (SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
             (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * n1 * n2) =>
               CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp))) eta''').
           assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1))))))) eta''' =
             SEM.to_pcg_exp (CD.sum e) eta''').
           { unfold e. apply (B2.conv4d_sum_flatten batch m1 m2 n1 n2 channel filernum p s
               w input Hs Hbatch Hchannel Hfilernum Hn1 Hn2). }
           assert (Heq_aux : SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idx_cell b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval_aux (c (CD.sum e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal.
             rewrite !OSE.to_pcg_exp_add. f_equal.
             { exact Hsum_eq. } }
           rewrite Heq_aux.
           apply SEM.eval_csum_equiv.
           ++ exact HPeta'''.
           ++ unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              unfold flat_cell, B2.conv4d_flat_cell.
              apply SEM.exp_independent_of_acc_mul.
              ** repeat apply OSE.safe_idx_nat_independent.
                 apply SEM.exp_independent_of_acc_idx.
                 apply SEM.exp_independent_of_acc_idx.
                 apply B2.Padding4d_independent.
                 exact Hinput_indep.
              ** repeat apply SEM.exp_independent_of_acc_idx.
                 exact Hw_indep.
           ++ apply (B2.conv4d_cell_continuation_ok batch m1 m2 n1 n2 channel filernum p s
                bias w input Hinput_indep Hw_indep Hb_indep output b nu i0 j0 Hdisj).
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

End Conv4d_Single.

(* -------------------------------------------------------------------------- *)
(* Maxpool4d: single-output semantic equivalence                              *)
(* (replay of [Operators_Sem_Equiv.Maxpool4d_sem]; the inner 3d instance is   *)
(*  [Bridge_LeNet5.Maxpool3d_sem_single])                                     *)
(* -------------------------------------------------------------------------- *)

Theorem Maxpool4d_sem_single : forall (batch filernum m1 m2 k : nat)
  (Hb : batch > 0) (Hf : filernum > 0) (Hk : k > 0)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  OSE.tmp_disjoint_from_output_maxp4d batch filernum m1 m2 k output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Maxpool4d batch filernum m1 m2 k input)) rho =
  SEM.eval (@CEO.Maxpool4d_comm batch filernum m1 m2 k input output) rho.
Proof.
  intros batch filernum m1 m2 k Hb Hf Hk input output rho Hi Hio Hdisj Hundef.
  unfold CG.A, COP.Maxpool4d, CEO.Maxpool4d_comm.
  assert (Hrow_indep : forall b,
    SEM.exp_independent_of_acc
      (DE.mkvSeq (fun nu : fin filernum => DE.mkvSeq (fun i0 : fin (m1/k) => DE.mkvSeq (fun i1 : fin (m2/k) =>
        (CD.max (DE.mkvSeq (fun j0 : fin k => (CD.max (DE.mkvSeq (fun j1 : fin k =>
          DE.idx (DE.idx (DE.idx (DE.idx input b) nu)
            (nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)))
            (nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1))))))))))))
      output).
  { intro b. apply SEM.exp_independent_of_acc_mkvSeq. intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq. intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq. intro i1.
    apply OSE.exp_independent_of_acc_max. intro j0.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_max. intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    repeat apply SEM.exp_independent_of_acc_idx. exact Hio. }
  rewrite SEM.eval_mkvSeq; [ | exact Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* Row equivalence reduces to the single-output 3D instance at [input|[b]]. *)
    assert (Hin3d : SEM.exp_independent_of_acc (DE.idx input b) (output |{ b})).
    { apply CEO.exp_independent_of_acc_weaken_ary.
      apply SEM.exp_independent_of_acc_idx. exact Hio. }
    assert (Hdisj3d : @OSE.tmp_disjoint_from_output_maxp3d filernum m1 m2 k (output |{ b})).
    { intros p nu i0 i1 Hp. exact (Hdisj p b nu i0 i1 Hp). }
    change (SEM.eval (CG.A ((output |{ b}), @COP.Maxpool3d filernum m1 m2 k (DE.idx input b))) eta =
            SEM.eval (@CEO.Maxpool3d_comm filernum m1 m2 k (DE.idx input b) (output |{ b})) eta).
    apply (BL.Maxpool3d_sem_single filernum m1 m2 k Hf Hk (DE.idx input b) (output |{ b}) eta).
    + apply SEM.exp_independent_of_acc_idx. exact Hi.
    + exact Hin3d.
    + exact Hdisj3d.
    + exact HPeta.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + apply PCG.assign_not_in_acc.
      intros Hc. simpl in Hc. destruct Hc as [nu Hc]. simpl in Hc. destruct Hc as [i0 Hc].
      simpl in Hc. destruct Hc as [i1 Hc].
      exact (Hdisj OSE.tmp_path b nu i0 i1 OSE.in_acc_tmp_scalar_acc Hc).
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

(* -------------------------------------------------------------------------- *)
(* Flatten4d: single-output semantic equivalence                              *)
(* (replay of [Operators_Sem_Equiv.Flatten4d_sem]; the per-batch instance is  *)
(*  [Bridge_LeNet5.flatten_batch_sem_single])                                 *)
(* -------------------------------------------------------------------------- *)

Theorem Flatten4d_sem_single : forall (batch channel m1 m2 : nat)
  (Hb : batch > 0) (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel * m1 * m2} num)))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input output ->
  OSE.tmp_disjoint_from_output2d batch (channel * m1 * m2) output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Flatten4d batch channel m1 m2 input)) rho =
  SEM.eval (@CEB.Flatten4d_comm batch channel m1 m2 input output) rho.
Proof.
  intros batch channel m1 m2 Hb Hc Hm1 Hm2 input output rho Hio Hdisj Hundef.
  unfold CG.A, COP.Flatten4d, CEB.Flatten4d_comm.
  assert (Hrow_indep : forall b,
    SEM.exp_independent_of_acc (CD.join (CD.join (DE.idx input b))) output).
  { intro b. rewrite (OSE.join_mkvSeq (CD.join (DE.idx input b))).
    rewrite (OSE.join_mkvSeq (DE.idx input b)).
    apply SEM.exp_independent_of_acc_mkvSeq. intro i.
    destruct (V.idx_1d_to_2d i) as [x y].
    repeat apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_mkvSeq. intro k.
    destruct (V.idx_1d_to_2d k) as [z w0].
    repeat apply SEM.exp_independent_of_acc_idx.
    exact Hio. }
  rewrite SEM.eval_mkvSeq; [ | exact Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [ exact Hundef | ].
  intros b eta HPeta. split.
  - rewrite SEM.eval_assign. rewrite !SEM.eval_seqfor.
    apply (BL.flatten_batch_sem_single batch channel m1 m2 input Hc Hm1 Hm2 (output |{ b}) b eta).
    apply CEO.exp_independent_of_acc_weaken_ary.
    apply SEM.exp_independent_of_acc_idx. exact Hio.
  - rewrite SEM.eval_assign.
    apply SEM.PCG_assign_preserves_StructUndefined.
    + exact HPeta.
    + intros p Hp Hout. simpl in Hout. destruct Hout as [out Hout'].
      apply (Hdisj p b out Hp). exact Hout'.
Qed.

(* -------------------------------------------------------------------------- *)
(* Linear2d: single-output semantic equivalence                               *)
(* (per-batch reduction to [Bridge_LeNet5.Linear1d_sem_single])               *)
(* -------------------------------------------------------------------------- *)

Theorem Linear2d_sem_single : forall (batch m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{outnum} num))) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc b OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc b output ->
  OSE.tmp_disjoint_from_output2d batch outnum output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Linear2d batch m outnum w b input)) rho =
  SEM.eval (@CEO.Linear2d_comm batch m outnum w b input output) rho.
Proof.
  intros batch m outnum w b input output rho Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  unfold CG.A, COP.Linear2d, CEO.Linear2d_comm.
  assert (Hrow_indep : forall bi,
    SEM.exp_independent_of_acc (COP.Linear w b (DE.idx input bi)) output).
  { intros bi. unfold COP.Linear.
    apply SEM.exp_independent_of_acc_mkvSeq. intro out.
    apply SEM.exp_independent_of_acc_add.
    - apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply SEM.exp_independent_of_acc_mul.
      + repeat apply SEM.exp_independent_of_acc_idx. exact Hio.
      + repeat apply SEM.exp_independent_of_acc_idx. exact Hwo.
    - apply SEM.exp_independent_of_acc_idx. exact Hbo. }
  rewrite SEM.eval_mkvSeq; [ | exact Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros bi eta HPeta. split.
  - change (SEM.eval (CG.A ((output |{ bi}), COP.Linear w b (DE.idx input bi))) eta =
            SEM.eval (@CEO.Linear1d_comm m outnum w b (DE.idx input bi) (output |{ bi})) eta).
    apply (BL.Linear1d_sem_single m outnum w b (DE.idx input bi) (output |{ bi}) eta).
    + apply SEM.exp_independent_of_acc_idx. exact Hi.
    + exact Hw.
    + exact Hb.
    + apply CEO.exp_independent_of_acc_weaken_ary.
      apply SEM.exp_independent_of_acc_idx. exact Hio.
    + apply CEO.exp_independent_of_acc_weaken_ary. exact Hwo.
    + apply CEO.exp_independent_of_acc_weaken_ary. exact Hbo.
    + intros p out Hp. exact (Hdisj p bi out Hp).
    + exact HPeta.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros out rho'. apply PCG.assign_not_in_acc.
      intros Hc. apply (Hdisj OSE.tmp_path bi out OSE.in_acc_tmp_scalar_acc). exact Hc.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

(* -------------------------------------------------------------------------- *)
(* Softmax2d: single-output semantic equivalence                              *)
(* (replay of [Operators_Sem_Equiv.Softmax2d_sem])                            *)
(* -------------------------------------------------------------------------- *)

(* Single-output analogue of [Operators_Sem_Equiv.Softmax2d_batch_continuation_ok]. *)
Lemma softmax2d_row_continuation_ok_single : forall (batch m : nat)
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{m} num))) (b : fin batch),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input (output |{ b}) ->
  (forall (p : DE.path) (j : fin m),
     @PCG.in_acc num p OSE.tmp_scalar_acc -> ((output |{ b}) |{ j}) <> p) ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => CG.seqfor (fun j : fin m =>
       ((output |{ b}) |{ j}) |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) r))
    (CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp (DE.idx (DE.idx input b) i)))).
Proof.
  intros batch m input output b Hi Hinput_row Hdisj_row.
  set (e_final := CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp (DE.idx (DE.idx input b) i)))).
  set (g := fun (j : fin m) (r : DE.exp num) => CD.div (CD.pExp (DE.idx (DE.idx input b) j)) r).
  assert (Hdisj_acc : OSE.tmp_disjoint_from_acc (output |{ b})).
  { intros p Hp Hout. unfold PCG.in_acc in Hout. simpl in Hout.
    destruct Hout as [j Hj]. simpl in Hj. assert (Hc := Hdisj_row p j Hp Hj). contradiction. }
  apply OSE.seqfor_scalar_assign_continuation_ok.
  - exact Hdisj_acc.
  - unfold e_final. apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_idx. exact Hi.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx. exact Hi.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx. exact Hi.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
  - intros j. unfold g. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
    + apply OSE.exp_independent_of_acc_REvar.
      intro Hc. apply (Hdisj_acc (DE.Var "__tmp") OSE.in_acc_tmp_scalar_acc Hc).
  - intros j rho0 eta v Hv Heta.
    rewrite !OSE.to_pcg_exp_div; f_equal.
    + rewrite !OSE.to_pcg_exp_pExp; f_equal.
      apply SEM.exp_independent_of_acc_eval with (a := OSE.tmp_scalar_acc).
      * apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hi.
      * intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
        apply Heta. intro Hc. apply Hq. simpl. auto.
    + unfold CG.vrd. simpl. rewrite SEM.to_pcg_exp_REvar.
      rewrite PCG.update_eq by reflexivity. symmetry. exact Hv.
Qed.

Theorem Softmax2d_sem_single : forall (batch m : nat)
  (Hb : batch > 0) (Hm : m > 0)
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{m} num))) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  (forall (p : DE.path) (b : fin batch) (j : fin m),
     @PCG.in_acc num p OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num p ((output |{ b}) |{ j})) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Softmax2d batch m input)) rho =
  SEM.eval (@CEO.Softmax2d_comm batch m input output) rho.
Proof.
  intros batch m Hb Hm input output rho Hi Hio Hdisj Hundef.
  unfold CG.A, COP.Softmax2d, CEO.Softmax2d_comm, CD.let_binding.
  set (s := DE.mkvSeq (fun b : fin batch =>
    CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp (DE.idx (DE.idx input b) i))))).
  set (row := fun b : fin batch => DE.mkvSeq (fun j : fin m =>
    CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b))).
  assert (Hs_indep : SEM.exp_independent_of_acc s output).
  { unfold s. apply SEM.exp_independent_of_acc_mkvSeq. intro b'.
    apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx.
    exact Hio. }
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros j.
    apply SEM.exp_independent_of_acc_div.
    - apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx.
      exact Hio.
    - apply SEM.exp_independent_of_acc_idx. exact Hs_indep. }
  rewrite SEM.eval_mkvSeq; [ | exact Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - assert (Hinput_row : SEM.exp_independent_of_acc input (output |{ b})).
    { apply CEO.exp_independent_of_acc_weaken_ary. exact Hio. }
    assert (Hs_row : SEM.exp_independent_of_acc s (output |{ b})).
    { unfold s. apply SEM.exp_independent_of_acc_mkvSeq. intro b'.
      apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx.
      exact Hinput_row. }
    assert (Hcell_indep_b : forall j,
      SEM.exp_independent_of_acc
        (CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b)) (output |{ b})).
    { intros j. apply SEM.exp_independent_of_acc_div.
      - apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx.
        exact Hinput_row.
      - apply SEM.exp_independent_of_acc_idx. exact Hs_row. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros j; apply Hcell_indep_b ].
    apply eq_trans with (y := SEM.eval_aux (CG.seqfor (fun j : fin m =>
      (output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b))) 1 eta).
    + rewrite SEM.eval_seqfor.
      assert (Hpoint : forall j,
        SEM.eval ((output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b)) =
        SEM.eval_aux ((output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b)) 1).
      { intro j. apply functional_extensionality; intro rho''.
        rewrite SEM.eval_assign. symmetry. apply SEM.eval_assign_aux. }
      replace (PCG.seqfor (fun j : fin m =>
                 SEM.eval ((output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b))) eta)
        with (PCG.seqfor (fun j : fin m =>
                 SEM.eval_aux ((output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (DE.idx s b)) 1) eta).
      2: { apply f_equal with (f := fun h => PCG.seqfor h eta).
           apply functional_extensionality; intro j. symmetry. apply Hpoint. }
      rewrite SEM.eval_seqfor_aux. reflexivity.
    + set (e := DE.mkvSeq (fun i : fin m => CD.pExp (DE.idx (DE.idx input b) i))).
      assert (Heq : DE.idx s b = CD.sum e).
      { unfold e, s, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
      rewrite Heq.
      set (c := fun r : DE.exp num => CG.seqfor (fun j : fin m =>
        (output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) r)).
      assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (CD.pExp (DE.idx (DE.idx input b) i)) (CG.vrd tmp)) ';
          CG.seqfor (fun j : fin m =>
            (output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (CG.vrd tmp))))
        = (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp)) ';
          CG.seqfor (fun j : fin m =>
            (output |{ b}) |{ j} |:= CD.div (CD.pExp (DE.idx (DE.idx input b) j)) (CG.vrd tmp))))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (CD.pExp (DE.idx (DE.idx input b) i)) (CG.vrd tmp))
                    = CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))).
        { apply FTac.seqfor_extensionality; intro i.
          assert (Heq_i : CD.pExp (DE.idx (DE.idx input b) i) = DE.idx e i).
          { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq_i. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      apply (@SEM.eval_csum_equiv m e c eta).
      * exact HPeta.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro i.
        apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx.
        exact Hi.
      * apply (softmax2d_row_continuation_ok_single batch m input output b).
        -- exact Hi.
        -- exact Hinput_row.
        -- intros p j' Hp Hc. apply (Hdisj p b j' Hp). simpl. rewrite Hc. simpl. reflexivity.
  - rewrite SEM.eval_assign.
    assert (Hpres : PCG.assign (output |{ b}) (SEM.to_pcg_exp (row b) eta) eta OSE.tmp_path =
      eta OSE.tmp_path).
    { unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j rho'.
      apply PCG.assign_not_in_acc.
      intros Hc. apply (Hdisj OSE.tmp_path b j OSE.in_acc_tmp_scalar_acc). exact Hc. }
    apply PCG.StructUndefined_num. apply eq_trans with (y := eta OSE.tmp_path).
    + exact Hpres.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

(* -------------------------------------------------------------------------- *)
(* ReLU2d / Linear2d / Softmax2d: functional interpretation lemmas            *)
(* -------------------------------------------------------------------------- *)

Lemma interp_ReLU2d : forall (m1 m2 : nat)
  (input : DE.exp (ary '{m1} (ary '{m2} num))) (rho : PCG.env),
  (forall (i0 : fin m1) (i1 : fin m2),
     DE.eval_bexp (BL.env_val rho) (CD.leExp (DE.idx (DE.idx input i0) i1) CD.zero) =
     DE.bexp2bool (CD.leExp (DE.idx (DE.idx input i0) i1) CD.zero)) ->
  SEM.to_pcg_exp (COP.ReLU2d input) rho =
  LF.ReLU2d (SEM.to_pcg_exp input rho).
Proof.
  intros m1 m2 input rho Hb.
  unfold COP.ReLU2d, LF.ReLU2d.
  apply BL.to_pcg_mkvSeq_ext; intro i0.
  apply BL.to_pcg_mkvSeq_ext; intro i1.
  rewrite <- (Hb i0 i1).
  remember (DE.eval_bexp (BL.env_val rho) (CD.leExp (DE.idx (DE.idx input i0) i1) CD.zero))
    as bcond eqn:E.
  rewrite BL.to_pcg_exp_BLe in E.
  rewrite SEM.to_pcg_exp_zero in E.
  repeat rewrite SEM.to_pcg_exp_idx in E.
  unfold PCG.zero.
  destruct bcond; rewrite <- E.
  - reflexivity.
  - repeat rewrite SEM.to_pcg_exp_idx. reflexivity.
Qed.

Lemma interp_Linear2d : forall (batch m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num))) (rho : PCG.env),
  SEM.to_pcg_exp (@COP.Linear2d batch m outnum w b input) rho =
  @OP.Linear2d batch m outnum (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp b rho)
    (SEM.to_pcg_exp input rho).
Proof.
  intros batch m outnum w b input rho.
  unfold COP.Linear2d, OP.Linear2d.
  apply BL.to_pcg_mkvSeq_ext; intro bi.
  apply BL.to_pcg_mkvSeq_ext; intro out.
  rewrite OSE.to_pcg_exp_add, SEM.to_pcg_exp_idx.
  apply f_equal2; [ | reflexivity ].
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_mul.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Lemma interp_Softmax2d : forall (batch m : nat) (Hb : batch > 0)
  (input : DE.exp (ary '{batch} (ary '{m} num))) (rho : PCG.env),
  SEM.to_pcg_exp (@COP.Softmax2d batch m input) rho =
  @OR.Softmax2d batch m (SEM.to_pcg_exp input rho).
Proof.
  intros batch m Hb input rho.
  unfold COP.Softmax2d, OR.Softmax2d. cbv [CD.let_binding]. cbv beta.
  apply BL.to_pcg_mkvSeq_ext; intro b.
  apply BL.to_pcg_mkvSeq_ext; intro j.
  rewrite OSE.to_pcg_exp_div, OSE.to_pcg_exp_pExp.
  repeat rewrite SEM.to_pcg_exp_idx.
  apply f_equal2; [ reflexivity | ].
  rewrite SEM.to_pcg_exp_mkvSeq.
  rewrite (PCG.idx_mkvSeq _ _ _ Hb).
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_pExp.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* ReLU layer bridges between named buffers                                   *)
(* (4d/2d mirrors of [Bridge_LeNet5.bridge_ReLU3d_buf]/[bridge_ReLU1d_buf])   *)
(* -------------------------------------------------------------------------- *)

Lemma bridge_ReLU4d_buf : forall {b c m1 m2 : nat} (sin sout : string)
  (eta : PCG.env),
  (sin <> "0")%string -> (sin <> "1")%string ->
  (forall u v : string, (sout ++ "[" ++ u <> sin ++ "[" ++ v)%string) ->
  (forall (bb : fin b) (cc : fin c) (i0 : fin m1) (i1 : fin m2),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx
        (SEM.to_pcg_exp (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin) eta)
        bb) cc) i0) i1 <= R0)%R) ->
  SEM.eval
    (@CEO.ReLU4d_comm b c m1 m2
       (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin)
       (@CG.vwt (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sout)) eta =
  PCG.assign (@CG.vwt (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sout)
    (@OE.ReLU4d b c m1 m2
      (SEM.to_pcg_exp (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin) eta))
    eta.
Proof.
  intros b c m1 m2 sin sout eta Hs0 Hs1 Hnames Hle.
  (* Convert the [Rle] premise to the native boolean side condition. *)
  assert (Hb : forall (bb : fin b) (cc : fin c) (i0 : fin m1) (i1 : fin m2),
    DE.eval_bexp (BL.env_val eta)
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin) bb) cc) i0) i1) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin) bb) cc) i0) i1) CD.zero)).
  { intros bb cc i0 i1.
    rewrite (BL.to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin) bb) cc) i0) i1) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (DE.idx (DE.idx (DE.idx
          (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin) bb) cc) i0) i1)
          PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (BL.env_val PCG.env_empty) by reflexivity.
      apply BL.to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (BL.to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite !BL.PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle bb cc i0 i1).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  (* The buffer read does not clash with the output buffer. *)
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sin)
    (@CG.vwt (ary '{b} (ary '{c} (ary '{m1} (ary '{m2} num)))) sout)).
  { intros p Hp. destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply BL.exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEO.ReLU4d_equiv_sem _ Hindep Hb).
  cbv [CG.A]. rewrite SEM.eval_assign.
  f_equal. apply BEL.interp_ReLU4d. exact Hb.
Qed.

Lemma bridge_ReLU2d_buf : forall {m1 m2 : nat} (sin sout : string)
  (eta : PCG.env),
  (sin <> "0")%string -> (sin <> "1")%string ->
  (forall u v : string, (sout ++ "[" ++ u <> sin ++ "[" ++ v)%string) ->
  (forall (i0 : fin m1) (i1 : fin m2),
     (PCG.idx (PCG.idx
        (SEM.to_pcg_exp (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) eta)
        i0) i1 <= R0)%R) ->
  SEM.eval
    (@CEB.ReLU2d_comm m1 m2
       (@CG.vrd (ary '{m1} (ary '{m2} num)) sin)
       (@CG.vwt (ary '{m1} (ary '{m2} num)) sout)) eta =
  PCG.assign (@CG.vwt (ary '{m1} (ary '{m2} num)) sout)
    (@LF.ReLU2d m1 m2
      (SEM.to_pcg_exp (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) eta))
    eta.
Proof.
  intros m1 m2 sin sout eta Hs0 Hs1 Hnames Hle.
  assert (Hb : forall (i0 : fin m1) (i1 : fin m2),
    DE.eval_bexp (BL.env_val eta)
      (CD.leExp (DE.idx (DE.idx
        (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx
        (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1) CD.zero)).
  { intros i0 i1.
    rewrite (BL.to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx
        (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (DE.idx
          (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1)
          PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (BL.env_val PCG.env_empty) by reflexivity.
      apply BL.to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (BL.to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite !BL.PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle i0 i1).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{m1} (ary '{m2} num)) sin)
    (@CG.vwt (ary '{m1} (ary '{m2} num)) sout)).
  { intros p Hp. destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply BL.exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEB.ReLU2d_equiv_sem _ Hindep Hb).
  cbv [CG.A]. rewrite SEM.eval_assign.
  f_equal. apply interp_ReLU2d. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* Buffer types (batch 1, 3x224x224 input; sizes via [VGG16_DPIA]'s symbolic  *)
(* layer-size functions so that the route-A weight types match definitionally)*)
(* -------------------------------------------------------------------------- *)

Definition Tin : data := ary '{1} (ary '{3} (ary '{224} (ary '{224} num))).
Definition Tkw1 : data := ary '{64} (ary '{3} (ary '{3} (ary '{3} num))).
Definition Tkw2 : data := ary '{64} (ary '{64} (ary '{3} (ary '{3} num))).
Definition Tkw3 : data := ary '{128} (ary '{64} (ary '{3} (ary '{3} num))).
Definition Tkw4 : data := ary '{128} (ary '{128} (ary '{3} (ary '{3} num))).
Definition Tkw5 : data := ary '{256} (ary '{128} (ary '{3} (ary '{3} num))).
Definition Tkw6 : data := ary '{256} (ary '{256} (ary '{3} (ary '{3} num))).
Definition Tkw7 : data := ary '{512} (ary '{256} (ary '{3} (ary '{3} num))).
Definition Tkw8 : data := ary '{512} (ary '{512} (ary '{3} (ary '{3} num))).
Definition Tkb64 : data := ary '{64} num.
Definition Tkb128 : data := ary '{128} num.
Definition Tkb256 : data := ary '{256} num.
Definition Tkb512 : data := ary '{512} num.
Definition Tc1 : data := ary '{1} (ary '{64} (ary '{VD.s01 224} (ary '{VD.s01 224} num))).
Definition Tc2 : data := ary '{1} (ary '{64} (ary '{VD.s02 224} (ary '{VD.s02 224} num))).
Definition Tp1 : data := ary '{1} (ary '{64} (ary '{VD.s03 224} (ary '{VD.s03 224} num))).
Definition Tc3 : data := ary '{1} (ary '{128} (ary '{VD.s04 224} (ary '{VD.s04 224} num))).
Definition Tc4 : data := ary '{1} (ary '{128} (ary '{VD.s05 224} (ary '{VD.s05 224} num))).
Definition Tp2 : data := ary '{1} (ary '{128} (ary '{VD.s06 224} (ary '{VD.s06 224} num))).
Definition Tc5 : data := ary '{1} (ary '{256} (ary '{VD.s07 224} (ary '{VD.s07 224} num))).
Definition Tc6 : data := ary '{1} (ary '{256} (ary '{VD.s08 224} (ary '{VD.s08 224} num))).
Definition Tc7 : data := ary '{1} (ary '{256} (ary '{VD.s09 224} (ary '{VD.s09 224} num))).
Definition Tp3 : data := ary '{1} (ary '{256} (ary '{VD.s10 224} (ary '{VD.s10 224} num))).
Definition Tc8 : data := ary '{1} (ary '{512} (ary '{VD.s11 224} (ary '{VD.s11 224} num))).
Definition Tc9 : data := ary '{1} (ary '{512} (ary '{VD.s12 224} (ary '{VD.s12 224} num))).
Definition Tc10 : data := ary '{1} (ary '{512} (ary '{VD.s13 224} (ary '{VD.s13 224} num))).
Definition Tp4 : data := ary '{1} (ary '{512} (ary '{VD.s14 224} (ary '{VD.s14 224} num))).
Definition Tc11 : data := ary '{1} (ary '{512} (ary '{VD.s15 224} (ary '{VD.s15 224} num))).
Definition Tc12 : data := ary '{1} (ary '{512} (ary '{VD.s16 224} (ary '{VD.s16 224} num))).
Definition Tc13 : data := ary '{1} (ary '{512} (ary '{VD.s17 224} (ary '{VD.s17 224} num))).
Definition Tp5 : data := ary '{1} (ary '{512} (ary '{VD.s18 224} (ary '{VD.s18 224} num))).
Definition Tflat : data := ary '{1} (ary '{512 * VD.s18 224 * VD.s18 224} num).
Definition Tfc1w : data := ary '{4096} (ary '{512 * VD.s18 224 * VD.s18 224} num).
Definition Tfc2w : data := ary '{4096} (ary '{4096} num).
Definition Tfc3w : data := ary '{1000} (ary '{4096} num).
Definition Tfcb4096 : data := ary '{4096} num.
Definition Tfcb1000 : data := ary '{1000} num.
Definition Tfc : data := ary '{1} (ary '{4096} num).
Definition Tout : data := ary '{1} (ary '{1000} num).

(* -------------------------------------------------------------------------- *)
(* The generic whole-network AST (loopacc-based layer commands; buffer names  *)
(* of [CNN_Examples_VGG16] plus a final softmax stage)                        *)
(* -------------------------------------------------------------------------- *)

Definition vgg16_gen_comm : CG.comm :=
  CG.seq ( @B2.Conv4d_ast_comm 1 224 224 3 3 3 64 1 1
             (@CG.vrd Tkb64 "conv1_1_b") (@CG.vrd Tkw1 "conv1_1_w")
             (@CG.vrd Tin "input") (@CG.vwt Tc1 "conv1_1_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 64 (VD.s01 224) (VD.s01 224)
             (@CG.vrd Tc1 "conv1_1_out") (@CG.vwt Tc1 "relu1_1_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s01 224) (VD.s01 224) 3 3 64 64 1 1
             (@CG.vrd Tkb64 "conv1_2_b") (@CG.vrd Tkw2 "conv1_2_w")
             (@CG.vrd Tc1 "relu1_1_out") (@CG.vwt Tc2 "conv1_2_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 64 (VD.s02 224) (VD.s02 224)
             (@CG.vrd Tc2 "conv1_2_out") (@CG.vwt Tc2 "relu1_2_out"),
  CG.seq ( @CEO.Maxpool4d_comm 1 64 (VD.s02 224) (VD.s02 224) 2
             (@CG.vrd Tc2 "relu1_2_out") (@CG.vwt Tp1 "pool1_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s03 224) (VD.s03 224) 3 3 64 128 1 1
             (@CG.vrd Tkb128 "conv2_1_b") (@CG.vrd Tkw3 "conv2_1_w")
             (@CG.vrd Tp1 "pool1_out") (@CG.vwt Tc3 "conv2_1_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 128 (VD.s04 224) (VD.s04 224)
             (@CG.vrd Tc3 "conv2_1_out") (@CG.vwt Tc3 "relu2_1_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s04 224) (VD.s04 224) 3 3 128 128 1 1
             (@CG.vrd Tkb128 "conv2_2_b") (@CG.vrd Tkw4 "conv2_2_w")
             (@CG.vrd Tc3 "relu2_1_out") (@CG.vwt Tc4 "conv2_2_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 128 (VD.s05 224) (VD.s05 224)
             (@CG.vrd Tc4 "conv2_2_out") (@CG.vwt Tc4 "relu2_2_out"),
  CG.seq ( @CEO.Maxpool4d_comm 1 128 (VD.s05 224) (VD.s05 224) 2
             (@CG.vrd Tc4 "relu2_2_out") (@CG.vwt Tp2 "pool2_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s06 224) (VD.s06 224) 3 3 128 256 1 1
             (@CG.vrd Tkb256 "conv3_1_b") (@CG.vrd Tkw5 "conv3_1_w")
             (@CG.vrd Tp2 "pool2_out") (@CG.vwt Tc5 "conv3_1_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 256 (VD.s07 224) (VD.s07 224)
             (@CG.vrd Tc5 "conv3_1_out") (@CG.vwt Tc5 "relu3_1_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s07 224) (VD.s07 224) 3 3 256 256 1 1
             (@CG.vrd Tkb256 "conv3_2_b") (@CG.vrd Tkw6 "conv3_2_w")
             (@CG.vrd Tc5 "relu3_1_out") (@CG.vwt Tc6 "conv3_2_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 256 (VD.s08 224) (VD.s08 224)
             (@CG.vrd Tc6 "conv3_2_out") (@CG.vwt Tc6 "relu3_2_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s08 224) (VD.s08 224) 3 3 256 256 1 1
             (@CG.vrd Tkb256 "conv3_3_b") (@CG.vrd Tkw6 "conv3_3_w")
             (@CG.vrd Tc6 "relu3_2_out") (@CG.vwt Tc7 "conv3_3_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 256 (VD.s09 224) (VD.s09 224)
             (@CG.vrd Tc7 "conv3_3_out") (@CG.vwt Tc7 "relu3_3_out"),
  CG.seq ( @CEO.Maxpool4d_comm 1 256 (VD.s09 224) (VD.s09 224) 2
             (@CG.vrd Tc7 "relu3_3_out") (@CG.vwt Tp3 "pool3_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s10 224) (VD.s10 224) 3 3 256 512 1 1
             (@CG.vrd Tkb512 "conv4_1_b") (@CG.vrd Tkw7 "conv4_1_w")
             (@CG.vrd Tp3 "pool3_out") (@CG.vwt Tc8 "conv4_1_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 512 (VD.s11 224) (VD.s11 224)
             (@CG.vrd Tc8 "conv4_1_out") (@CG.vwt Tc8 "relu4_1_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s11 224) (VD.s11 224) 3 3 512 512 1 1
             (@CG.vrd Tkb512 "conv4_2_b") (@CG.vrd Tkw8 "conv4_2_w")
             (@CG.vrd Tc8 "relu4_1_out") (@CG.vwt Tc9 "conv4_2_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 512 (VD.s12 224) (VD.s12 224)
             (@CG.vrd Tc9 "conv4_2_out") (@CG.vwt Tc9 "relu4_2_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s12 224) (VD.s12 224) 3 3 512 512 1 1
             (@CG.vrd Tkb512 "conv4_3_b") (@CG.vrd Tkw8 "conv4_3_w")
             (@CG.vrd Tc9 "relu4_2_out") (@CG.vwt Tc10 "conv4_3_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 512 (VD.s13 224) (VD.s13 224)
             (@CG.vrd Tc10 "conv4_3_out") (@CG.vwt Tc10 "relu4_3_out"),
  CG.seq ( @CEO.Maxpool4d_comm 1 512 (VD.s13 224) (VD.s13 224) 2
             (@CG.vrd Tc10 "relu4_3_out") (@CG.vwt Tp4 "pool4_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s14 224) (VD.s14 224) 3 3 512 512 1 1
             (@CG.vrd Tkb512 "conv5_1_b") (@CG.vrd Tkw8 "conv5_1_w")
             (@CG.vrd Tp4 "pool4_out") (@CG.vwt Tc11 "conv5_1_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 512 (VD.s15 224) (VD.s15 224)
             (@CG.vrd Tc11 "conv5_1_out") (@CG.vwt Tc11 "relu5_1_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s15 224) (VD.s15 224) 3 3 512 512 1 1
             (@CG.vrd Tkb512 "conv5_2_b") (@CG.vrd Tkw8 "conv5_2_w")
             (@CG.vrd Tc11 "relu5_1_out") (@CG.vwt Tc12 "conv5_2_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 512 (VD.s16 224) (VD.s16 224)
             (@CG.vrd Tc12 "conv5_2_out") (@CG.vwt Tc12 "relu5_2_out"),
  CG.seq ( @B2.Conv4d_ast_comm 1 (VD.s16 224) (VD.s16 224) 3 3 512 512 1 1
             (@CG.vrd Tkb512 "conv5_3_b") (@CG.vrd Tkw8 "conv5_3_w")
             (@CG.vrd Tc12 "relu5_2_out") (@CG.vwt Tc13 "conv5_3_out"),
  CG.seq ( @CEO.ReLU4d_comm 1 512 (VD.s17 224) (VD.s17 224)
             (@CG.vrd Tc13 "conv5_3_out") (@CG.vwt Tc13 "relu5_3_out"),
  CG.seq ( @CEO.Maxpool4d_comm 1 512 (VD.s17 224) (VD.s17 224) 2
             (@CG.vrd Tc13 "relu5_3_out") (@CG.vwt Tp5 "pool5_out"),
  CG.seq ( @CEB.Flatten4d_comm 1 512 (VD.s18 224) (VD.s18 224)
             (@CG.vrd Tp5 "pool5_out") (@CG.vwt Tflat "flatten_out"),
  CG.seq ( @CEO.Linear2d_comm 1 (512 * VD.s18 224 * VD.s18 224) 4096
             (@CG.vrd Tfc1w "fc1_w") (@CG.vrd Tfcb4096 "fc1_b")
             (@CG.vrd Tflat "flatten_out") (@CG.vwt Tfc "fc1_out"),
  CG.seq ( @CEB.ReLU2d_comm 1 4096
             (@CG.vrd Tfc "fc1_out") (@CG.vwt Tfc "fc1_relu_out"),
  CG.seq ( @CEO.Linear2d_comm 1 4096 4096
             (@CG.vrd Tfc2w "fc2_w") (@CG.vrd Tfcb4096 "fc2_b")
             (@CG.vrd Tfc "fc1_relu_out") (@CG.vwt Tfc "fc2_out"),
  CG.seq ( @CEB.ReLU2d_comm 1 4096
             (@CG.vrd Tfc "fc2_out") (@CG.vwt Tfc "fc2_relu_out"),
  CG.seq ( @CEO.Linear2d_comm 1 4096 1000
             (@CG.vrd Tfc3w "fc3_w") (@CG.vrd Tfcb1000 "fc3_b")
             (@CG.vrd Tfc "fc2_relu_out") (@CG.vwt Tout "fc3_out"),
             @CEO.Softmax2d_comm 1 1000
             (@CG.vrd Tout "fc3_out") (@CG.vwt Tout "output")
  ))))))))))))))))))))))))))))))))))))).

(* -------------------------------------------------------------------------- *)
(* Functional layer values (route A), as functions of the initial env         *)
(* -------------------------------------------------------------------------- *)

Definition rd (d : data) (s : string) (rho : PCG.env) : PCG.exp d :=
  SEM.to_pcg_exp (@CG.vrd d s) rho.

Definition Gc1 (rho : PCG.env) : PCG.exp Tc1 :=
  OC.Conv4d 1 1 (rd Tkb64 "conv1_1_b" rho) (rd Tkw1 "conv1_1_w" rho) (rd Tin "input" rho).
Definition Gc2 (rho : PCG.env) : PCG.exp Tc2 :=
  OC.Conv4d 1 1 (rd Tkb64 "conv1_2_b" rho) (rd Tkw2 "conv1_2_w" rho) (OE.ReLU4d (Gc1 rho)).
Definition Gc3 (rho : PCG.env) : PCG.exp Tc3 :=
  OC.Conv4d 1 1 (rd Tkb128 "conv2_1_b" rho) (rd Tkw3 "conv2_1_w" rho)
    (OP.Maxpool4d 2 (OE.ReLU4d (Gc2 rho))).
Definition Gc4 (rho : PCG.env) : PCG.exp Tc4 :=
  OC.Conv4d 1 1 (rd Tkb128 "conv2_2_b" rho) (rd Tkw4 "conv2_2_w" rho) (OE.ReLU4d (Gc3 rho)).
Definition Gc5 (rho : PCG.env) : PCG.exp Tc5 :=
  OC.Conv4d 1 1 (rd Tkb256 "conv3_1_b" rho) (rd Tkw5 "conv3_1_w" rho)
    (OP.Maxpool4d 2 (OE.ReLU4d (Gc4 rho))).
Definition Gc6 (rho : PCG.env) : PCG.exp Tc6 :=
  OC.Conv4d 1 1 (rd Tkb256 "conv3_2_b" rho) (rd Tkw6 "conv3_2_w" rho) (OE.ReLU4d (Gc5 rho)).
Definition Gc7 (rho : PCG.env) : PCG.exp Tc7 :=
  OC.Conv4d 1 1 (rd Tkb256 "conv3_3_b" rho) (rd Tkw6 "conv3_3_w" rho) (OE.ReLU4d (Gc6 rho)).
Definition Gc8 (rho : PCG.env) : PCG.exp Tc8 :=
  OC.Conv4d 1 1 (rd Tkb512 "conv4_1_b" rho) (rd Tkw7 "conv4_1_w" rho)
    (OP.Maxpool4d 2 (OE.ReLU4d (Gc7 rho))).
Definition Gc9 (rho : PCG.env) : PCG.exp Tc9 :=
  OC.Conv4d 1 1 (rd Tkb512 "conv4_2_b" rho) (rd Tkw8 "conv4_2_w" rho) (OE.ReLU4d (Gc8 rho)).
Definition Gc10 (rho : PCG.env) : PCG.exp Tc10 :=
  OC.Conv4d 1 1 (rd Tkb512 "conv4_3_b" rho) (rd Tkw8 "conv4_3_w" rho) (OE.ReLU4d (Gc9 rho)).
Definition Gc11 (rho : PCG.env) : PCG.exp Tc11 :=
  OC.Conv4d 1 1 (rd Tkb512 "conv5_1_b" rho) (rd Tkw8 "conv5_1_w" rho)
    (OP.Maxpool4d 2 (OE.ReLU4d (Gc10 rho))).
Definition Gc12 (rho : PCG.env) : PCG.exp Tc12 :=
  OC.Conv4d 1 1 (rd Tkb512 "conv5_2_b" rho) (rd Tkw8 "conv5_2_w" rho) (OE.ReLU4d (Gc11 rho)).
Definition Gc13 (rho : PCG.env) : PCG.exp Tc13 :=
  OC.Conv4d 1 1 (rd Tkb512 "conv5_3_b" rho) (rd Tkw8 "conv5_3_w" rho) (OE.ReLU4d (Gc12 rho)).
Definition Gf1 (rho : PCG.env) : PCG.exp Tfc :=
  OP.Linear2d (rd Tfc1w "fc1_w" rho) (rd Tfcb4096 "fc1_b" rho)
    (AD.Flatten4d (OP.Maxpool4d 2 (OE.ReLU4d (Gc13 rho)))).
Definition Gf2 (rho : PCG.env) : PCG.exp Tfc :=
  OP.Linear2d (rd Tfc2w "fc2_w" rho) (rd Tfcb4096 "fc2_b" rho) (LF.ReLU2d (Gf1 rho)).
Definition Gout (rho : PCG.env) : PCG.exp Tout :=
  OR.Softmax2d
    (OP.Linear2d (rd Tfc3w "fc3_w" rho) (rd Tfcb1000 "fc3_b" rho) (LF.ReLU2d (Gf2 rho))).

(* -------------------------------------------------------------------------- *)
(* Wrapper bodies (A1): each functional layer value keeps its folded name;    *)
(* the bodies below are the ONLY sanctioned unfoldings.  [Gout] is the final  *)
(* route-B value.                                                             *)
(* -------------------------------------------------------------------------- *)
Lemma Gc1_body : forall rho, Gc1 rho = OC.Conv4d 1 1 (rd Tkb64 "conv1_1_b" rho) (rd Tkw1 "conv1_1_w" rho) (rd Tin "input" rho).
Proof. intros. reflexivity. Qed.
Lemma Gc2_body : forall rho, Gc2 rho = OC.Conv4d 1 1 (rd Tkb64 "conv1_2_b" rho) (rd Tkw2 "conv1_2_w" rho) (OE.ReLU4d (Gc1 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc3_body : forall rho, Gc3 rho = OC.Conv4d 1 1 (rd Tkb128 "conv2_1_b" rho) (rd Tkw3 "conv2_1_w" rho) (OP.Maxpool4d 2 (OE.ReLU4d (Gc2 rho))).
Proof. intros. reflexivity. Qed.
Lemma Gc4_body : forall rho, Gc4 rho = OC.Conv4d 1 1 (rd Tkb128 "conv2_2_b" rho) (rd Tkw4 "conv2_2_w" rho) (OE.ReLU4d (Gc3 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc5_body : forall rho, Gc5 rho = OC.Conv4d 1 1 (rd Tkb256 "conv3_1_b" rho) (rd Tkw5 "conv3_1_w" rho) (OP.Maxpool4d 2 (OE.ReLU4d (Gc4 rho))).
Proof. intros. reflexivity. Qed.
Lemma Gc6_body : forall rho, Gc6 rho = OC.Conv4d 1 1 (rd Tkb256 "conv3_2_b" rho) (rd Tkw6 "conv3_2_w" rho) (OE.ReLU4d (Gc5 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc7_body : forall rho, Gc7 rho = OC.Conv4d 1 1 (rd Tkb256 "conv3_3_b" rho) (rd Tkw6 "conv3_3_w" rho) (OE.ReLU4d (Gc6 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc8_body : forall rho, Gc8 rho = OC.Conv4d 1 1 (rd Tkb512 "conv4_1_b" rho) (rd Tkw7 "conv4_1_w" rho) (OP.Maxpool4d 2 (OE.ReLU4d (Gc7 rho))).
Proof. intros. reflexivity. Qed.
Lemma Gc9_body : forall rho, Gc9 rho = OC.Conv4d 1 1 (rd Tkb512 "conv4_2_b" rho) (rd Tkw8 "conv4_2_w" rho) (OE.ReLU4d (Gc8 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc10_body : forall rho, Gc10 rho = OC.Conv4d 1 1 (rd Tkb512 "conv4_3_b" rho) (rd Tkw8 "conv4_3_w" rho) (OE.ReLU4d (Gc9 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc11_body : forall rho, Gc11 rho = OC.Conv4d 1 1 (rd Tkb512 "conv5_1_b" rho) (rd Tkw8 "conv5_1_w" rho) (OP.Maxpool4d 2 (OE.ReLU4d (Gc10 rho))).
Proof. intros. reflexivity. Qed.
Lemma Gc12_body : forall rho, Gc12 rho = OC.Conv4d 1 1 (rd Tkb512 "conv5_2_b" rho) (rd Tkw8 "conv5_2_w" rho) (OE.ReLU4d (Gc11 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gc13_body : forall rho, Gc13 rho = OC.Conv4d 1 1 (rd Tkb512 "conv5_3_b" rho) (rd Tkw8 "conv5_3_w" rho) (OE.ReLU4d (Gc12 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gf1_body : forall rho, Gf1 rho = OP.Linear2d (rd Tfc1w "fc1_w" rho) (rd Tfcb4096 "fc1_b" rho) (AD.Flatten4d (OP.Maxpool4d 2 (OE.ReLU4d (Gc13 rho)))).
Proof. intros. reflexivity. Qed.
Lemma Gf2_body : forall rho, Gf2 rho = OP.Linear2d (rd Tfc2w "fc2_w" rho) (rd Tfcb4096 "fc2_b" rho) (LF.ReLU2d (Gf1 rho)).
Proof. intros. reflexivity. Qed.
Lemma Gout_body : forall rho, Gout rho = OR.Softmax2d (OP.Linear2d (rd Tfc3w "fc3_w" rho) (rd Tfcb1000 "fc3_b" rho) (LF.ReLU2d (Gf2 rho))).
Proof. intros. reflexivity. Qed.

(* Never unfold the wrappers in reduction/rewrite keying: every use goes *)
(* through the [*]_body lemmas above or the Hr* premises.                *)
Opaque Gc1 Gc2 Gc3 Gc4 Gc5 Gc6 Gc7 Gc8 Gc9 Gc10 Gc11 Gc12 Gc13 Gf1 Gf2 Gout.

(* One fold-or-peel step of the route-B/route-A value alignment: expose the *)
(* body of the single folded wrapper on the left, then peel one operator    *)
(* layer by congruence.  Terms never grow beyond one unfolded layer.        *)
Ltac finstep := first
  [ rewrite Gout_body | rewrite Gf2_body | rewrite Gf1_body
  | rewrite Gc13_body | rewrite Gc12_body | rewrite Gc11_body | rewrite Gc10_body
  | rewrite Gc9_body | rewrite Gc8_body | rewrite Gc7_body | rewrite Gc6_body
  | rewrite Gc5_body | rewrite Gc4_body | rewrite Gc3_body | rewrite Gc2_body
  | rewrite Gc1_body | f_equal | exact eq_refl ].

(* B1: the whole-network value equality, proved by a fold/f_equal chain     *)
(* instead of a single kernel conversion over the fully nested term.        *)
Lemma vgg16_out_eq : forall (rho : PCG.env),
  Gout rho =
  @VD.VGG16 1 3 224 224
    (rd Tin "input" rho)
    (rd Tkw1 "conv1_1_w" rho) (rd Tkb64 "conv1_1_b" rho)
    (rd Tkw2 "conv1_2_w" rho) (rd Tkb64 "conv1_2_b" rho)
    (rd Tkw3 "conv2_1_w" rho) (rd Tkb128 "conv2_1_b" rho)
    (rd Tkw4 "conv2_2_w" rho) (rd Tkb128 "conv2_2_b" rho)
    (rd Tkw5 "conv3_1_w" rho) (rd Tkb256 "conv3_1_b" rho)
    (rd Tkw6 "conv3_2_w" rho) (rd Tkb256 "conv3_2_b" rho)
    (rd Tkw6 "conv3_3_w" rho) (rd Tkb256 "conv3_3_b" rho)
    (rd Tkw7 "conv4_1_w" rho) (rd Tkb512 "conv4_1_b" rho)
    (rd Tkw8 "conv4_2_w" rho) (rd Tkb512 "conv4_2_b" rho)
    (rd Tkw8 "conv4_3_w" rho) (rd Tkb512 "conv4_3_b" rho)
    (rd Tkw8 "conv5_1_w" rho) (rd Tkb512 "conv5_1_b" rho)
    (rd Tkw8 "conv5_2_w" rho) (rd Tkb512 "conv5_2_b" rho)
    (rd Tkw8 "conv5_3_w" rho) (rd Tkb512 "conv5_3_b" rho)
    (rd Tfc1w "fc1_w" rho) (rd Tfcb4096 "fc1_b" rho)
    (rd Tfc2w "fc2_w" rho) (rd Tfcb4096 "fc2_b" rho)
    (rd Tfc3w "fc3_w" rho) (rd Tfcb1000 "fc3_b" rho).
Proof.
  intros rho.
  unfold VD.VGG16. cbv zeta beta.
  repeat finstep.
  all: try exact eq_refl.
Qed.


(* Freshness of the initial environment: the loopacc temporary and the
   route-A intermediate accumulators are all undefined. *)
Definition net_fresh (rho : PCG.env) : Prop :=
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho /\
  PCG.StructUndefined (@VD.v1_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v2_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v3_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v4_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v5_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v6_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v7_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v8_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v9_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v10_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v11_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v12_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v13_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v14_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v15_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v16_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v17_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v18_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v19_acc 1 224 224) rho /\
  PCG.StructUndefined (@VD.v20_acc 1) rho /\
  PCG.StructUndefined (@VD.v21_acc 1) rho.

(* -------------------------------------------------------------------------- *)
(* Generic per-layer step lemmas                                              *)
(* -------------------------------------------------------------------------- *)

Lemma HB_conv_gen : forall (batch inch outch m : nat)
  (Hb : batch > 0) (Hic : inch > 0) (Hoc : outch > 0) (Hm : 3 <= m)
  (sb sw si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sw ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sb ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sw ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sb ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval
    (@B2.Conv4d_ast_comm batch m m 3 3 inch outch 1 1
       (@CG.vrd (ary '{outch} num) sb)
       (@CG.vrd (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))) sw)
       (@CG.vrd (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))) si)
       (@CG.vwt (ary '{batch} (ary '{outch}
          (ary '{(m - 3 + 2 * 1) / 1 + 1} (ary '{(m - 3 + 2 * 1) / 1 + 1} num)))) so)) eta =
  PCG.assign
    (@CG.vwt (ary '{batch} (ary '{outch}
       (ary '{(m - 3 + 2 * 1) / 1 + 1} (ary '{(m - 3 + 2 * 1) / 1 + 1} num)))) so)
    (@OC.Conv4d batch m m 3 3 inch outch 1 1
       (SEM.to_pcg_exp (@CG.vrd (ary '{outch} num) sb) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))) sw) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))) si) eta))
    eta.
Proof.
  intros batch inch outch m Hb Hic Hoc Hm sb sw si so eta
    Hni Hnw Hnb Hno Hdoi Hdow Hdob Htmp.
  assert (Hi : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))) si) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hni).
  assert (Hw : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))) sw) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hnw).
  assert (Hbias : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outch} num) sb) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hnb).
  assert (Hio : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))) si)
    (@CG.vwt (ary '{batch} (ary '{outch}
       (ary '{(m - 3 + 2 * 1) / 1 + 1} (ary '{(m - 3 + 2 * 1) / 1 + 1} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdoi).
  assert (Hwo : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))) sw)
    (@CG.vwt (ary '{batch} (ary '{outch}
       (ary '{(m - 3 + 2 * 1) / 1 + 1} (ary '{(m - 3 + 2 * 1) / 1 + 1} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdow).
  assert (Hbo : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outch} num) sb)
    (@CG.vwt (ary '{batch} (ary '{outch}
       (ary '{(m - 3 + 2 * 1) / 1 + 1} (ary '{(m - 3 + 2 * 1) / 1 + 1} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdob).
  assert (Hdisj : B2.tmp_disjoint_from_output_conv4d batch m m 3 3 outch 1 1
    (@CG.vwt (ary '{batch} (ary '{outch}
       (ary '{(m - 3 + 2 * 1) / 1 + 1} (ary '{(m - 3 + 2 * 1) / 1 + 1} num)))) so))
    by (exact (tmp_neq_vwt4 _ _ _ _ so Hno)).
  rewrite <- (Conv4d_sem_single batch m m 3 3 inch outch 1 1 _ _ _
    (Nat.lt_0_succ 0) Hb Hic Hoc (Nat.lt_0_succ 2) (Nat.lt_0_succ 2)
    Hi Hw Hbias _ Hio Hwo Hbo eta Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite <- (B2.interp_Conv4d batch m m 3 3 inch outch 1 1 _ _ _
    (Nat.lt_0_succ 0) Hb Hic (Nat.lt_0_succ 2) (Nat.lt_0_succ 2) Hm Hm eta).
  reflexivity.
Qed.

Lemma HB_pool_gen : forall (batch ch m : nat)
  (Hb : batch > 0) (Hc : ch > 0)
  (si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval
    (@CEO.Maxpool4d_comm batch ch m m 2
       (@CG.vrd (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))) si)
       (@CG.vwt (ary '{batch} (ary '{ch} (ary '{m/2} (ary '{m/2} num)))) so)) eta =
  PCG.assign
    (@CG.vwt (ary '{batch} (ary '{ch} (ary '{m/2} (ary '{m/2} num)))) so)
    (@OP.Maxpool4d batch ch m m 2
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))) si) eta))
    eta.
Proof.
  intros batch ch m Hb Hc si so eta Hni Hno Hdoi Htmp.
  assert (Hi : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))) si) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hni).
  assert (Hio : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))) si)
    (@CG.vwt (ary '{batch} (ary '{ch} (ary '{m/2} (ary '{m/2} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdoi).
  assert (Hdisj : OSE.tmp_disjoint_from_output_maxp4d batch ch m m 2
    (@CG.vwt (ary '{batch} (ary '{ch} (ary '{m/2} (ary '{m/2} num)))) so))
    by (exact (tmp_neq_vwt4 _ _ _ _ so Hno)).
  rewrite <- (Maxpool4d_sem_single batch ch m m 2 Hb Hc (Nat.lt_0_succ 1)
    _ _ eta Hi Hio Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Maxpool4d batch ch m m 2 _ eta).
  reflexivity.
Qed.

Lemma HB_flat_gen : forall (batch channel m1 m2 : nat)
  (Hb : batch > 0) (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (si so : string) (eta : PCG.env),
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval
    (@CEB.Flatten4d_comm batch channel m1 m2
       (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) si)
       (@CG.vwt (ary '{batch} (ary '{channel * m1 * m2} num)) so)) eta =
  PCG.assign
    (@CG.vwt (ary '{batch} (ary '{channel * m1 * m2} num)) so)
    (@AD.Flatten4d batch channel m1 m2
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) si) eta))
    eta.
Proof.
  intros batch channel m1 m2 Hb Hc Hm1 Hm2 si so eta Hno Hdoi Htmp.
  assert (Hio : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) si)
    (@CG.vwt (ary '{batch} (ary '{channel * m1 * m2} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdoi).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d batch (channel * m1 * m2)
    (@CG.vwt (ary '{batch} (ary '{channel * m1 * m2} num)) so))
    by (exact (tmp_neq_vwt2 _ _ so Hno)).
  rewrite <- (Flatten4d_sem_single batch channel m1 m2 Hb Hc Hm1 Hm2 _ _ eta Hio Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (B2.interp_Flatten4d batch channel m1 m2 Hb Hc Hm1 Hm2 _ eta).
  reflexivity.
Qed.

Lemma HB_linear_gen : forall (batch m outnum : nat)
  (sb sw si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sw ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sb ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sw ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sb ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval
    (@CEO.Linear2d_comm batch m outnum
       (@CG.vrd (ary '{outnum} (ary '{m} num)) sw)
       (@CG.vrd (ary '{outnum} num) sb)
       (@CG.vrd (ary '{batch} (ary '{m} num)) si)
       (@CG.vwt (ary '{batch} (ary '{outnum} num)) so)) eta =
  PCG.assign
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so)
    (@OP.Linear2d batch m outnum
       (SEM.to_pcg_exp (@CG.vrd (ary '{outnum} (ary '{m} num)) sw) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{outnum} num) sb) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{m} num)) si) eta))
    eta.
Proof.
  intros batch m outnum sb sw si so eta Hni Hnw Hnb Hno Hdoi Hdow Hdob Htmp.
  assert (Hi : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{m} num)) si) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hni).
  assert (Hw : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outnum} (ary '{m} num)) sw) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hnw).
  assert (Hbias : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outnum} num) sb) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hnb).
  assert (Hio : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdoi).
  assert (Hwo : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outnum} (ary '{m} num)) sw)
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdow).
  assert (Hbo : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{outnum} num) sb)
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdob).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d batch outnum
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (exact (tmp_neq_vwt2 _ _ so Hno)).
  rewrite <- (Linear2d_sem_single batch m outnum _ _ _ _ eta
    Hi Hw Hbias Hio Hwo Hbo Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (interp_Linear2d batch m outnum _ _ _ eta).
  reflexivity.
Qed.

Lemma HB_softmax_gen : forall (batch m : nat)
  (Hb : batch > 0) (Hm : m > 0)
  (si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval
    (@CEO.Softmax2d_comm batch m
       (@CG.vrd (ary '{batch} (ary '{m} num)) si)
       (@CG.vwt (ary '{batch} (ary '{m} num)) so)) eta =
  PCG.assign
    (@CG.vwt (ary '{batch} (ary '{m} num)) so)
    (@OR.Softmax2d batch m
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{m} num)) si) eta))
    eta.
Proof.
  intros batch m Hb Hm si so eta Hni Hno Hdoi Htmp.
  assert (Hi : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{m} num)) si) OSE.tmp_scalar_acc)
    by (apply BL.vrd_ary_indep_tmp; exact Hni).
  assert (Hio : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    (@CG.vwt (ary '{batch} (ary '{m} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hdoi).
  assert (Hdisj : forall (p : DE.path) (b : fin batch) (j : fin m),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p
        ((@CG.vwt (ary '{batch} (ary '{m} num)) so) |{ b} |{ j}))
    by (exact (tmp_neq_vwt2 _ _ so Hno)).
  rewrite <- (Softmax2d_sem_single batch m Hb Hm _ _ eta Hi Hio Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (interp_Softmax2d batch m Hb _ eta).
  reflexivity.
Qed.
(* -------------------------------------------------------------------------- *)
(* The whole-network bridge                                                   *)
(* -------------------------------------------------------------------------- *)

(* Forward-simulation tactics.  To keep every simulation step O(1) in the
   number of layers already processed, the current environment is folded by
   [remember] after each layer ([fold_and_bump]), and the reads of the 33
   read-only buffers (input/weights/biases) are maintained as rewrite facts
   about the folded variable; the read of the buffer written by the previous
   layer is discharged by a single [vrd_after_own_vwt]-based fact. *)

Ltac rw_fact s :=
  match goal with
  | [ H : SEM.to_pcg_exp (@CG.vrd ?d s) _ = _ |- _ ] => rewrite H
  end.

Ltac clear_fact s :=
  match goal with
  | [ H : SEM.to_pcg_exp (@CG.vrd ?d s) _ = _ |- _ ] => clear H
  end.

Ltac su_fact :=
  match goal with
  | [ H : PCG.StructUndefined (PCG.acc' OSE.tmp_path) _ |- _ ] => exact H
  end.

(* Fold the freshly extended environment [assign (vwt so) v eta] into a new
   variable, bump every buffer-read fact from [eta] to the new variable, bump
   the [StructUndefined tmp] fact, and record the own-read fact for [so] in
   the folded form [XV] (a wrapper constant [Gc*]/[Gf*] or a one-layer
   expression over wrappers), so the goal never carries the nested layer
   chain: every simulation step is O(1) in the number of layers processed.
   The conversion [v = XV] discharged by the final [apply] is one wrapper
   delta plus a syntactic match (see probe evidence: sub-second). *)
Ltac fold_and_bump so XV :=
  match goal with
  | |- context [ PCG.assign (OSE.as_PCG_acc (@CG.vwt ?td so)) ?v ?eta ] =>
    let x := fresh "NS" in
    let e := fresh "HE" in
    (* NOTE: the remembered term must be written with the [OSE.as_PCG_acc]
       coercion exactly as it appears in the goal; the [@PCG.assign td
       (@CG.vwt td so) v eta] form elaborates to a syntactically different
       term, in which case [remember] silently abstracts NOTHING and the whole
       forward simulation degenerates. *)
    remember (PCG.assign (OSE.as_PCG_acc (@CG.vwt td so)) v eta) as x eqn:e;
    (* NOTE: the discharge of the bumped fact MUST be the syntactic [exact H],
       never [assumption]: rejecting a wrong candidate here costs a conversion
       between two different large [to_pcg_exp (vrd ...) _] types (e.g.
       1000x4096 vs 4096x4096), which unfolds [to_pcg_exp] over the array
       types and explodes (the >5h/19.7GB event). *)
    repeat match goal with
    | [ H : SEM.to_pcg_exp (@CG.vrd ?d ?s) eta = ?g |- _ ] =>
      assert (SEM.to_pcg_exp (@CG.vrd d s) x = g) by
        (rewrite e; rewrite BL.vrd_after_other_vwt_ary_gen by str_neq_tac;
         exact H);
      clear H
    end;
    match goal with
    | [ H : PCG.StructUndefined (PCG.acc' OSE.tmp_path) eta |- _ ] =>
      assert (PCG.StructUndefined (PCG.acc' OSE.tmp_path) x) by
        (rewrite e; apply BL.SU_tmp_after_assign_vwt;
         [ intros u Heq2; discriminate | exact H ]);
      clear H
    end;
    assert (SEM.to_pcg_exp (@CG.vrd td so) x = XV) by
      (rewrite e; apply SEM.vrd_after_own_vwt; discriminate)
  end.

Theorem Bridge_VGG16 : forall (rho : PCG.env) (p : DE.path),
  @PCG.in_acc Tout p (@CG.vwt Tout "output") ->
  net_fresh rho ->
  (forall (bb : fin 1) (cc : fin 64) (i0 : fin (VD.s01 224)) (i1 : fin (VD.s01 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc1 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 64) (i0 : fin (VD.s02 224)) (i1 : fin (VD.s02 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc2 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 128) (i0 : fin (VD.s04 224)) (i1 : fin (VD.s04 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc3 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 128) (i0 : fin (VD.s05 224)) (i1 : fin (VD.s05 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc4 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 256) (i0 : fin (VD.s07 224)) (i1 : fin (VD.s07 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc5 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 256) (i0 : fin (VD.s08 224)) (i1 : fin (VD.s08 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc6 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 256) (i0 : fin (VD.s09 224)) (i1 : fin (VD.s09 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc7 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 512) (i0 : fin (VD.s11 224)) (i1 : fin (VD.s11 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc8 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 512) (i0 : fin (VD.s12 224)) (i1 : fin (VD.s12 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc9 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 512) (i0 : fin (VD.s13 224)) (i1 : fin (VD.s13 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc10 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 512) (i0 : fin (VD.s15 224)) (i1 : fin (VD.s15 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc11 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 512) (i0 : fin (VD.s16 224)) (i1 : fin (VD.s16 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc12 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (cc : fin 512) (i0 : fin (VD.s17 224)) (i1 : fin (VD.s17 224)),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gc13 rho) bb) cc) i0) i1 <= R0)%R) ->
  (forall (bb : fin 1) (i : fin 4096),
     (PCG.idx (PCG.idx (Gf1 rho) bb) i <= R0)%R) ->
  (forall (bb : fin 1) (i : fin 4096),
     (PCG.idx (PCG.idx (Gf2 rho) bb) i <= R0)%R) ->
  SEM.eval vgg16_gen_comm rho p =
  @VD.vgg16_comm 1 3 224 224
    (rd Tin "input" rho)
    (rd Tkw1 "conv1_1_w" rho) (rd Tkb64 "conv1_1_b" rho)
    (rd Tkw2 "conv1_2_w" rho) (rd Tkb64 "conv1_2_b" rho)
    (rd Tkw3 "conv2_1_w" rho) (rd Tkb128 "conv2_1_b" rho)
    (rd Tkw4 "conv2_2_w" rho) (rd Tkb128 "conv2_2_b" rho)
    (rd Tkw5 "conv3_1_w" rho) (rd Tkb256 "conv3_1_b" rho)
    (rd Tkw6 "conv3_2_w" rho) (rd Tkb256 "conv3_2_b" rho)
    (rd Tkw6 "conv3_3_w" rho) (rd Tkb256 "conv3_3_b" rho)
    (rd Tkw7 "conv4_1_w" rho) (rd Tkb512 "conv4_1_b" rho)
    (rd Tkw8 "conv4_2_w" rho) (rd Tkb512 "conv4_2_b" rho)
    (rd Tkw8 "conv4_3_w" rho) (rd Tkb512 "conv4_3_b" rho)
    (rd Tkw8 "conv5_1_w" rho) (rd Tkb512 "conv5_1_b" rho)
    (rd Tkw8 "conv5_2_w" rho) (rd Tkb512 "conv5_2_b" rho)
    (rd Tkw8 "conv5_3_w" rho) (rd Tkb512 "conv5_3_b" rho)
    (rd Tfc1w "fc1_w" rho) (rd Tfcb4096 "fc1_b" rho)
    (rd Tfc2w "fc2_w" rho) (rd Tfcb4096 "fc2_b" rho)
    (rd Tfc3w "fc3_w" rho) (rd Tfcb1000 "fc3_b" rho)
    (@CG.vwt Tout "output") rho p.
Proof.
  intros rho p Hinacc Hfresh Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7 Hr8 Hr9 Hr10 Hr11 Hr12 Hr13
    Hr14 Hr15.
  destruct Hfresh as [Htmp [Hl1 [Hl2 [Hl3 [Hl4 [Hl5 [Hl6 [Hl7 [Hl8 [Hl9 [Hl10
    [Hl11 [Hl12 [Hl13 [Hl14 [Hl15 [Hl16 [Hl17 [Hl18 [Hl19 [Hl20 Hl21]]]]]]]]]]]]]]]]]]]]].
  (* Route-A side: collapse [vgg16_comm] to the functional assignment. *)
  assert (HfreshA : @VD.vgg16_fresh 1 224 224 (@CG.vwt Tout "output") rho).
  { unfold VD.vgg16_fresh. repeat split; try assumption;
    intros p0 Hin0 Hin1;
    destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hin0) as [u Heq]; subst p0;
    apply BL.in_acc_acc'_Var in Hin1; injection Hin1 as Hin1; discriminate. }
  rewrite (VD.A_VGG16 (batch:=1) (channel:=3) (m1:=224) (m2:=224)
    (rd Tin "input" rho)
    (rd Tkw1 "conv1_1_w" rho) (rd Tkb64 "conv1_1_b" rho)
    (rd Tkw2 "conv1_2_w" rho) (rd Tkb64 "conv1_2_b" rho)
    (rd Tkw3 "conv2_1_w" rho) (rd Tkb128 "conv2_1_b" rho)
    (rd Tkw4 "conv2_2_w" rho) (rd Tkb128 "conv2_2_b" rho)
    (rd Tkw5 "conv3_1_w" rho) (rd Tkb256 "conv3_1_b" rho)
    (rd Tkw6 "conv3_2_w" rho) (rd Tkb256 "conv3_2_b" rho)
    (rd Tkw6 "conv3_3_w" rho) (rd Tkb256 "conv3_3_b" rho)
    (rd Tkw7 "conv4_1_w" rho) (rd Tkb512 "conv4_1_b" rho)
    (rd Tkw8 "conv4_2_w" rho) (rd Tkb512 "conv4_2_b" rho)
    (rd Tkw8 "conv4_3_w" rho) (rd Tkb512 "conv4_3_b" rho)
    (rd Tkw8 "conv5_1_w" rho) (rd Tkb512 "conv5_1_b" rho)
    (rd Tkw8 "conv5_2_w" rho) (rd Tkb512 "conv5_2_b" rho)
    (rd Tkw8 "conv5_3_w" rho) (rd Tkb512 "conv5_3_b" rho)
    (rd Tfc1w "fc1_w" rho) (rd Tfcb4096 "fc1_b" rho)
    (rd Tfc2w "fc2_w" rho) (rd Tfcb4096 "fc2_b" rho)
    (rd Tfc3w "fc3_w" rho) (rd Tfcb1000 "fc3_b" rho) Hinacc HfreshA).
  cbv [DR.A]. cbv beta.
  (* Route-B side: 38-step forward simulation. *)
  unfold vgg16_gen_comm.
  (* read-only buffer facts at [rho] *)
  assert (SEM.to_pcg_exp (@CG.vrd Tin "input") rho = rd Tin "input" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw1 "conv1_1_w") rho = rd Tkw1 "conv1_1_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb64 "conv1_1_b") rho = rd Tkb64 "conv1_1_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw2 "conv1_2_w") rho = rd Tkw2 "conv1_2_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb64 "conv1_2_b") rho = rd Tkb64 "conv1_2_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw3 "conv2_1_w") rho = rd Tkw3 "conv2_1_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb128 "conv2_1_b") rho = rd Tkb128 "conv2_1_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw4 "conv2_2_w") rho = rd Tkw4 "conv2_2_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb128 "conv2_2_b") rho = rd Tkb128 "conv2_2_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw5 "conv3_1_w") rho = rd Tkw5 "conv3_1_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb256 "conv3_1_b") rho = rd Tkb256 "conv3_1_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw6 "conv3_2_w") rho = rd Tkw6 "conv3_2_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb256 "conv3_2_b") rho = rd Tkb256 "conv3_2_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw6 "conv3_3_w") rho = rd Tkw6 "conv3_3_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb256 "conv3_3_b") rho = rd Tkb256 "conv3_3_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw7 "conv4_1_w") rho = rd Tkw7 "conv4_1_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb512 "conv4_1_b") rho = rd Tkb512 "conv4_1_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw8 "conv4_2_w") rho = rd Tkw8 "conv4_2_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb512 "conv4_2_b") rho = rd Tkb512 "conv4_2_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw8 "conv4_3_w") rho = rd Tkw8 "conv4_3_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb512 "conv4_3_b") rho = rd Tkb512 "conv4_3_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw8 "conv5_1_w") rho = rd Tkw8 "conv5_1_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb512 "conv5_1_b") rho = rd Tkb512 "conv5_1_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw8 "conv5_2_w") rho = rd Tkw8 "conv5_2_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb512 "conv5_2_b") rho = rd Tkb512 "conv5_2_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkw8 "conv5_3_w") rho = rd Tkw8 "conv5_3_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tkb512 "conv5_3_b") rho = rd Tkb512 "conv5_3_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tfc1w "fc1_w") rho = rd Tfc1w "fc1_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tfcb4096 "fc1_b") rho = rd Tfcb4096 "fc1_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tfc2w "fc2_w") rho = rd Tfc2w "fc2_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tfcb4096 "fc2_b") rho = rd Tfcb4096 "fc2_b" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tfc3w "fc3_w") rho = rd Tfc3w "fc3_w" rho) by exact eq_refl.
  assert (SEM.to_pcg_exp (@CG.vrd Tfcb1000 "fc3_b") rho = rd Tfcb1000 "fc3_b" rho) by exact eq_refl.
  (* conv1_1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 3 64 224 (Nat.lt_0_succ 0) (Nat.lt_0_succ 2) (Nat.lt_0_succ 63)
    (ltac:(lia) : 3 <= 224) "conv1_1_b" "conv1_1_w" "input" "conv1_1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv1_1_b".
  rw_fact "conv1_1_w".
  rw_fact "input".
  fold_and_bump "conv1_1_out" (Gc1 rho).
  (* relu1_1 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=64) (m1:=VD.s01 224) (m2:=VD.s01 224)
    "conv1_1_out" "relu1_1_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv1_1_out"; exact (Hr1 bb cc i0 i1) ].
  rw_fact "conv1_1_out".
  clear_fact "conv1_1_out".
  fold_and_bump "relu1_1_out" (OE.ReLU4d (Gc1 rho)).
  (* conv1_2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 64 64 (VD.s01 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 63)
    (Nat.lt_0_succ 63) (ltac:(vm_compute; lia)) "conv1_2_b" "conv1_2_w" "relu1_1_out" "conv1_2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv1_2_b".
  rw_fact "conv1_2_w".
  rw_fact "relu1_1_out".
  clear_fact "relu1_1_out".
  fold_and_bump "conv1_2_out" (Gc2 rho).
  (* relu1_2 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=64) (m1:=VD.s02 224) (m2:=VD.s02 224)
    "conv1_2_out" "relu1_2_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv1_2_out"; exact (Hr2 bb cc i0 i1) ].
  rw_fact "conv1_2_out".
  clear_fact "conv1_2_out".
  fold_and_bump "relu1_2_out" (OE.ReLU4d (Gc2 rho)).
  (* pool1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_pool_gen 1 64 (VD.s02 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 63)
    "relu1_2_out" "pool1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "relu1_2_out".
  clear_fact "relu1_2_out".
  fold_and_bump "pool1_out" (OP.Maxpool4d 2 (OE.ReLU4d (Gc2 rho))).
  (* conv2_1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 64 128 (VD.s03 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 63)
    (Nat.lt_0_succ 127) (ltac:(vm_compute; lia)) "conv2_1_b" "conv2_1_w" "pool1_out" "conv2_1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv2_1_b".
  rw_fact "conv2_1_w".
  rw_fact "pool1_out".
  clear_fact "pool1_out".
  fold_and_bump "conv2_1_out" (Gc3 rho).
  (* relu2_1 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=128) (m1:=VD.s04 224) (m2:=VD.s04 224)
    "conv2_1_out" "relu2_1_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv2_1_out"; exact (Hr3 bb cc i0 i1) ].
  rw_fact "conv2_1_out".
  clear_fact "conv2_1_out".
  fold_and_bump "relu2_1_out" (OE.ReLU4d (Gc3 rho)).
  (* conv2_2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 128 128 (VD.s04 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 127)
    (Nat.lt_0_succ 127) (ltac:(vm_compute; lia)) "conv2_2_b" "conv2_2_w" "relu2_1_out" "conv2_2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv2_2_b".
  rw_fact "conv2_2_w".
  rw_fact "relu2_1_out".
  clear_fact "relu2_1_out".
  fold_and_bump "conv2_2_out" (Gc4 rho).
  (* relu2_2 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=128) (m1:=VD.s05 224) (m2:=VD.s05 224)
    "conv2_2_out" "relu2_2_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv2_2_out"; exact (Hr4 bb cc i0 i1) ].
  rw_fact "conv2_2_out".
  clear_fact "conv2_2_out".
  fold_and_bump "relu2_2_out" (OE.ReLU4d (Gc4 rho)).
  (* pool2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_pool_gen 1 128 (VD.s05 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 127)
    "relu2_2_out" "pool2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "relu2_2_out".
  clear_fact "relu2_2_out".
  fold_and_bump "pool2_out" (OP.Maxpool4d 2 (OE.ReLU4d (Gc4 rho))).
  (* conv3_1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 128 256 (VD.s06 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 127)
    (Nat.lt_0_succ 255) (ltac:(vm_compute; lia)) "conv3_1_b" "conv3_1_w" "pool2_out" "conv3_1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv3_1_b".
  rw_fact "conv3_1_w".
  rw_fact "pool2_out".
  clear_fact "pool2_out".
  fold_and_bump "conv3_1_out" (Gc5 rho).
  (* relu3_1 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=256) (m1:=VD.s07 224) (m2:=VD.s07 224)
    "conv3_1_out" "relu3_1_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv3_1_out"; exact (Hr5 bb cc i0 i1) ].
  rw_fact "conv3_1_out".
  clear_fact "conv3_1_out".
  fold_and_bump "relu3_1_out" (OE.ReLU4d (Gc5 rho)).
  (* conv3_2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 256 256 (VD.s07 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 255)
    (Nat.lt_0_succ 255) (ltac:(vm_compute; lia)) "conv3_2_b" "conv3_2_w" "relu3_1_out" "conv3_2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv3_2_b".
  rw_fact "conv3_2_w".
  rw_fact "relu3_1_out".
  clear_fact "relu3_1_out".
  fold_and_bump "conv3_2_out" (Gc6 rho).
  (* relu3_2 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=256) (m1:=VD.s08 224) (m2:=VD.s08 224)
    "conv3_2_out" "relu3_2_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv3_2_out"; exact (Hr6 bb cc i0 i1) ].
  rw_fact "conv3_2_out".
  clear_fact "conv3_2_out".
  fold_and_bump "relu3_2_out" (OE.ReLU4d (Gc6 rho)).
  (* conv3_3 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 256 256 (VD.s08 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 255)
    (Nat.lt_0_succ 255) (ltac:(vm_compute; lia)) "conv3_3_b" "conv3_3_w" "relu3_2_out" "conv3_3_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv3_3_b".
  rw_fact "conv3_3_w".
  rw_fact "relu3_2_out".
  clear_fact "relu3_2_out".
  fold_and_bump "conv3_3_out" (Gc7 rho).
  (* relu3_3 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=256) (m1:=VD.s09 224) (m2:=VD.s09 224)
    "conv3_3_out" "relu3_3_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv3_3_out"; exact (Hr7 bb cc i0 i1) ].
  rw_fact "conv3_3_out".
  clear_fact "conv3_3_out".
  fold_and_bump "relu3_3_out" (OE.ReLU4d (Gc7 rho)).
  (* pool3 *)
  rewrite BL.eval_seq'.
  rewrite (HB_pool_gen 1 256 (VD.s09 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 255)
    "relu3_3_out" "pool3_out");
    [| str_neq1_tac | str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "relu3_3_out".
  clear_fact "relu3_3_out".
  fold_and_bump "pool3_out" (OP.Maxpool4d 2 (OE.ReLU4d (Gc7 rho))).
  (* conv4_1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 256 512 (VD.s10 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 255)
    (Nat.lt_0_succ 511) (ltac:(vm_compute; lia)) "conv4_1_b" "conv4_1_w" "pool3_out" "conv4_1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv4_1_b".
  rw_fact "conv4_1_w".
  rw_fact "pool3_out".
  clear_fact "pool3_out".
  fold_and_bump "conv4_1_out" (Gc8 rho).
  (* relu4_1 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=512) (m1:=VD.s11 224) (m2:=VD.s11 224)
    "conv4_1_out" "relu4_1_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv4_1_out"; exact (Hr8 bb cc i0 i1) ].
  rw_fact "conv4_1_out".
  clear_fact "conv4_1_out".
  fold_and_bump "relu4_1_out" (OE.ReLU4d (Gc8 rho)).
  (* conv4_2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 512 512 (VD.s11 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    (Nat.lt_0_succ 511) (ltac:(vm_compute; lia)) "conv4_2_b" "conv4_2_w" "relu4_1_out" "conv4_2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv4_2_b".
  rw_fact "conv4_2_w".
  rw_fact "relu4_1_out".
  clear_fact "relu4_1_out".
  fold_and_bump "conv4_2_out" (Gc9 rho).
  (* relu4_2 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=512) (m1:=VD.s12 224) (m2:=VD.s12 224)
    "conv4_2_out" "relu4_2_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv4_2_out"; exact (Hr9 bb cc i0 i1) ].
  rw_fact "conv4_2_out".
  clear_fact "conv4_2_out".
  fold_and_bump "relu4_2_out" (OE.ReLU4d (Gc9 rho)).
  (* conv4_3 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 512 512 (VD.s12 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    (Nat.lt_0_succ 511) (ltac:(vm_compute; lia)) "conv4_3_b" "conv4_3_w" "relu4_2_out" "conv4_3_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv4_3_b".
  rw_fact "conv4_3_w".
  rw_fact "relu4_2_out".
  clear_fact "relu4_2_out".
  fold_and_bump "conv4_3_out" (Gc10 rho).
  (* relu4_3 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=512) (m1:=VD.s13 224) (m2:=VD.s13 224)
    "conv4_3_out" "relu4_3_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv4_3_out"; exact (Hr10 bb cc i0 i1) ].
  rw_fact "conv4_3_out".
  clear_fact "conv4_3_out".
  fold_and_bump "relu4_3_out" (OE.ReLU4d (Gc10 rho)).
  (* pool4 *)
  rewrite BL.eval_seq'.
  rewrite (HB_pool_gen 1 512 (VD.s13 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    "relu4_3_out" "pool4_out");
    [| str_neq1_tac | str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "relu4_3_out".
  clear_fact "relu4_3_out".
  fold_and_bump "pool4_out" (OP.Maxpool4d 2 (OE.ReLU4d (Gc10 rho))).
  (* conv5_1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 512 512 (VD.s14 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    (Nat.lt_0_succ 511) (ltac:(vm_compute; lia)) "conv5_1_b" "conv5_1_w" "pool4_out" "conv5_1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv5_1_b".
  rw_fact "conv5_1_w".
  rw_fact "pool4_out".
  clear_fact "pool4_out".
  fold_and_bump "conv5_1_out" (Gc11 rho).
  (* relu5_1 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=512) (m1:=VD.s15 224) (m2:=VD.s15 224)
    "conv5_1_out" "relu5_1_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv5_1_out"; exact (Hr11 bb cc i0 i1) ].
  rw_fact "conv5_1_out".
  clear_fact "conv5_1_out".
  fold_and_bump "relu5_1_out" (OE.ReLU4d (Gc11 rho)).
  (* conv5_2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 512 512 (VD.s15 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    (Nat.lt_0_succ 511) (ltac:(vm_compute; lia)) "conv5_2_b" "conv5_2_w" "relu5_1_out" "conv5_2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv5_2_b".
  rw_fact "conv5_2_w".
  rw_fact "relu5_1_out".
  clear_fact "relu5_1_out".
  fold_and_bump "conv5_2_out" (Gc12 rho).
  (* relu5_2 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=512) (m1:=VD.s16 224) (m2:=VD.s16 224)
    "conv5_2_out" "relu5_2_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv5_2_out"; exact (Hr12 bb cc i0 i1) ].
  rw_fact "conv5_2_out".
  clear_fact "conv5_2_out".
  fold_and_bump "relu5_2_out" (OE.ReLU4d (Gc12 rho)).
  (* conv5_3 *)
  rewrite BL.eval_seq'.
  rewrite (HB_conv_gen 1 512 512 (VD.s16 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    (Nat.lt_0_succ 511) (ltac:(vm_compute; lia)) "conv5_3_b" "conv5_3_w" "relu5_2_out" "conv5_3_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "conv5_3_b".
  rw_fact "conv5_3_w".
  rw_fact "relu5_2_out".
  clear_fact "relu5_2_out".
  fold_and_bump "conv5_3_out" (Gc13 rho).
  (* relu5_3 *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU4d_buf (b:=1) (c:=512) (m1:=VD.s17 224) (m2:=VD.s17 224)
    "conv5_3_out" "relu5_3_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb cc i0 i1; rw_fact "conv5_3_out"; exact (Hr13 bb cc i0 i1) ].
  rw_fact "conv5_3_out".
  clear_fact "conv5_3_out".
  fold_and_bump "relu5_3_out" (OE.ReLU4d (Gc13 rho)).
  (* pool5 *)
  rewrite BL.eval_seq'.
  rewrite (HB_pool_gen 1 512 (VD.s17 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    "relu5_3_out" "pool5_out");
    [| str_neq1_tac | str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "relu5_3_out".
  clear_fact "relu5_3_out".
  fold_and_bump "pool5_out" (OP.Maxpool4d 2 (OE.ReLU4d (Gc13 rho))).
  (* flatten *)
  rewrite BL.eval_seq'.
  rewrite (HB_flat_gen 1 512 (VD.s18 224) (VD.s18 224) (Nat.lt_0_succ 0) (Nat.lt_0_succ 511)
    (Nat.lt_0_succ 6) (Nat.lt_0_succ 6) "pool5_out" "flatten_out");
    [| str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "pool5_out".
  clear_fact "pool5_out".
  fold_and_bump "flatten_out" (AD.Flatten4d (OP.Maxpool4d 2 (OE.ReLU4d (Gc13 rho)))).
  (* fc1 *)
  rewrite BL.eval_seq'.
  rewrite (HB_linear_gen 1 (512 * VD.s18 224 * VD.s18 224) 4096
    "fc1_b" "fc1_w" "flatten_out" "fc1_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "fc1_b".
  rw_fact "fc1_w".
  rw_fact "flatten_out".
  clear_fact "flatten_out".
  fold_and_bump "fc1_out" (Gf1 rho).
  (* fc1_relu *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU2d_buf (m1:=1) (m2:=4096) "fc1_out" "fc1_relu_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb i; rw_fact "fc1_out"; exact (Hr14 bb i) ].
  rw_fact "fc1_out".
  clear_fact "fc1_out".
  fold_and_bump "fc1_relu_out" (LF.ReLU2d (Gf1 rho)).
  (* fc2 *)
  rewrite BL.eval_seq'.
  rewrite (HB_linear_gen 1 4096 4096 "fc2_b" "fc2_w" "fc1_relu_out" "fc2_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "fc2_b".
  rw_fact "fc2_w".
  rw_fact "fc1_relu_out".
  clear_fact "fc1_relu_out".
  fold_and_bump "fc2_out" (Gf2 rho).
  (* fc2_relu *)
  rewrite BL.eval_seq'.
  rewrite (bridge_ReLU2d_buf (m1:=1) (m2:=4096) "fc2_out" "fc2_relu_out");
    [| discriminate | discriminate | str_neq_tac |
       intros bb i; rw_fact "fc2_out"; exact (Hr15 bb i) ].
  rw_fact "fc2_out".
  clear_fact "fc2_out".
  fold_and_bump "fc2_relu_out" (LF.ReLU2d (Gf2 rho)).
  (* fc3 *)
  rewrite BL.eval_seq'.
  rewrite (HB_linear_gen 1 4096 1000 "fc3_b" "fc3_w" "fc2_relu_out" "fc3_out");
    [| str_neq1_tac | str_neq1_tac | str_neq1_tac | str_neq1_tac
     | str_neq_tac | str_neq_tac | str_neq_tac | su_fact ].
  rw_fact "fc3_b".
  rw_fact "fc3_w".
  rw_fact "fc2_relu_out".
  clear_fact "fc2_relu_out".
  fold_and_bump "fc3_out" (OP.Linear2d (rd Tfc3w "fc3_w" rho) (rd Tfcb1000 "fc3_b" rho) (LF.ReLU2d (Gf2 rho))).
  (* output: softmax *)
  rewrite (HB_softmax_gen 1 1000 (Nat.lt_0_succ 0) (Nat.lt_0_succ 999) "fc3_out" "output");
    [| str_neq1_tac | str_neq1_tac | str_neq_tac | su_fact ].
  rw_fact "fc3_out".
  (* Observe at [p] inside the output buffer. *)
  rewrite (SEM.assign_in_acc_independent_of_env _ _ _ _ rho _ Hinacc).
  rewrite <- Gout_body.
  rewrite vgg16_out_eq.
  exact eq_refl.
Qed.

Print Assumptions Bridge_VGG16.
