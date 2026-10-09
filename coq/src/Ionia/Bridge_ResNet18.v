(* ========================================================================= *)
(* Bridge_ResNet18.v                                                         *)
(*                                                                           *)
(* Whole-network route-A/route-B bridge for ResNet18 (batch = 1, 3x224x224   *)
(* input, 1000 classes):                                                     *)
(*                                                                           *)
(*   eval resnet18_AST rho p  =  resnet18_comm (route A) ... rho p           *)
(*                                                                           *)
(* pointwise at every path [p] inside the output accumulator.                *)
(*                                                                           *)
(* Route B (code generation): a self-assembled sequential composition of     *)
(*   per-layer AST commands — [Bridge_ReduceConv2.Conv4d_ast_comm] (the      *)
(*   general Conv4d covering the 7x7s2p3 stem, the 3x3s1p1 block convs, the  *)
(*   3x3s2p1 downsample convs and the 1x1s2 projection convs),               *)
(*   [CNN_Examples_Base.BatchNorm4d_comm] (inference mode; mean/var          *)
(*   instantiated with [Bridge_ReduceConv2.bn1_mean]/[bn1_var], the batch=1  *)
(*   alignment of route A's online batch statistics — see the header note    *)
(*   of [Bridge_ReduceConv2]), [CNN_Examples_Base_Ops.ReLU4d_comm],          *)
(*   [CNN_Examples_Base.Add4d_comm] (residual),                              *)
(*   [Bridge_ReduceConv2.Maxpool4d_pad_ast_comm] (stem pool),                *)
(*   [CNN_Examples_Base_Ops.GlobalAvgPool4d_comm]/[Linear2d_comm]/           *)
(*   [Softmax2d_comm] (classifier).  Buffer names follow                     *)
(*   [CNN_Examples_ResNet18]; each block's post-add ReLU writes a fresh      *)
(*   buffer ("lX_bY_out") since the bridge needs read/write separation.      *)
(* Route A (DPIA): [ResNet18_DPIA.resnet18_comm] with its proved whole-      *)
(*   network collapse [ResNet18_DPIA.A_ResNet18].                            *)
(*                                                                           *)
(* Structural notes:                                                         *)
(* 1. Single-output side conditions.  The operator equivalences              *)
(*    [Bridge_ReduceConv2.Conv4d_sem]/[Maxpool4d_pad_sem] and                *)
(*    [Operators_Sem_Equiv.GlobalAvgPool4d_sem]/[Linear2d_sem]/              *)
(*    [Softmax2d_sem] universally quantify the output acceptor in their      *)
(*    independence premises ([forall output', exp_independent_of_acc input   *)
(*    output']), which is unsatisfiable for buffer-read inputs such as       *)
(*    [vrd "l1_b1_relu1_out"] (take [output'] to be an acceptor over the     *)
(*    buffer's own paths).  Exactly as [Bridge_LeNet5] did for LeNet-5,      *)
(*    this file re-proves single-output variants ([Conv4d_sem_single],       *)
(*    [Maxpool4d_pad_sem_single], [GlobalAvgPool4d_sem_single],              *)
(*    [Linear2d_sem_single], [Softmax2d_sem_single]) by replaying the        *)
(*    original proofs with the concrete-output premises; all heavy           *)
(*    machinery (sum/max flattening, continuation lemmas, padding            *)
(*    independence) is reused from [Bridge_ReduceConv2] and                  *)
(*    [Operators_Sem_Equiv].                                                 *)
(* 2. Canonical conv variants.  Route A uses the canonical-size variants     *)
(*    [ResNet18_DPIA.Conv4d_3x3_s1]/[Conv4d_3x3_s2]/[Conv4d_1x1_s2] while    *)
(*    route B lands at [Ops_Conv.Conv4d p s].  At the concrete ResNet18      *)
(*    sizes the stride-2/1x1/stem instances are convertible; the stride-1    *)
(*    3x3 instances differ only by [fin2nat i0 * 1] vs [fin2nat i0] and are  *)
(*    bridged by [conv4d_s1_eq_56/28/14/7].                                  *)
(* 3. ReLU side conditions.  As in [Bridge_LeNet5], the runtime boolean      *)
(*    guard of [ReLU4d_equiv_sem] is discharged from an [Rle] premise on     *)
(*    each ReLU input (the functional value fed into each of the 17 ReLU     *)
(*    layers is assumed pointwise [<= 0]).                                   *)
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
  Ionia.FusionTactics Ionia.Bridge_ReduceConv Ionia.Bridge_Elementwise
  Ionia.Bridge_ReduceConv2 Ionia.Bridge_LeNet5
  Ionia.Ops_Conv Ionia.Ops_BatchNorm Ionia.Ops_Elementwise
  Ionia.Ops_PoolPad Ionia.Ops_Reduce Ionia.AlexNet_DPIA Ionia.ResNet18_DPIA.

Open Scope string_scope.

(* See [Bridge_LeNet5] for why keyed unification is needed here. *)
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
Module V := Ionia.vector.
Module BRC := Ionia.Bridge_ReduceConv.
Module BE := Ionia.Bridge_Elementwise.
Module BR2 := Ionia.Bridge_ReduceConv2.
Module BL := Ionia.Bridge_LeNet5.
Module OC := Ionia.Ops_Conv.
Module OB := Ionia.Ops_BatchNorm.
Module OE := Ionia.Ops_Elementwise.
Module OP := Ionia.Ops_PoolPad.
Module OR := Ionia.Ops_Reduce.
Module AD := Ionia.AlexNet_DPIA.
Module RD := Ionia.ResNet18_DPIA.
Module FTac := Ionia.FusionTactics.

(* 4-D tensor buffer type. *)
Definition T4 (batch channel m1 m2 : nat) : data :=
  ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))).

(* Reading buffer [s] of type [d] in [rho], as a route-A expression. *)
Definition Rd (d : data) (s : string) (rho : PCG.env) : PCG.exp d :=
  SEM.to_pcg_exp (@CG.vrd d s) rho.

(* -------------------------------------------------------------------------- *)
(* Name-infrastructure helpers (4-D/2-D tmp disjointness, scalar reads)       *)
(* -------------------------------------------------------------------------- *)

(* tmp disjointness of a 4d output buffer (conv4d/maxp4dp shape) *)
Lemma tmp_disj_vwt4 : forall (n1 n2 n3 n4 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (b : fin n1) (nu : fin n2) (i0 : fin n3) (j0 : fin n4),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p
        ((@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} (ary '{n4} num)))) s)
           |{ b} |{ nu} |{ i0} |{ j0}).
Proof.
  intros n1 n2 n3 n4 s Hneq p b nu i0 j0 Hp Hin.
  apply BL.in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

(* tmp disjointness of a 2d output buffer (gap/linear/softmax shape) *)
Lemma tmp_disj_vwt2 : forall (n1 n2 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (b : fin n1) (c : fin n2),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p ((@CG.vwt (ary '{n1} (ary '{n2} num)) s) |{ b} |{ c}).
Proof.
  intros n1 n2 s Hneq p b c Hp Hin.
  apply BL.in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

(* Type-polymorphic read-after-write for a SCALAR read (e.g. "bn_eps") past
   an array write.  Mirror of [BL.vrd_after_other_vwt_ary_gen] at [num]. *)
Lemma vrd_num_after_other_vwt_ary : forall (n : nat) (f : fle n) (d : data)
  (si t : string),
  (forall w u : string, (t ++ w <> si ++ "[" ++ u)%string) ->
  forall (v : PCG.exp (ary f d)) (rho : PCG.env),
    SEM.to_pcg_exp (@CG.vrd num t)
      (PCG.assign (@CG.vwt (ary f d) si) v rho) =
    SEM.to_pcg_exp (@CG.vrd num t) rho.
Proof.
  intros n f d si t Hdiv v rho.
  apply (@SEM.exp_independent_of_acc_eval num (ary f d)
           (@CG.vrd num t) (@CG.vwt (ary f d) si)).
  - intros p Hp. destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply SEM.exp_indep_vrd_Var. intros w Hw.
    exact (Hdiv w u Hw).
  - intros q Hq. apply PCG.assign_not_in_acc. exact Hq.
Qed.

(* String name-clash solvers (local copies of the [Bridge_LeNet5] tactics). *)
Ltac str_neq_tac := intros u v Heq; discriminate.
Ltac str_neq1_tac := intros u Heq; discriminate.

(* Discharge [StructUndefined tmp] at any stage env. *)
Ltac su_tmp_tac :=
  repeat (apply BL.SU_tmp_after_assign_vwt; [ intros u Heq; discriminate | ]);
  assumption.

(* -------------------------------------------------------------------------- *)
(* Conv4d: single-output semantic equivalence                                 *)
(*                                                                            *)
(*   Replay of [Bridge_ReduceConv2.Conv4d_sem] with the universally           *)
(*   quantified independence premises replaced by concrete-output ones.       *)
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
Variables (output : DE.acc (ary '{batch} (ary '{filernum}
  (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))).
Hypothesis Hinput_out : SEM.exp_independent_of_acc input output.
Hypothesis Hw_out : SEM.exp_independent_of_acc w output.
Hypothesis Hb_out : SEM.exp_independent_of_acc bias output.

Let out_h := ((m1 - n1 + 2 * p) / s + 1).
Let out_w := ((m2 - n2 + 2 * p) / s + 1).

Local Notation idxc :=
  (BR2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input).
Local Notation flatc :=
  (BR2.conv4d_flat_cell batch m1 m2 n1 n2 channel filernum p s w input).

Lemma conv4d_cell_indep_out_single : forall
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  SEM.exp_independent_of_acc
    (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel =>
      CD.sum (DE.mkvSeq (fun i1 : fin n1 =>
        CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1)))))))
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
    unfold BR2.conv4d_idx_cell.
    apply SEM.exp_independent_of_acc_mul.
    + repeat apply OSE.safe_idx_nat_independent.
      apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx.
      apply BR2.Padding4d_independent.
      exact Hinput_out.
    + repeat apply SEM.exp_independent_of_acc_idx.
      exact Hw_out.
  - apply SEM.exp_independent_of_acc_idx.
    exact Hb_out.
Qed.

Theorem Conv4d_sem_single : forall (rho : PCG.env),
  BR2.tmp_disjoint_from_output_conv4d batch m1 m2 n1 n2 filernum p s output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CG.A (output, COP.Conv4d p s bias w input)) rho =
  SEM.eval (BR2.Conv4d_ast_comm p s bias w input output) rho.
Proof.
  intros rho Hdisj Hundef.
  unfold CG.A, COP.Conv4d, CD.let_binding, BR2.Conv4d_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin out_h =>
        DE.mkvSeq (fun j0 : fin out_w =>
          CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply conv4d_cell_indep_out_single. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* batch slice b *)
    assert (Hcell_b : forall nu i0 j0,
      SEM.exp_independent_of_acc
        (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
        (output |{ b})).
    { intros nu i0 j0 p0 Hp.
      apply (conv4d_cell_indep_out_single b nu i0 j0).
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
          (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
          ((output |{ b}) |{ nu})).
      { intros i0 j0 p0 Hp.
        apply (conv4d_cell_indep_out_single b nu i0 j0).
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
            (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
            (((output |{ b}) |{ nu}) |{ i0})).
        { intros j0 p0 Hp.
          apply (conv4d_cell_indep_out_single b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
          exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- (* the cell: loopacc elimination *)
           set (e := DE.mkvSeq (flatc b nu i0 j0)).
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
           change (SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
             (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * n1 * n2) =>
               CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp))) eta''').
           assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1))))))) eta''' =
             SEM.to_pcg_exp (CD.sum e) eta''').
           { unfold e. apply BR2.conv4d_sum_flatten; assumption. }
           assert (Heq_aux : SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => idxc b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval_aux (c (CD.sum e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal.
             rewrite !OSE.to_pcg_exp_add. f_equal.
             { exact Hsum_eq. } }
           rewrite Heq_aux.
           apply SEM.eval_csum_equiv.
           ++ exact HPeta'''.
           ++ unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              unfold BR2.conv4d_flat_cell.
              apply SEM.exp_independent_of_acc_mul.
              ** repeat apply OSE.safe_idx_nat_independent.
                 apply SEM.exp_independent_of_acc_idx.
                 apply SEM.exp_independent_of_acc_idx.
                 apply BR2.Padding4d_independent.
                 exact Hinput_indep.
              ** repeat apply SEM.exp_independent_of_acc_idx.
                 exact Hw_indep.
           ++ apply BR2.conv4d_cell_continuation_ok; assumption.
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
(* Maxpool4d_pad: single-output semantic equivalence                          *)
(*                                                                            *)
(*   Replay of [Bridge_ReduceConv2.Maxpool4d_pad_sem] with the concrete       *)
(*   output acceptor.                                                         *)
(* -------------------------------------------------------------------------- *)

Section Maxpool4d_pad_Single.

Variables (batch filernum m1 m2 kersize stride padding : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))).
Hypothesis Hs : stride > 0.
Hypothesis Hbatch : batch > 0.
Hypothesis Hfilernum : filernum > 0.
Hypothesis Hk : kersize > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Variables (output : DE.acc (ary '{batch} (ary '{filernum}
  (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
  (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))).
Hypothesis Hinput_out : SEM.exp_independent_of_acc input output.

Let out_h := ((m1 - kersize + 2 * padding) / stride + 1).
Let out_w := ((m2 - kersize + 2 * padding) / stride + 1).

Local Notation flatm :=
  (BR2.maxp4dp_flat_cell batch filernum m1 m2 kersize stride padding input).

Lemma maxp4dp_cell_indep_out_single : forall
  (b : fin batch) (nu : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
  SEM.exp_independent_of_acc
    (CD.max (DE.mkvSeq (fun i1 : fin kersize =>
      CD.max (DE.mkvSeq (fun j1 : fin kersize =>
        CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu])
          (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
    output.
Proof.
  intros b nu i0 j0.
  apply OSE.exp_independent_of_acc_max; intro i1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_max; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply OSE.safe_idx_nat_independent.
  apply SEM.exp_independent_of_acc_idx.
  apply SEM.exp_independent_of_acc_idx.
  apply BR2.Padding4d_independent.
  exact Hinput_out.
Qed.

Theorem Maxpool4d_pad_sem_single : forall (rho : PCG.env),
  BR2.tmp_disjoint_from_output_maxp4dp batch filernum m1 m2 kersize stride
    padding output ->
  (@PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho) ->
  SEM.eval (CG.A (output, BR2.maxp4dp_exp kersize stride padding input)) rho =
  SEM.eval (BR2.Maxpool4d_pad_ast_comm kersize stride padding input output) rho.
Proof.
  intros rho Hdisj Hundef.
  unfold CG.A, BR2.maxp4dp_exp, CD.let_binding, BR2.Maxpool4d_pad_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin out_h =>
        DE.mkvSeq (fun j0 : fin out_w =>
          CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply maxp4dp_cell_indep_out_single. }
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
      apply (maxp4dp_cell_indep_out_single b nu i0 j0).
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
        apply (maxp4dp_cell_indep_out_single b nu i0 j0).
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
          apply (maxp4dp_cell_indep_out_single b nu i0 j0).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
          exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- (* the cell: loopacc elimination *)
           set (e := DE.mkvSeq (flatm b nu i0 j0)).
           set (c := fun r : DE.exp num =>
             (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= r).
           assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (kersize * kersize) =>
                 CG.If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (CG.vrd tmp))
                   (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
               (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= (CG.vrd tmp : DE.exp num)))
             = (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (kersize * kersize) =>
                 CG.If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                   (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
               (((output |{ b}) |{ nu}) |{ i0}) |{ j0} |:= (CG.vrd tmp : DE.exp num)))).
           { f_equal. apply functional_extensionality; intro tmp.
             assert (Hfor : CG.seqfor (fun kk : fin (kersize * kersize) =>
                       CG.If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (CG.vrd tmp))
                         (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))
                     = CG.seqfor (fun kk : fin (kersize * kersize) =>
                       CG.If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                         (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))).
             { apply FTac.seqfor_extensionality; intro kk.
               assert (Heq : CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize) = DE.idx e kk).
               { unfold e, BR2.maxp4dp_flat_cell, DE.idx, DE.mkvSeq.
                 rewrite V.v_idx_mk_vec. reflexivity. }
               rewrite Heq. reflexivity. }
             rewrite Hfor. reflexivity. }
           rewrite Hrhs.
           rewrite SEM.eval_assign.
           rewrite <- (SEM.eval_assign_aux 1 num _ _ eta''').
           change (SEM.eval_aux (c (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
               (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (kersize * kersize) =>
                 CG.If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                   (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num))) ';
               c (CG.vrd tmp))) eta''').
           assert (Hmax_eq : SEM.to_pcg_exp (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))) eta''' =
             SEM.to_pcg_exp (CD.max e) eta''').
           { unfold e. apply BR2.maxp4dp_nested_max_flat; assumption. }
           assert (Heq_aux : SEM.eval_aux (c (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))) 1 eta''' =
             SEM.eval_aux (c (CD.max e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal. exact Hmax_eq. }
           rewrite Heq_aux.
           apply SEM.eval_cmax_equiv.
           ++ exact HPeta'''.
           ++ unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              unfold BR2.maxp4dp_flat_cell.
              repeat apply OSE.safe_idx_nat_independent.
              apply SEM.exp_independent_of_acc_idx.
              apply SEM.exp_independent_of_acc_idx.
              apply BR2.Padding4d_independent.
              exact Hinput_indep.
           ++ apply BR2.maxp4dp_cell_continuation_ok; assumption.
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

End Maxpool4d_pad_Single.

(* -------------------------------------------------------------------------- *)
(* GlobalAvgPool4d: single-output semantic equivalence                        *)
(*                                                                            *)
(*   Replay of [Operators_Sem_Equiv.GlobalAvgPool4d_sem] with the concrete    *)
(*   output acceptor.                                                         *)
(* -------------------------------------------------------------------------- *)

Section GlobalAvgPool4d_Single.

Variables (batch channel m1 m2 : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))).
Hypothesis Hbatch : batch > 0.
Hypothesis Hchannel : channel > 0.
Hypothesis Hm1 : m1 > 0.
Hypothesis Hm2 : m2 > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Variables (output : DE.acc (ary '{batch} (ary '{channel} num))).
Hypothesis Hinput_out : SEM.exp_independent_of_acc input output.

Local Notation gapc := (OSE.GAP_flat_cell m1 m2 input).

Lemma gap_cell_indep_out_single : forall (b : fin batch) (c : fin channel),
  SEM.exp_independent_of_acc
    (CD.div_n (CD.sum (DE.mkvSeq (fun i : fin m1 =>
      CD.sum (DE.mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) (m1 * m2))
    output.
Proof.
  intros b c.
  apply OSE.exp_independent_of_acc_div_n.
  apply OSE.exp_independent_of_acc_sum. intro i.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_sum. intro j.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply SEM.exp_independent_of_acc_idx. exact Hinput_out.
Qed.

Theorem GlobalAvgPool4d_sem_single : forall (rho : PCG.env),
  OSE.tmp_disjoint_from_output_gap batch channel output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.GlobalAvgPool4d batch channel m1 m2 input)) rho =
  SEM.eval (@CEO.GlobalAvgPool4d_comm batch channel m1 m2 input output) rho.
Proof.
  intros rho Hdisj Hundef.
  unfold CG.A, COP.GlobalAvgPool4d, CEO.GlobalAvgPool4d_comm.
  set (row := fun b : fin batch => DE.mkvSeq (fun c : fin channel =>
    CD.div_n (CD.sum (DE.mkvSeq (fun i : fin m1 =>
      CD.sum (DE.mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) (m1 * m2))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros c.
    apply gap_cell_indep_out_single. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - (* Row-level equivalence. *)
    assert (Hcell_indep_b : forall c,
      SEM.exp_independent_of_acc
        (CD.div_n (CD.sum (DE.mkvSeq (fun i : fin m1 =>
          CD.sum (DE.mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) (m1 * m2))
        (output |{ b})).
    { intros c. unfold SEM.exp_independent_of_acc. intros p Hp.
      apply (gap_cell_indep_out_single b c).
      simpl in Hp. destruct Hp as [c' Hc'].
      simpl. exists b. exists c'. exact Hc'. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros c; apply Hcell_indep_b ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros c eta' HPeta'. split.
    + set (e := DE.mkvSeq (gapc b c)).
      set (c' := fun r : DE.exp num => (output|{b}|{c}) |:= CD.div_n r (m1 * m2)).
      assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun k : fin (m1 * m2) =>
            CG.vwt tmp |:= CD.add (CD.safe_idx_nat (CD.safe_idx_nat input|[b]|[c]
              (Nat.div (fin2nat k) m2)) (Nat.modulo (fin2nat k) m2)) (CG.vrd tmp))
          '; (output|{b}|{c}) |:= CD.div_n (CG.vrd tmp) (m1 * m2)))
        = (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun k : fin (m1 * m2) =>
            CG.vwt tmp |:= CD.add (DE.idx e k) (CG.vrd tmp))
          '; (output|{b}|{c}) |:= CD.div_n (CG.vrd tmp) (m1 * m2)))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun k : fin (m1 * m2) =>
                        CG.vwt tmp |:= CD.add (CD.safe_idx_nat (CD.safe_idx_nat input|[b]|[c]
                          (Nat.div (fin2nat k) m2)) (Nat.modulo (fin2nat k) m2)) (CG.vrd tmp))
                    = CG.seqfor (fun k : fin (m1 * m2) =>
                        CG.vwt tmp |:= CD.add (DE.idx e k) (CG.vrd tmp))).
        { apply FTac.seqfor_extensionality; intro k.
          assert (Heq : CD.safe_idx_nat (CD.safe_idx_nat input|[b]|[c]
                          (Nat.div (fin2nat k) m2)) (Nat.modulo (fin2nat k) m2) = DE.idx e k).
          { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      rewrite SEM.eval_assign.
      rewrite <- (SEM.eval_assign_aux 1 num _ _ eta').
      change (SEM.eval_aux (c' (CD.sum (DE.mkvSeq (fun i : fin m1 =>
        CD.sum (DE.mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j])))))) 1 eta' =
        SEM.eval (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun k : fin (m1 * m2) =>
            CG.vwt tmp |:= CD.add (DE.idx e k) (CG.vrd tmp))
          '; c' (CG.vrd tmp))) eta').
      assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun i : fin m1 =>
        CD.sum (DE.mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) eta' =
        SEM.to_pcg_exp (CD.sum e) eta').
      { unfold e. apply OSE.GAP_nested_sum_flat; assumption. }
      assert (Heq_aux : SEM.eval_aux (c' (CD.sum (DE.mkvSeq (fun i : fin m1 =>
        CD.sum (DE.mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j])))))) 1 eta' =
        SEM.eval_aux (c' (CD.sum e)) 1 eta').
      { unfold c'. rewrite !SEM.eval_assign_aux. f_equal.
        rewrite !OSE.to_pcg_exp_div_n. f_equal. exact Hsum_eq. }
      rewrite Heq_aux.
      apply SEM.eval_csum_equiv.
      * exact HPeta'.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro k.
        unfold OSE.GAP_flat_cell. repeat apply OSE.safe_idx_nat_independent.
        apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx.
        exact Hinput_indep.
      * apply OSE.GlobalAvgPool4d_cell_continuation_ok; assumption.
    + rewrite SEM.eval_assign.
      apply OSE.assign_preserves_StructUndefined_tmp.
      * intros p Hp Hout. apply (Hdisj p b c Hp). exact Hout.
      * exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros c rho'. apply PCG.assign_not_in_acc.
      intros Hc. apply (Hdisj OSE.tmp_path b c OSE.in_acc_tmp_scalar_acc). exact Hc.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

End GlobalAvgPool4d_Single.

(* -------------------------------------------------------------------------- *)
(* Linear2d: single-output semantic equivalence                               *)
(*                                                                            *)
(*   Replay of [Operators_Sem_Equiv.Linear2d_sem] with the concrete output    *)
(*   acceptor.                                                                *)
(* -------------------------------------------------------------------------- *)

Section Linear2d_Single.

Variables (batch m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num))).
Hypothesis Hbatch : batch > 0.
Hypothesis Hm : m > 0.
Hypothesis Houtnum : outnum > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Hypothesis Hw_indep : SEM.exp_independent_of_acc w OSE.tmp_scalar_acc.
Hypothesis Hb_indep : SEM.exp_independent_of_acc b OSE.tmp_scalar_acc.
Variables (output : DE.acc (ary '{batch} (ary '{outnum} num))).
Hypothesis Hinput_out : SEM.exp_independent_of_acc input output.
Hypothesis Hw_out : SEM.exp_independent_of_acc w output.
Hypothesis Hb_out : SEM.exp_independent_of_acc b output.

Lemma linear2d_cell_indep_out_single : forall (bi : fin batch) (out : fin outnum),
  SEM.exp_independent_of_acc
    (CD.add (CD.sum (DE.mkvSeq (fun i : fin m =>
      CD.mul input|[bi]|[i] w|[out]|[i]))) b|[out])
    output.
Proof.
  intros bi out.
  apply SEM.exp_independent_of_acc_add.
  - apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply SEM.exp_independent_of_acc_mul.
    + apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_out.
    + apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hw_out.
  - apply SEM.exp_independent_of_acc_idx. exact Hb_out.
Qed.

Theorem Linear2d_sem_single : forall (rho : PCG.env),
  OSE.tmp_disjoint_from_output2d batch outnum output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Linear2d batch m outnum w b input)) rho =
  SEM.eval (@CEO.Linear2d_comm batch m outnum w b input output) rho.
Proof.
  intros rho Hdisj Hundef.
  unfold CG.A, COP.Linear2d, CEO.Linear2d_comm.
  set (row := fun bi : fin batch => DE.mkvSeq (fun out : fin outnum =>
    CD.add (CD.sum (DE.mkvSeq (fun i : fin m => CD.mul input|[bi]|[i] w|[out]|[i]))) b|[out])).
  assert (Hrow_indep : forall bi, SEM.exp_independent_of_acc (row bi) output).
  { intros bi. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros out.
    apply linear2d_cell_indep_out_single. }
  rewrite SEM.eval_mkvSeq; [ | intros bi; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros bi eta HPeta. split.
  - (* Row-level equivalence. *)
    assert (Hcell_indep_bi : forall out,
      SEM.exp_independent_of_acc
        (CD.add (CD.sum (DE.mkvSeq (fun i : fin m => CD.mul input|[bi]|[i] w|[out]|[i]))) b|[out])
        (output |{ bi})).
    { intros out. unfold SEM.exp_independent_of_acc. intros p Hp.
      apply (linear2d_cell_indep_out_single bi out).
      simpl in Hp. destruct Hp as [out' Hout'].
      simpl. exists bi. exists out'. exact Hout'. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros out; apply Hcell_indep_bi ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros out eta' HPeta'. split.
    + set (e := DE.mkvSeq (fun i : fin m => CD.mul input|[bi]|[i] w|[out]|[i])).
      set (c := fun r : DE.exp num => (output|{bi}|{out}) |:= CD.add r b|[out]).
      assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (CD.mul input|[bi]|[i] w|[out]|[i]) (CG.vrd tmp)) ';
          (output|{bi}|{out}) |:= CD.add (CG.vrd tmp) b|[out]))
        = (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp)) ';
          (output|{bi}|{out}) |:= CD.add (CG.vrd tmp) b|[out]))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (CD.mul input|[bi]|[i] w|[out]|[i]) (CG.vrd tmp))
                    = CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))).
        { apply FTac.seqfor_extensionality; intro i.
          assert (Heq : CD.mul input|[bi]|[i] w|[out]|[i] = DE.idx e i).
          { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      rewrite SEM.eval_assign.
      rewrite <- (SEM.eval_assign_aux 1 num _ _ eta').
      change (SEM.eval_aux (c (CD.sum e)) 1 eta' =
        SEM.eval (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))
          '; c (CG.vrd tmp))) eta').
      apply (@SEM.eval_csum_equiv m e c eta').
      * exact HPeta'.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro i.
        apply SEM.exp_independent_of_acc_mul.
        -- apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_indep.
        -- apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hw_indep.
      * apply OSE.Linear2d_cell_continuation_ok; assumption.
    + rewrite SEM.eval_assign.
      apply OSE.assign_preserves_StructUndefined_tmp.
      * intros p Hp Hout. apply (Hdisj p bi out Hp). exact Hout.
      * exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros out rho'. apply PCG.assign_not_in_acc.
      intros Hc. apply (Hdisj OSE.tmp_path bi out OSE.in_acc_tmp_scalar_acc). exact Hc.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

End Linear2d_Single.

(* -------------------------------------------------------------------------- *)
(* Softmax2d: single-output semantic equivalence                              *)
(*                                                                            *)
(*   Replay of [Operators_Sem_Equiv.Softmax2d_sem] with the concrete output   *)
(*   acceptor.                                                                *)
(* -------------------------------------------------------------------------- *)

Section Softmax2d_Single.

Variables (batch m : nat) (input : DE.exp (ary '{batch} (ary '{m} num))).
Hypothesis Hbatch : batch > 0.
Hypothesis Hm : m > 0.
Hypothesis Hinput_indep : SEM.exp_independent_of_acc input OSE.tmp_scalar_acc.
Variables (output : DE.acc (ary '{batch} (ary '{m} num))).
Hypothesis Hinput_out : SEM.exp_independent_of_acc input output.

Lemma softmax2d_batch_continuation_ok_single : forall (b : fin batch),
  (forall p j, @PCG.in_acc num p OSE.tmp_scalar_acc -> (output |{ b} |{ j}) <> p) ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => CG.seqfor (fun j : fin m =>
      output|{b}|{j} |:= CD.div (CD.pExp input|[b]|[j]) r))
    (CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i]))).
Proof.
  intros b Hdisj_row.
  set (e_final := CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i]))).
  set (g := fun (j : fin m) (r : DE.exp num) => CD.div (CD.pExp input|[b]|[j]) r).
  assert (Hdisj_acc : OSE.tmp_disjoint_from_acc (output |{ b})).
  { intros p Hp Hout. unfold PCG.in_acc in Hout. simpl in Hout.
    destruct Hout as [j Hj]. simpl in Hj. assert (Hc := Hdisj_row p j Hp Hj). contradiction. }
  assert (Hinput_row : SEM.exp_independent_of_acc input (output |{ b})).
  { intros p Hp. apply Hinput_out. unfold PCG.in_acc in Hp |- *. simpl in Hp |- *.
    exists b. destruct Hp as [j Hj]. exists j. exact Hj. }
  apply OSE.seqfor_scalar_assign_continuation_ok.
  - exact Hdisj_acc.
  - unfold e_final. apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_indep.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_indep.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_indep.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
  - intros j. unfold g. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
    + apply OSE.exp_independent_of_acc_REvar.
      intro Hc. apply (Hdisj_acc (DE.Var "__tmp") OSE.in_acc_tmp_scalar_acc Hc).
  - intros j rho eta v Hv Heta.
    rewrite !OSE.to_pcg_exp_div; f_equal.
    + rewrite !OSE.to_pcg_exp_pExp; f_equal.
      apply SEM.exp_independent_of_acc_eval with (a := OSE.tmp_scalar_acc).
      * apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_indep.
      * intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
        apply Heta. intro Hc. apply Hq. simpl. auto.
    + unfold CG.vrd. simpl. rewrite SEM.to_pcg_exp_REvar.
      rewrite PCG.update_eq by reflexivity. symmetry. exact Hv.
Qed.

Theorem Softmax2d_sem_single : forall (rho : PCG.env),
  OSE.tmp_disjoint_from_output2d batch m output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Softmax2d batch m input)) rho =
  SEM.eval (@CEO.Softmax2d_comm batch m input output) rho.
Proof.
  intros rho Hdisj Hundef.
  unfold CG.A, COP.Softmax2d, CEO.Softmax2d_comm, CD.let_binding.
  set (s := DE.mkvSeq (fun b : fin batch =>
    CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i])))).
  set (row := fun b : fin batch => DE.mkvSeq (fun j : fin m =>
    CD.div (CD.pExp input|[b]|[j]) (s|[b]))).
  assert (Hs_indep : SEM.exp_independent_of_acc s output).
  { unfold s. apply SEM.exp_independent_of_acc_mkvSeq. intro b'.
    apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx. exact Hinput_out. }
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros j.
    apply SEM.exp_independent_of_acc_div.
    - apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx. exact Hinput_out.
    - apply SEM.exp_independent_of_acc_idx. exact Hs_indep. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - assert (Hinput_row : SEM.exp_independent_of_acc input (output |{ b})).
    { intros p Hp. apply Hinput_out. unfold PCG.in_acc in Hp |- *. simpl in Hp |- *.
      exists b. destruct Hp as [j Hj]. exists j. exact Hj. }
    assert (Hs_row : SEM.exp_independent_of_acc s (output |{ b})).
    { unfold s. apply SEM.exp_independent_of_acc_mkvSeq. intro b'.
      apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx.
      exact Hinput_row. }
    assert (Hcell_indep_b : forall j,
      SEM.exp_independent_of_acc (CD.div (CD.pExp input|[b]|[j]) (s|[b])) (output |{ b})).
    { intros j.
      apply (OSE.Softmax2d_cell_independent_of_output (d' := ary '{ m} num) (a := output |{ b}));
        [ exact Hinput_row | apply SEM.exp_independent_of_acc_idx; exact Hs_row ]. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros j; apply Hcell_indep_b ].
    apply eq_trans with (y := SEM.eval_aux (CG.seqfor (fun j : fin m =>
      (output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (s|[b]))) 1 eta).
    + rewrite SEM.eval_seqfor.
      assert (Hpoint : forall j,
        SEM.eval ((output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (s|[b])) =
        SEM.eval_aux ((output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (s|[b])) 1).
      { intro j. apply functional_extensionality; intro rho''.
        rewrite SEM.eval_assign. symmetry. apply SEM.eval_assign_aux. }
      replace (PCG.seqfor (fun j : fin m =>
        SEM.eval ((output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (s|[b]))) eta)
        with (PCG.seqfor (fun j : fin m =>
          SEM.eval_aux ((output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (s|[b])) 1) eta).
      2: { apply f_equal with (f := fun h => PCG.seqfor h eta).
           apply functional_extensionality; intro j. symmetry. apply Hpoint. }
      rewrite SEM.eval_seqfor_aux. reflexivity.
    + set (e := DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i])).
      assert (Heq : s|[b] = CD.sum e).
      { unfold e, s, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
      rewrite Heq.
      set (c := fun r : DE.exp num => CG.seqfor (fun j : fin m =>
        (output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) r)).
      assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (CD.pExp input|[b]|[i]) (CG.vrd tmp)) ';
          CG.seqfor (fun j : fin m =>
            (output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (CG.vrd tmp))))
        = (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
            CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp)) ';
          CG.seqfor (fun j : fin m =>
            (output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (CG.vrd tmp))))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (CD.pExp input|[b]|[i]) (CG.vrd tmp))
                    = CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))).
        { apply FTac.seqfor_extensionality; intro i.
          assert (Heq_i : CD.pExp input|[b]|[i] = DE.idx e i).
          { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq_i. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      apply (@SEM.eval_csum_equiv m e c eta).
      * exact HPeta.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro i.
        apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx. exact Hinput_indep.
      * apply softmax2d_batch_continuation_ok_single.
        intros p j' Hp Hc. apply (Hdisj p b j' Hp). simpl. rewrite Hc. simpl. reflexivity.
  - rewrite SEM.eval_assign.
    assert (Hpres : PCG.assign (output|{b}) (SEM.to_pcg_exp (row b) eta) eta OSE.tmp_path = eta OSE.tmp_path).
    { unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j rho'.
      apply PCG.assign_not_in_acc.
      intros Hc. apply (Hdisj OSE.tmp_path b j OSE.in_acc_tmp_scalar_acc). exact Hc. }
    apply PCG.StructUndefined_num. apply eq_trans with (y := eta OSE.tmp_path).
    + exact Hpres.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

End Softmax2d_Single.

(* -------------------------------------------------------------------------- *)
(* Classifier interpretation lemmas (route-B model -> route-A functional)     *)
(* -------------------------------------------------------------------------- *)

Lemma interp_Linear2d : forall (batch m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Linear2d w b input) rho =
  OP.Linear2d (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp b rho)
    (SEM.to_pcg_exp input rho).
Proof.
  intros batch m outnum w b input rho.
  unfold COP.Linear2d, OP.Linear2d.
  apply BRC.to_pcg_mkvSeq_ext; intro bb.
  apply BRC.to_pcg_mkvSeq_ext; intro out.
  rewrite SEM.to_pcg_exp_add, SEM.to_pcg_exp_idx, BRC.to_pcg_sum_mkvSeq.
  apply f_equal2; [ | reflexivity ].
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_mul.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Lemma interp_Softmax2d : forall (batch m : nat) (Hb : batch > 0)
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (rho : PCG.env),
  SEM.to_pcg_exp (COP.Softmax2d input) rho =
  OR.Softmax2d (SEM.to_pcg_exp input rho).
Proof.
  intros batch m Hb input rho.
  unfold COP.Softmax2d, OR.Softmax2d.
  cbv [CD.let_binding PCG.let_binding]. cbv beta.
  apply BRC.to_pcg_mkvSeq_ext; intro b.
  apply BRC.to_pcg_mkvSeq_ext; intro j.
  rewrite OSE.to_pcg_exp_div, OSE.to_pcg_exp_pExp.
  apply f_equal2.
  - repeat rewrite SEM.to_pcg_exp_idx. reflexivity.
  - rewrite SEM.to_pcg_exp_idx, SEM.to_pcg_exp_mkvSeq.
    rewrite (PCG.idx_mkvSeq _ _ _ Hb).
    rewrite BRC.to_pcg_sum_mkvSeq.
    apply f_equal. apply V.mk_vec_ext; intro i.
    rewrite OSE.to_pcg_exp_pExp. repeat rewrite SEM.to_pcg_exp_idx. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Canonical conv variants at the concrete ResNet18 sizes                     *)
(*                                                                            *)
(*   [Ops_Conv.Conv4d 1 1] (stride 1) differs from the route-A canonical      *)
(*   [ResNet18_DPIA.Conv4d_3x3_s1] only by [fin2nat i0 * 1] vs [fin2nat i0].  *)
(*   (The stride-2 3x3/1x1 and the 7x7 stem instances are convertible.)       *)
(* -------------------------------------------------------------------------- *)

Lemma conv4d_s1_eq_56 : forall (batch inch outch : nat)
  (bias : PCG.exp (ary '{outch} num))
  (w : PCG.exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : PCG.exp (ary '{batch} (ary '{inch} (ary '{56} (ary '{56} num))))),
  @OC.Conv4d batch 56 56 3 3 inch outch 1 1 bias w input =
  @RD.Conv4d_3x3_s1 batch inch outch 56 56 bias w input.
Proof.
  intros. unfold OC.Conv4d, OC.Conv4dCell, RD.Conv4d_3x3_s1.
  cbv beta. rewrite ?Nat.mul_1_r. reflexivity.
Qed.

Lemma conv4d_s1_eq_28 : forall (batch inch outch : nat)
  (bias : PCG.exp (ary '{outch} num))
  (w : PCG.exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : PCG.exp (ary '{batch} (ary '{inch} (ary '{28} (ary '{28} num))))),
  @OC.Conv4d batch 28 28 3 3 inch outch 1 1 bias w input =
  @RD.Conv4d_3x3_s1 batch inch outch 28 28 bias w input.
Proof.
  intros. unfold OC.Conv4d, OC.Conv4dCell, RD.Conv4d_3x3_s1.
  cbv beta. rewrite ?Nat.mul_1_r. reflexivity.
Qed.

Lemma conv4d_s1_eq_14 : forall (batch inch outch : nat)
  (bias : PCG.exp (ary '{outch} num))
  (w : PCG.exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : PCG.exp (ary '{batch} (ary '{inch} (ary '{14} (ary '{14} num))))),
  @OC.Conv4d batch 14 14 3 3 inch outch 1 1 bias w input =
  @RD.Conv4d_3x3_s1 batch inch outch 14 14 bias w input.
Proof.
  intros. unfold OC.Conv4d, OC.Conv4dCell, RD.Conv4d_3x3_s1.
  cbv beta. rewrite ?Nat.mul_1_r. reflexivity.
Qed.

Lemma conv4d_s1_eq_7 : forall (batch inch outch : nat)
  (bias : PCG.exp (ary '{outch} num))
  (w : PCG.exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : PCG.exp (ary '{batch} (ary '{inch} (ary '{7} (ary '{7} num))))),
  @OC.Conv4d batch 7 7 3 3 inch outch 1 1 bias w input =
  @RD.Conv4d_3x3_s1 batch inch outch 7 7 bias w input.
Proof.
  intros. unfold OC.Conv4d, OC.Conv4dCell, RD.Conv4d_3x3_s1.
  cbv beta. rewrite ?Nat.mul_1_r. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic per-layer buffer bridges                                           *)
(*                                                                            *)
(*   Each [HB_*] lemma collapses one route-B AST layer command over named     *)
(*   buffers to a single [PCG.assign] of the route-A functional operator.     *)
(* -------------------------------------------------------------------------- *)

Lemma HB_conv4d : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hs : s > 0) (Hb : batch > 0) (Hc : channel > 0) (Hf : filernum > 0)
  (Hn1 : n1 > 0) (Hn2 : n2 > 0) (Hk1 : n1 <= m1) (Hk2 : n2 <= m2)
  (sb sw si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sw ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sb ++ "[" ++ u <> "__tmp")%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sw ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sb ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BR2.Conv4d_ast_comm batch m1 m2 n1 n2 channel filernum p s
      (@CG.vrd (ary '{filernum} num) sb)
      (@CG.vrd (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))) sw)
      (@CG.vrd (T4 batch channel m1 m2) si)
      (@CG.vwt (ary '{batch} (ary '{filernum}
        (ary '{((m1 - n1 + 2 * p) / s + 1)}
        (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so)) eta =
  PCG.assign (@CG.vwt (ary '{batch} (ary '{filernum}
        (ary '{((m1 - n1 + 2 * p) / s + 1)}
        (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so)
    (@OC.Conv4d batch m1 m2 n1 n2 channel filernum p s
       (SEM.to_pcg_exp (@CG.vrd (ary '{filernum} num) sb) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{filernum}
         (ary '{channel} (ary '{n1} (ary '{n2} num)))) sw) eta)
       (SEM.to_pcg_exp (@CG.vrd (T4 batch channel m1 m2) si) eta)) eta.
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s Hs Hb Hc Hf Hn1 Hn2 Hk1 Hk2
    sb sw si so eta Hti Htw Htb Hio0 Hwo0 Hbo0 Htmpn Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd (T4 batch channel m1 m2) si)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Hti).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd (ary '{filernum}
    (ary '{channel} (ary '{n1} (ary '{n2} num)))) sw)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Htw).
  assert (Hbias : SEM.exp_independent_of_acc (@CG.vrd (ary '{filernum} num) sb)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Htb).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd (T4 batch channel m1 m2) si)
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - n1 + 2 * p) / s + 1)}
      (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hio0).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd (ary '{filernum}
    (ary '{channel} (ary '{n1} (ary '{n2} num)))) sw)
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - n1 + 2 * p) / s + 1)}
      (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hwo0).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd (ary '{filernum} num) sb)
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - n1 + 2 * p) / s + 1)}
      (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hbo0).
  assert (Hdisj : BR2.tmp_disjoint_from_output_conv4d batch m1 m2 n1 n2
    filernum p s
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - n1 + 2 * p) / s + 1)}
      (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so))
    by (exact (tmp_disj_vwt4 _ _ _ _ _ Htmpn)).
  rewrite <- (Conv4d_sem_single batch m1 m2 n1 n2 channel filernum p s
    (@CG.vrd (ary '{filernum} num) sb)
    (@CG.vrd (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))) sw)
    (@CG.vrd (T4 batch channel m1 m2) si)
    Hs Hb Hc Hf Hn1 Hn2 Hi Hw Hbias
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - n1 + 2 * p) / s + 1)}
      (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so)
    Hio Hwo Hbo eta Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal.
  apply BR2.interp_Conv4d; assumption.
Qed.

Lemma HB_bn : forall (channel m1 m2 : nat) (Hc : channel > 0)
  (si sg sb se so : string)
  (mean var : DE.exp (ary '{channel} num)) (eta : PCG.env),
  mean = BR2.bn1_mean (@CG.vrd (T4 1 channel m1 m2) si) ->
  var = BR2.bn1_var (@CG.vrd (T4 1 channel m1 m2) si) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sg ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sb ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall w u : string, (se ++ w <> so ++ "[" ++ u)%string) ->
  SEM.eval (@CEB.BatchNorm4d_comm 1 channel m1 m2
      (@CG.vrd (T4 1 channel m1 m2) si) mean var
      (@CG.vrd (ary '{channel} num) sg)
      (@CG.vrd (ary '{channel} num) sb)
      (@CG.vrd num se)
      (@CG.vwt (T4 1 channel m1 m2) so)) eta =
  PCG.assign (@CG.vwt (T4 1 channel m1 m2) so)
    (@OB.BatchNorm4d 1 channel m1 m2
       (SEM.to_pcg_exp (@CG.vrd (T4 1 channel m1 m2) si) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{channel} num) sg) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{channel} num) sb) eta)
       (SEM.to_pcg_exp (@CG.vrd num se) eta)) eta.
Proof.
  intros channel m1 m2 Hc si sg sb se so mean var eta Hm Hv Hio0 Hgo0 Hbo0 Heo0.
  subst mean. subst var.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd (T4 1 channel m1 m2) si)
    (@CG.vwt (T4 1 channel m1 m2) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hio0).
  assert (Hg : SEM.exp_independent_of_acc (@CG.vrd (ary '{channel} num) sg)
    (@CG.vwt (T4 1 channel m1 m2) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hgo0).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd (ary '{channel} num) sb)
    (@CG.vwt (T4 1 channel m1 m2) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hbo0).
  assert (He : SEM.exp_independent_of_acc (@CG.vrd num se)
    (@CG.vwt (T4 1 channel m1 m2) so)).
  { intros p Hp. destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply SEM.exp_indep_vrd_Var. intros w Hw.
    exact (Heo0 w u Hw). }
  rewrite <- (CEB.BatchNorm4d_equiv_sem eta Hi
    (BR2.bn1_mean_independent _ _ _ _ _ Hi)
    (BR2.bn1_var_independent _ _ _ _ _ Hi) Hg Hb He).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal.
  apply BR2.interp_BatchNorm4d. exact Hc.
Qed.

Lemma HB_relu : forall (batch channel m1 m2 : nat)
  (si so : string) (eta : PCG.env),
  (si <> "0")%string -> (si <> "1")%string ->
  (forall u v : string, (so ++ "[" ++ u <> si ++ "[" ++ v)%string) ->
  (forall (b : fin batch) (c : fin channel) (i0 : fin m1) (i1 : fin m2),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx
        (SEM.to_pcg_exp (@CG.vrd (T4 batch channel m1 m2) si) eta) b) c) i0) i1
       <= R0)%R) ->
  SEM.eval (@CEO.ReLU4d_comm batch channel m1 m2
      (@CG.vrd (T4 batch channel m1 m2) si)
      (@CG.vwt (T4 batch channel m1 m2) so)) eta =
  PCG.assign (@CG.vwt (T4 batch channel m1 m2) so)
    (@OE.ReLU4d batch channel m1 m2
       (SEM.to_pcg_exp (@CG.vrd (T4 batch channel m1 m2) si) eta)) eta.
Proof.
  intros batch channel m1 m2 si so eta Hs0 Hs1 Hnames Hle.
  assert (Hb : forall (b : fin batch) (c : fin channel) (i0 : fin m1) (i1 : fin m2),
    DE.eval_bexp (BE.env_val eta)
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (T4 batch channel m1 m2) si) b) c) i0) i1) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (T4 batch channel m1 m2) si) b) c) i0) i1) CD.zero)).
  { intros b c i0 i1.
    rewrite (BE.to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (T4 batch channel m1 m2) si) b) c) i0) i1) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (DE.idx (DE.idx (DE.idx
          (@CG.vrd (T4 batch channel m1 m2) si) b) c) i0) i1) PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (BE.env_val PCG.env_empty) by reflexivity.
      apply BE.to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (BL.to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite !BL.PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle b c i0 i1).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (T4 batch channel m1 m2) si) (@CG.vwt (T4 batch channel m1 m2) so)).
  { intros p Hp. destruct (BL.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply BL.exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEO.ReLU4d_equiv_sem eta Hindep Hb).
  cbv [CG.A]. rewrite SEM.eval_assign.
  f_equal. apply BE.interp_ReLU4d. exact Hb.
Qed.

Lemma HB_add : forall (batch channel m1 m2 : nat)
  (sx sy so : string) (eta : PCG.env),
  (forall u v : string, (sx ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sy ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  SEM.eval (@CEB.Add4d_comm batch channel m1 m2
      (@CG.vrd (T4 batch channel m1 m2) sx)
      (@CG.vrd (T4 batch channel m1 m2) sy)
      (@CG.vwt (T4 batch channel m1 m2) so)) eta =
  PCG.assign (@CG.vwt (T4 batch channel m1 m2) so)
    (@OE.Add4d batch channel m1 m2
       (SEM.to_pcg_exp (@CG.vrd (T4 batch channel m1 m2) sx) eta)
       (SEM.to_pcg_exp (@CG.vrd (T4 batch channel m1 m2) sy) eta)) eta.
Proof.
  intros batch channel m1 m2 sx sy so eta Hx0 Hy0.
  assert (Hx : SEM.exp_independent_of_acc (@CG.vrd (T4 batch channel m1 m2) sx)
    (@CG.vwt (T4 batch channel m1 m2) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hx0).
  assert (Hy : SEM.exp_independent_of_acc (@CG.vrd (T4 batch channel m1 m2) sy)
    (@CG.vwt (T4 batch channel m1 m2) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hy0).
  rewrite <- (CEB.Add4d_equiv_sem eta Hx Hy).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal. apply BE.interp_Add4d.
Qed.

Lemma HB_maxp : forall (batch filernum m1 m2 kersize stride padding : nat)
  (Hb : batch > 0) (Hf : filernum > 0) (Hk : kersize > 0) (Hs : stride > 0)
  (Hk1 : kersize <= m1) (Hk2 : kersize <= m2)
  (si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BR2.Maxpool4d_pad_ast_comm batch filernum m1 m2 kersize stride
      padding
      (@CG.vrd (T4 batch filernum m1 m2) si)
      (@CG.vwt (ary '{batch} (ary '{filernum}
        (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
        (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))) so)) eta =
  PCG.assign (@CG.vwt (ary '{batch} (ary '{filernum}
        (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
        (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))) so)
    (@AD.Maxpool4d_pad batch filernum m1 m2 kersize stride padding
       (SEM.to_pcg_exp (@CG.vrd (T4 batch filernum m1 m2) si) eta)) eta.
Proof.
  intros batch filernum m1 m2 kersize stride padding Hb Hf Hk Hs Hk1 Hk2
    si so eta Hti Hio0 Htmpn Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd (T4 batch filernum m1 m2) si)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Hti).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd (T4 batch filernum m1 m2) si)
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
      (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hio0).
  assert (Hdisj : BR2.tmp_disjoint_from_output_maxp4dp batch filernum m1 m2
    kersize stride padding
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
      (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))) so))
    by (exact (tmp_disj_vwt4 _ _ _ _ _ Htmpn)).
  rewrite <- (Maxpool4d_pad_sem_single batch filernum m1 m2 kersize stride
    padding (@CG.vrd (T4 batch filernum m1 m2) si)
    Hs Hb Hf Hk Hi
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
      (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num)))) so)
    Hio eta Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal.
  apply BR2.interp_Maxpool4d_pad; assumption.
Qed.

Lemma HB_gap : forall (batch channel m1 m2 : nat)
  (Hb : batch > 0) (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.GlobalAvgPool4d_comm batch channel m1 m2
      (@CG.vrd (T4 batch channel m1 m2) si)
      (@CG.vwt (ary '{batch} (ary '{channel} num)) so)) eta =
  PCG.assign (@CG.vwt (ary '{batch} (ary '{channel} num)) so)
    (@OR.GlobalAvgPool4d batch channel m1 m2
       (SEM.to_pcg_exp (@CG.vrd (T4 batch channel m1 m2) si) eta)) eta.
Proof.
  intros batch channel m1 m2 Hb Hc Hm1 Hm2 si so eta Hti Hio0 Htmpn Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd (T4 batch channel m1 m2) si)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Hti).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd (T4 batch channel m1 m2) si)
    (@CG.vwt (ary '{batch} (ary '{channel} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hio0).
  assert (Hdisj : OSE.tmp_disjoint_from_output_gap batch channel
    (@CG.vwt (ary '{batch} (ary '{channel} num)) so))
    by (exact (tmp_disj_vwt2 _ _ _ Htmpn)).
  rewrite <- (GlobalAvgPool4d_sem_single batch channel m1 m2
    (@CG.vrd (T4 batch channel m1 m2) si)
    Hb Hc Hm1 Hm2 Hi
    (@CG.vwt (ary '{batch} (ary '{channel} num)) so)
    Hio eta Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal.
  apply BR2.interp_GlobalAvgPool4d.
Qed.

Lemma HB_linear : forall (batch m outnum : nat)
  (Hb : batch > 0) (Hm : m > 0) (Ho : outnum > 0)
  (sw sb si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sw ++ "[" ++ u <> "__tmp")%string) ->
  (forall u : string, (sb ++ "[" ++ u <> "__tmp")%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sw ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u v : string, (sb ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear2d_comm batch m outnum
      (@CG.vrd (ary '{outnum} (ary '{m} num)) sw)
      (@CG.vrd (ary '{outnum} num) sb)
      (@CG.vrd (ary '{batch} (ary '{m} num)) si)
      (@CG.vwt (ary '{batch} (ary '{outnum} num)) so)) eta =
  PCG.assign (@CG.vwt (ary '{batch} (ary '{outnum} num)) so)
    (@OP.Linear2d batch m outnum
       (SEM.to_pcg_exp (@CG.vrd (ary '{outnum} (ary '{m} num)) sw) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{outnum} num) sb) eta)
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{m} num)) si) eta)) eta.
Proof.
  intros batch m outnum Hb Hm Ho sw sb si so eta Hti Htw Htb Hio0 Hwo0 Hbo0
    Htmpn Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Hti).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd (ary '{outnum} (ary '{m} num)) sw)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Htw).
  assert (Hbias : SEM.exp_independent_of_acc (@CG.vrd (ary '{outnum} num) sb)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Htb).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hio0).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd (ary '{outnum} (ary '{m} num)) sw)
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hwo0).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd (ary '{outnum} num) sb)
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hbo0).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d batch outnum
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so))
    by (exact (tmp_disj_vwt2 _ _ _ Htmpn)).
  rewrite <- (Linear2d_sem_single batch m outnum
    (@CG.vrd (ary '{outnum} (ary '{m} num)) sw)
    (@CG.vrd (ary '{outnum} num) sb)
    (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    Hi Hw Hbias
    (@CG.vwt (ary '{batch} (ary '{outnum} num)) so)
    Hio Hwo Hbo eta Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal.
  apply interp_Linear2d.
Qed.

Lemma HB_softmax : forall (batch m : nat)
  (Hb : batch > 0) (Hm : m > 0)
  (si so : string) (eta : PCG.env),
  (forall u : string, (si ++ "[" ++ u <> "__tmp")%string) ->
  (forall u v : string, (si ++ "[" ++ u <> so ++ "[" ++ v)%string) ->
  (forall u : string, ("__tmp" <> so ++ "[" ++ u)%string) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Softmax2d_comm batch m
      (@CG.vrd (ary '{batch} (ary '{m} num)) si)
      (@CG.vwt (ary '{batch} (ary '{m} num)) so)) eta =
  PCG.assign (@CG.vwt (ary '{batch} (ary '{m} num)) so)
    (@OR.Softmax2d batch m
       (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{m} num)) si) eta)) eta.
Proof.
  intros batch m Hb Hm si so eta Hti Hio0 Htmpn Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    OSE.tmp_scalar_acc) by (apply BL.vrd_ary_indep_tmp; exact Hti).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    (@CG.vwt (ary '{batch} (ary '{m} num)) so))
    by (apply BL.vrd_ary_indep_vwt_ary; exact Hio0).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d batch m
    (@CG.vwt (ary '{batch} (ary '{m} num)) so))
    by (exact (tmp_disj_vwt2 _ _ _ Htmpn)).
  rewrite <- (Softmax2d_sem_single batch m
    (@CG.vrd (ary '{batch} (ary '{m} num)) si)
    Hi
    (@CG.vwt (ary '{batch} (ary '{m} num)) so)
    Hio eta Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign. f_equal.
  apply interp_Softmax2d. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* The whole-network route-B AST                                              *)
(*                                                                            *)
(*   Buffer names follow [CNN_Examples_ResNet18]; every BatchNorm's mean/var  *)
(*   inputs are instantiated with [BR2.bn1_mean]/[BR2.bn1_var] of the         *)
(*   preceding convolution buffer (the batch=1 alignment, see the header      *)
(*   note of [Bridge_ReduceConv2]).  Each block's post-add ReLU writes a      *)
(*   fresh buffer ("lX_bY_out").                                              *)
(* -------------------------------------------------------------------------- *)

Definition ast_conv (batch m1 m2 n1 n2 channel filernum p s : nat)
  (sb sw si so : string) : CG.comm :=
  @BR2.Conv4d_ast_comm batch m1 m2 n1 n2 channel filernum p s
    (@CG.vrd (ary '{filernum} num) sb)
    (@CG.vrd (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))) sw)
    (@CG.vrd (T4 batch channel m1 m2) si)
    (@CG.vwt (ary '{batch} (ary '{filernum}
      (ary '{((m1 - n1 + 2 * p) / s + 1)}
      (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) so).

Definition ast_bn (channel m1 m2 : nat) (si sg sb so : string) : CG.comm :=
  @CEB.BatchNorm4d_comm 1 channel m1 m2
    (@CG.vrd (T4 1 channel m1 m2) si)
    (BR2.bn1_mean (@CG.vrd (T4 1 channel m1 m2) si))
    (BR2.bn1_var (@CG.vrd (T4 1 channel m1 m2) si))
    (@CG.vrd (ary '{channel} num) sg)
    (@CG.vrd (ary '{channel} num) sb)
    (@CG.vrd num "bn_eps")
    (@CG.vwt (T4 1 channel m1 m2) so).

Definition ast_relu (batch channel m1 m2 : nat) (si so : string) : CG.comm :=
  @CEO.ReLU4d_comm batch channel m1 m2
    (@CG.vrd (T4 batch channel m1 m2) si)
    (@CG.vwt (T4 batch channel m1 m2) so).

Definition ast_add (batch channel m1 m2 : nat) (sx sy so : string) : CG.comm :=
  @CEB.Add4d_comm batch channel m1 m2
    (@CG.vrd (T4 batch channel m1 m2) sx)
    (@CG.vrd (T4 batch channel m1 m2) sy)
    (@CG.vwt (T4 batch channel m1 m2) so).

(* Identity-shortcut basic block: conv-bn-relu-conv-bn-add-relu. *)
Definition bb_id_ast (c sz : nat) (sin : string)
  (w1 b1 g1 z1 w2 b2 g2 z2 : string)
  (c1 n1 r1 c2 n2 a2 o : string) : CG.comm :=
  CG.seq (ast_conv 1 sz sz 3 3 c c 1 1 b1 w1 sin c1,
  CG.seq (ast_bn c sz sz c1 g1 z1 n1,
  CG.seq (ast_relu 1 c sz sz n1 r1,
  CG.seq (ast_conv 1 sz sz 3 3 c c 1 1 b2 w2 r1 c2,
  CG.seq (ast_bn c sz sz c2 g2 z2 n2,
  CG.seq (ast_add 1 c sz sz n2 sin a2,
         ast_relu 1 c sz sz a2 o)))))).

(* Projection-shortcut basic block: (1x1s2 conv + bn on the shortcut first),
   then conv3x3s2-bn-relu-conv3x3s1-bn-add-relu. *)
Definition bb_proj_ast (inch outch sz : nat) (sin : string)
  (w1 b1 g1 z1 w2 b2 g2 z2 ws bs gs zs : string)
  (sc sn c1 n1 r1 c2 n2 a2 o : string) : CG.comm :=
  CG.seq (ast_conv 1 sz sz 1 1 inch outch 0 2 bs ws sin sc,
  CG.seq (ast_bn outch (RD.half sz) (RD.half sz) sc gs zs sn,
  CG.seq (ast_conv 1 sz sz 3 3 inch outch 1 2 b1 w1 sin c1,
  CG.seq (ast_bn outch (RD.half sz) (RD.half sz) c1 g1 z1 n1,
  CG.seq (ast_relu 1 outch (RD.half sz) (RD.half sz) n1 r1,
  CG.seq (ast_conv 1 (RD.half sz) (RD.half sz) 3 3 outch outch 1 1 b2 w2 r1 c2,
  CG.seq (ast_bn outch (RD.half sz) (RD.half sz) c2 g2 z2 n2,
  CG.seq (ast_add 1 outch (RD.half sz) (RD.half sz) n2 sn a2,
         ast_relu 1 outch (RD.half sz) (RD.half sz) a2 o)))))))).

Definition resnet18_AST : CG.comm :=
  CG.seq (ast_conv 1 224 224 7 7 3 64 3 2 "conv1_b" "conv1_w" "input" "conv1_out",
  CG.seq (ast_bn 64 112 112 "conv1_out" "bn1_gamma" "bn1_beta" "bn1_out",
  CG.seq (ast_relu 1 64 112 112 "bn1_out" "relu1_out",
  CG.seq (@BR2.Maxpool4d_pad_ast_comm 1 64 112 112 3 2 1
            (@CG.vrd (T4 1 64 112 112) "relu1_out")
            (@CG.vwt (ary '{1} (ary '{64} (ary '{56} (ary '{56} num)))) "pool_out"),
  CG.seq (bb_id_ast 64 56 "pool_out"
            "l1_b1_w1" "l1_b1_b1" "l1_b1_bn1_gamma" "l1_b1_bn1_beta"
            "l1_b1_w2" "l1_b1_b2" "l1_b1_bn2_gamma" "l1_b1_bn2_beta"
            "l1_b1_conv1_out" "l1_b1_bn1_out" "l1_b1_relu1_out"
            "l1_b1_conv2_out" "l1_b1_bn2_out" "l1_b1_add_out" "l1_b1_out",
  CG.seq (bb_id_ast 64 56 "l1_b1_out"
            "l1_b2_w1" "l1_b2_b1" "l1_b2_bn1_gamma" "l1_b2_bn1_beta"
            "l1_b2_w2" "l1_b2_b2" "l1_b2_bn2_gamma" "l1_b2_bn2_beta"
            "l1_b2_conv1_out" "l1_b2_bn1_out" "l1_b2_relu1_out"
            "l1_b2_conv2_out" "l1_b2_bn2_out" "l1_b2_add_out" "l1_b2_out",
  CG.seq (bb_proj_ast 64 128 56 "l1_b2_out"
            "l2_b1_w1" "l2_b1_b1" "l2_b1_bn1_gamma" "l2_b1_bn1_beta"
            "l2_b1_w2" "l2_b1_b2" "l2_b1_bn2_gamma" "l2_b1_bn2_beta"
            "l2_b1_shortcut_w" "l2_b1_shortcut_b"
            "l2_b1_shortcut_gamma" "l2_b1_shortcut_beta"
            "l2_b1_shortcut_out" "l2_b1_sbn_out"
            "l2_b1_conv1_out" "l2_b1_bn1_out" "l2_b1_relu1_out"
            "l2_b1_conv2_out" "l2_b1_bn2_out" "l2_b1_add_out" "l2_b1_out",
  CG.seq (bb_id_ast 128 28 "l2_b1_out"
            "l2_b2_w1" "l2_b2_b1" "l2_b2_bn1_gamma" "l2_b2_bn1_beta"
            "l2_b2_w2" "l2_b2_b2" "l2_b2_bn2_gamma" "l2_b2_bn2_beta"
            "l2_b2_conv1_out" "l2_b2_bn1_out" "l2_b2_relu1_out"
            "l2_b2_conv2_out" "l2_b2_bn2_out" "l2_b2_add_out" "l2_b2_out",
  CG.seq (bb_proj_ast 128 256 28 "l2_b2_out"
            "l3_b1_w1" "l3_b1_b1" "l3_b1_bn1_gamma" "l3_b1_bn1_beta"
            "l3_b1_w2" "l3_b1_b2" "l3_b1_bn2_gamma" "l3_b1_bn2_beta"
            "l3_b1_shortcut_w" "l3_b1_shortcut_b"
            "l3_b1_shortcut_gamma" "l3_b1_shortcut_beta"
            "l3_b1_shortcut_out" "l3_b1_sbn_out"
            "l3_b1_conv1_out" "l3_b1_bn1_out" "l3_b1_relu1_out"
            "l3_b1_conv2_out" "l3_b1_bn2_out" "l3_b1_add_out" "l3_b1_out",
  CG.seq (bb_id_ast 256 14 "l3_b1_out"
            "l3_b2_w1" "l3_b2_b1" "l3_b2_bn1_gamma" "l3_b2_bn1_beta"
            "l3_b2_w2" "l3_b2_b2" "l3_b2_bn2_gamma" "l3_b2_bn2_beta"
            "l3_b2_conv1_out" "l3_b2_bn1_out" "l3_b2_relu1_out"
            "l3_b2_conv2_out" "l3_b2_bn2_out" "l3_b2_add_out" "l3_b2_out",
  CG.seq (bb_proj_ast 256 512 14 "l3_b2_out"
            "l4_b1_w1" "l4_b1_b1" "l4_b1_bn1_gamma" "l4_b1_bn1_beta"
            "l4_b1_w2" "l4_b1_b2" "l4_b1_bn2_gamma" "l4_b1_bn2_beta"
            "l4_b1_shortcut_w" "l4_b1_shortcut_b"
            "l4_b1_shortcut_gamma" "l4_b1_shortcut_beta"
            "l4_b1_shortcut_out" "l4_b1_sbn_out"
            "l4_b1_conv1_out" "l4_b1_bn1_out" "l4_b1_relu1_out"
            "l4_b1_conv2_out" "l4_b1_bn2_out" "l4_b1_add_out" "l4_b1_out",
  CG.seq (bb_id_ast 512 7 "l4_b1_out"
            "l4_b2_w1" "l4_b2_b1" "l4_b2_bn1_gamma" "l4_b2_bn1_beta"
            "l4_b2_w2" "l4_b2_b2" "l4_b2_bn2_gamma" "l4_b2_bn2_beta"
            "l4_b2_conv1_out" "l4_b2_bn1_out" "l4_b2_relu1_out"
            "l4_b2_conv2_out" "l4_b2_bn2_out" "l4_b2_add_out" "l4_b2_out",
  CG.seq (@CEO.GlobalAvgPool4d_comm 1 512 7 7
            (@CG.vrd (T4 1 512 7 7) "l4_b2_out")
            (@CG.vwt (ary '{1} (ary '{512} num)) "avgpool_out"),
  CG.seq (@CEO.Linear2d_comm 1 512 1000
            (@CG.vrd (ary '{1000} (ary '{512} num)) "fc_w")
            (@CG.vrd (ary '{1000} num) "fc_b")
            (@CG.vrd (ary '{1} (ary '{512} num)) "avgpool_out")
            (@CG.vwt (ary '{1} (ary '{1000} num)) "fc_out"),
         @CEO.Softmax2d_comm 1 1000
            (@CG.vrd (ary '{1} (ary '{1000} num)) "fc_out")
            (@CG.vwt (ary '{1} (ary '{1000} num)) "output")
  )))))))))))))).

(* -------------------------------------------------------------------------- *)
(* Functional layer values (route A), as functions of the initial env         *)
(*                                                                            *)
(*   Only the values feeding the 17 ReLU layers (plus their chain             *)
(*   dependencies) are named; they are exactly the subterms of                *)
(*   [ResNet18_DPIA.ResNet18].                                                *)
(* -------------------------------------------------------------------------- *)

Section Functional_Chain.

Variable rho : PCG.env.

Definition eps_e : PCG.exp num := Rd num "bn_eps" rho.

(* Stem *)
Definition Gx1 : PCG.exp (T4 1 64 112 112) :=
  @OC.Conv4d_p3_k7_s2 1 3 64 224
    (Rd _ "input" rho) (Rd _ "conv1_w" rho) (Rd _ "conv1_b" rho).
Definition Gx2 : PCG.exp (T4 1 64 112 112) :=
  @OB.BatchNorm4d 1 64 112 112 Gx1
    (Rd _ "bn1_gamma" rho) (Rd _ "bn1_beta" rho) eps_e.
Definition Gx3 : PCG.exp (T4 1 64 112 112) := @OE.ReLU4d 1 64 112 112 Gx2.
Definition Gx4 : PCG.exp (T4 1 64 56 56) := @AD.Maxpool4d_pad 1 64 112 112 3 2 1 Gx3.

(* Stage 1, block 1 (identity, 64 @ 56) *)
Definition Gb11n1 : PCG.exp (T4 1 64 56 56) :=
  @OB.BatchNorm4d 1 64 56 56
    (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) Gx4)
    (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) eps_e.
Definition Gb11a2 : PCG.exp (T4 1 64 56 56) :=
  @OE.Add4d 1 64 56 56
    (@OB.BatchNorm4d 1 64 56 56
       (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho)
          (@OE.ReLU4d 1 64 56 56 Gb11n1))
       (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) eps_e)
    Gx4.
Definition Gb11 : PCG.exp (T4 1 64 56 56) := @OE.ReLU4d 1 64 56 56 Gb11a2.

(* Stage 1, block 2 (identity, 64 @ 56) *)
Definition Gb12n1 : PCG.exp (T4 1 64 56 56) :=
  @OB.BatchNorm4d 1 64 56 56
    (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) Gb11)
    (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) eps_e.
Definition Gb12a2 : PCG.exp (T4 1 64 56 56) :=
  @OE.Add4d 1 64 56 56
    (@OB.BatchNorm4d 1 64 56 56
       (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho)
          (@OE.ReLU4d 1 64 56 56 Gb12n1))
       (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) eps_e)
    Gb11.
Definition Gb12 : PCG.exp (T4 1 64 56 56) := @OE.ReLU4d 1 64 56 56 Gb12a2.

(* Stage 2, block 1 (projection 64 -> 128 @ 56) *)
Definition Gb21sn : PCG.exp (T4 1 128 28 28) :=
  @OB.BatchNorm4d 1 128 28 28
    (@RD.Conv4d_1x1_s2 1 64 128 56 56
       (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) Gb12)
    (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) eps_e.
Definition Gb21n1 : PCG.exp (T4 1 128 28 28) :=
  @OB.BatchNorm4d 1 128 28 28
    (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) Gb12)
    (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) eps_e.
Definition Gb21a2 : PCG.exp (T4 1 128 28 28) :=
  @OE.Add4d 1 128 28 28
    (@OB.BatchNorm4d 1 128 28 28
       (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho)
          (@OE.ReLU4d 1 128 28 28 Gb21n1))
       (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) eps_e)
    Gb21sn.
Definition Gb21 : PCG.exp (T4 1 128 28 28) := @OE.ReLU4d 1 128 28 28 Gb21a2.

(* Stage 2, block 2 (identity, 128 @ 28) *)
Definition Gb22n1 : PCG.exp (T4 1 128 28 28) :=
  @OB.BatchNorm4d 1 128 28 28
    (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) Gb21)
    (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) eps_e.
Definition Gb22a2 : PCG.exp (T4 1 128 28 28) :=
  @OE.Add4d 1 128 28 28
    (@OB.BatchNorm4d 1 128 28 28
       (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho)
          (@OE.ReLU4d 1 128 28 28 Gb22n1))
       (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) eps_e)
    Gb21.
Definition Gb22 : PCG.exp (T4 1 128 28 28) := @OE.ReLU4d 1 128 28 28 Gb22a2.

(* Stage 3, block 1 (projection 128 -> 256 @ 28) *)
Definition Gb31sn : PCG.exp (T4 1 256 14 14) :=
  @OB.BatchNorm4d 1 256 14 14
    (@RD.Conv4d_1x1_s2 1 128 256 28 28
       (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) Gb22)
    (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) eps_e.
Definition Gb31n1 : PCG.exp (T4 1 256 14 14) :=
  @OB.BatchNorm4d 1 256 14 14
    (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) Gb22)
    (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) eps_e.
Definition Gb31a2 : PCG.exp (T4 1 256 14 14) :=
  @OE.Add4d 1 256 14 14
    (@OB.BatchNorm4d 1 256 14 14
       (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho)
          (@OE.ReLU4d 1 256 14 14 Gb31n1))
       (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) eps_e)
    Gb31sn.
Definition Gb31 : PCG.exp (T4 1 256 14 14) := @OE.ReLU4d 1 256 14 14 Gb31a2.

(* Stage 3, block 2 (identity, 256 @ 14) *)
Definition Gb32n1 : PCG.exp (T4 1 256 14 14) :=
  @OB.BatchNorm4d 1 256 14 14
    (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) Gb31)
    (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) eps_e.
Definition Gb32a2 : PCG.exp (T4 1 256 14 14) :=
  @OE.Add4d 1 256 14 14
    (@OB.BatchNorm4d 1 256 14 14
       (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho)
          (@OE.ReLU4d 1 256 14 14 Gb32n1))
       (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) eps_e)
    Gb31.
Definition Gb32 : PCG.exp (T4 1 256 14 14) := @OE.ReLU4d 1 256 14 14 Gb32a2.

(* Stage 4, block 1 (projection 256 -> 512 @ 14) *)
Definition Gb41sn : PCG.exp (T4 1 512 7 7) :=
  @OB.BatchNorm4d 1 512 7 7
    (@RD.Conv4d_1x1_s2 1 256 512 14 14
       (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) Gb32)
    (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) eps_e.
Definition Gb41n1 : PCG.exp (T4 1 512 7 7) :=
  @OB.BatchNorm4d 1 512 7 7
    (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) Gb32)
    (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) eps_e.
Definition Gb41a2 : PCG.exp (T4 1 512 7 7) :=
  @OE.Add4d 1 512 7 7
    (@OB.BatchNorm4d 1 512 7 7
       (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho)
          (@OE.ReLU4d 1 512 7 7 Gb41n1))
       (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) eps_e)
    Gb41sn.
Definition Gb41 : PCG.exp (T4 1 512 7 7) := @OE.ReLU4d 1 512 7 7 Gb41a2.

(* Stage 4, block 2 (identity, 512 @ 7) *)
Definition Gb42n1 : PCG.exp (T4 1 512 7 7) :=
  @OB.BatchNorm4d 1 512 7 7
    (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) Gb41)
    (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) eps_e.
Definition Gb42a2 : PCG.exp (T4 1 512 7 7) :=
  @OE.Add4d 1 512 7 7
    (@OB.BatchNorm4d 1 512 7 7
       (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho)
          (@OE.ReLU4d 1 512 7 7 Gb42n1))
       (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) eps_e)
    Gb41.
Definition Gb42 : PCG.exp (T4 1 512 7 7) := @OE.ReLU4d 1 512 7 7 Gb42a2.

End Functional_Chain.

(* Freshness of the initial environment: the loopacc temporary and all of
   route A's accumulators (layer buffers l1..l13, block temporaries bt1..bt8)
   are undefined; the route-A freshness package also covers disjointness from
   the output buffer. *)
Definition net_fresh (rho : PCG.env) : Prop :=
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho /\
  RD.resnet18_fresh (m:=224) (@CG.vwt (ary '{1} (ary '{1000} num)) "output") rho.

(* -------------------------------------------------------------------------- *)
(* Wrapper bodies (A1): each functional layer value keeps its folded name;    *)
(* the bodies below are the ONLY sanctioned unfoldings.  [Gout] is the final  *)
(* route-B value (softmax of the classifier over [Gb42]).                     *)
(* -------------------------------------------------------------------------- *)

Lemma Gx1_body : forall rho, Gx1 rho =
  @OC.Conv4d_p3_k7_s2 1 3 64 224 (Rd _ "input" rho) (Rd _ "conv1_w" rho) (Rd _ "conv1_b" rho).
Proof. intros. reflexivity. Qed.
Lemma Gx2_body : forall rho, Gx2 rho =
  @OB.BatchNorm4d 1 64 112 112 (Gx1 rho) (Rd _ "bn1_gamma" rho) (Rd _ "bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gx3_body : forall rho, Gx3 rho = @OE.ReLU4d 1 64 112 112 (Gx2 rho).
Proof. intros. reflexivity. Qed.
Lemma Gx4_body : forall rho, Gx4 rho = @AD.Maxpool4d_pad 1 64 112 112 3 2 1 (Gx3 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb11n1_body : forall rho, Gb11n1 rho =
  @OB.BatchNorm4d 1 64 56 56
    (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) (Gx4 rho))
    (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb11a2_body : forall rho, Gb11a2 rho =
  @OE.Add4d 1 64 56 56
    (@OB.BatchNorm4d 1 64 56 56
       (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho)
          (@OE.ReLU4d 1 64 56 56 (Gb11n1 rho)))
       (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho))
    (Gx4 rho).
Proof. intros. reflexivity. Qed.
Lemma Gb11_body : forall rho, Gb11 rho = @OE.ReLU4d 1 64 56 56 (Gb11a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb12n1_body : forall rho, Gb12n1 rho =
  @OB.BatchNorm4d 1 64 56 56
    (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) (Gb11 rho))
    (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb12a2_body : forall rho, Gb12a2 rho =
  @OE.Add4d 1 64 56 56
    (@OB.BatchNorm4d 1 64 56 56
       (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho)
          (@OE.ReLU4d 1 64 56 56 (Gb12n1 rho)))
       (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho))
    (Gb11 rho).
Proof. intros. reflexivity. Qed.
Lemma Gb12_body : forall rho, Gb12 rho = @OE.ReLU4d 1 64 56 56 (Gb12a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb21sn_body : forall rho, Gb21sn rho =
  @OB.BatchNorm4d 1 128 28 28
    (@RD.Conv4d_1x1_s2 1 64 128 56 56
       (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) (Gb12 rho))
    (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb21n1_body : forall rho, Gb21n1 rho =
  @OB.BatchNorm4d 1 128 28 28
    (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) (Gb12 rho))
    (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb21a2_body : forall rho, Gb21a2 rho =
  @OE.Add4d 1 128 28 28
    (@OB.BatchNorm4d 1 128 28 28
       (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho)
          (@OE.ReLU4d 1 128 28 28 (Gb21n1 rho)))
       (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho))
    (Gb21sn rho).
Proof. intros. reflexivity. Qed.
Lemma Gb21_body : forall rho, Gb21 rho = @OE.ReLU4d 1 128 28 28 (Gb21a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb22n1_body : forall rho, Gb22n1 rho =
  @OB.BatchNorm4d 1 128 28 28
    (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) (Gb21 rho))
    (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb22a2_body : forall rho, Gb22a2 rho =
  @OE.Add4d 1 128 28 28
    (@OB.BatchNorm4d 1 128 28 28
       (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho)
          (@OE.ReLU4d 1 128 28 28 (Gb22n1 rho)))
       (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho))
    (Gb21 rho).
Proof. intros. reflexivity. Qed.
Lemma Gb22_body : forall rho, Gb22 rho = @OE.ReLU4d 1 128 28 28 (Gb22a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb31sn_body : forall rho, Gb31sn rho =
  @OB.BatchNorm4d 1 256 14 14
    (@RD.Conv4d_1x1_s2 1 128 256 28 28
       (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) (Gb22 rho))
    (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb31n1_body : forall rho, Gb31n1 rho =
  @OB.BatchNorm4d 1 256 14 14
    (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) (Gb22 rho))
    (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb31a2_body : forall rho, Gb31a2 rho =
  @OE.Add4d 1 256 14 14
    (@OB.BatchNorm4d 1 256 14 14
       (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho)
          (@OE.ReLU4d 1 256 14 14 (Gb31n1 rho)))
       (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho))
    (Gb31sn rho).
Proof. intros. reflexivity. Qed.
Lemma Gb31_body : forall rho, Gb31 rho = @OE.ReLU4d 1 256 14 14 (Gb31a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb32n1_body : forall rho, Gb32n1 rho =
  @OB.BatchNorm4d 1 256 14 14
    (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) (Gb31 rho))
    (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb32a2_body : forall rho, Gb32a2 rho =
  @OE.Add4d 1 256 14 14
    (@OB.BatchNorm4d 1 256 14 14
       (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho)
          (@OE.ReLU4d 1 256 14 14 (Gb32n1 rho)))
       (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho))
    (Gb31 rho).
Proof. intros. reflexivity. Qed.
Lemma Gb32_body : forall rho, Gb32 rho = @OE.ReLU4d 1 256 14 14 (Gb32a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb41sn_body : forall rho, Gb41sn rho =
  @OB.BatchNorm4d 1 512 7 7
    (@RD.Conv4d_1x1_s2 1 256 512 14 14
       (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) (Gb32 rho))
    (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb41n1_body : forall rho, Gb41n1 rho =
  @OB.BatchNorm4d 1 512 7 7
    (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) (Gb32 rho))
    (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb41a2_body : forall rho, Gb41a2 rho =
  @OE.Add4d 1 512 7 7
    (@OB.BatchNorm4d 1 512 7 7
       (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho)
          (@OE.ReLU4d 1 512 7 7 (Gb41n1 rho)))
       (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho))
    (Gb41sn rho).
Proof. intros. reflexivity. Qed.
Lemma Gb41_body : forall rho, Gb41 rho = @OE.ReLU4d 1 512 7 7 (Gb41a2 rho).
Proof. intros. reflexivity. Qed.

Lemma Gb42n1_body : forall rho, Gb42n1 rho =
  @OB.BatchNorm4d 1 512 7 7
    (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) (Gb41 rho))
    (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho).
Proof. intros. reflexivity. Qed.
Lemma Gb42a2_body : forall rho, Gb42a2 rho =
  @OE.Add4d 1 512 7 7
    (@OB.BatchNorm4d 1 512 7 7
       (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho)
          (@OE.ReLU4d 1 512 7 7 (Gb42n1 rho)))
       (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho))
    (Gb41 rho).
Proof. intros. reflexivity. Qed.
Lemma Gb42_body : forall rho, Gb42 rho = @OE.ReLU4d 1 512 7 7 (Gb42a2 rho).
Proof. intros. reflexivity. Qed.

Definition Gout (rho : PCG.env) : PCG.exp (ary '{1} (ary '{1000} num)) :=
  @OR.Softmax2d 1 1000
    (@OP.Linear2d 1 512 1000 (Rd _ "fc_w" rho) (Rd _ "fc_b" rho)
       (@OR.GlobalAvgPool4d 1 512 7 7 (Gb42 rho))).
Lemma Gout_body : forall rho, Gout rho =
  @OR.Softmax2d 1 1000
    (@OP.Linear2d 1 512 1000 (Rd _ "fc_w" rho) (Rd _ "fc_b" rho)
       (@OR.GlobalAvgPool4d 1 512 7 7 (Gb42 rho))).
Proof. intros. reflexivity. Qed.

(* Never unfold the wrappers in reduction/rewrite keying: every use goes *)
(* through the [*]_body lemmas above or the Hr* premises.                *)
Opaque Gx1 Gx2 Gx3 Gx4
  Gb11n1 Gb11a2 Gb11 Gb12n1 Gb12a2 Gb12
  Gb21sn Gb21n1 Gb21a2 Gb21 Gb22n1 Gb22a2 Gb22
  Gb31sn Gb31n1 Gb31a2 Gb31 Gb32n1 Gb32a2 Gb32
  Gb41sn Gb41n1 Gb41a2 Gb41 Gb42n1 Gb42a2 Gb42 Gout.

(* B1: the whole-network value equality, proved by a fold/f_equal chain     *)
(* instead of a single kernel conversion over the fully nested term.        *)
Lemma resnet18_out_eq : forall (rho : PCG.env),
  Gout rho =
  RD.ResNet18 (batch:=1) (channel:=3) (m:=224)
    (Rd _ "input" rho) (Rd _ "conv1_w" rho) (Rd _ "conv1_b" rho)
    (Rd _ "bn1_gamma" rho) (Rd _ "bn1_beta" rho) (eps_e rho)
    (Rd _ "l1_b1_w1" rho) (Rd _ "l1_b1_b1" rho)
    (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho)
    (Rd _ "l1_b1_w2" rho) (Rd _ "l1_b1_b2" rho)
    (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho)
    (Rd _ "l1_b2_w1" rho) (Rd _ "l1_b2_b1" rho)
    (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho)
    (Rd _ "l1_b2_w2" rho) (Rd _ "l1_b2_b2" rho)
    (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho)
    (Rd _ "l2_b1_w1" rho) (Rd _ "l2_b1_b1" rho)
    (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho)
    (Rd _ "l2_b1_w2" rho) (Rd _ "l2_b1_b2" rho)
    (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho)
    (Rd _ "l2_b1_shortcut_w" rho) (Rd _ "l2_b1_shortcut_b" rho)
    (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho)
    (Rd _ "l2_b2_w1" rho) (Rd _ "l2_b2_b1" rho)
    (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho)
    (Rd _ "l2_b2_w2" rho) (Rd _ "l2_b2_b2" rho)
    (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho)
    (Rd _ "l3_b1_w1" rho) (Rd _ "l3_b1_b1" rho)
    (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho)
    (Rd _ "l3_b1_w2" rho) (Rd _ "l3_b1_b2" rho)
    (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho)
    (Rd _ "l3_b1_shortcut_w" rho) (Rd _ "l3_b1_shortcut_b" rho)
    (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho)
    (Rd _ "l3_b2_w1" rho) (Rd _ "l3_b2_b1" rho)
    (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho)
    (Rd _ "l3_b2_w2" rho) (Rd _ "l3_b2_b2" rho)
    (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho)
    (Rd _ "l4_b1_w1" rho) (Rd _ "l4_b1_b1" rho)
    (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho)
    (Rd _ "l4_b1_w2" rho) (Rd _ "l4_b1_b2" rho)
    (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho)
    (Rd _ "l4_b1_shortcut_w" rho) (Rd _ "l4_b1_shortcut_b" rho)
    (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho)
    (Rd _ "l4_b2_w1" rho) (Rd _ "l4_b2_b1" rho)
    (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho)
    (Rd _ "l4_b2_w2" rho) (Rd _ "l4_b2_b2" rho)
    (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho)
    (Rd _ "fc_w" rho) (Rd _ "fc_b" rho).
Proof.
  intros rho.
  unfold RD.ResNet18, RD.BasicBlock_id, RD.BasicBlock_proj. cbv zeta beta.
  (* Fold the fully expanded route-A tree back into the wrappers, bottom-up;
     each [rewrite <-] carries a fully specified pattern over a shrinking
     tree (32 rewrites, ~30s total, no congruence applies -- see
     PROGRESS_ResNet18.md for why [f_equal]-based peeling is unusable here). *)
  rewrite <- Gx1_body.
  rewrite <- Gx2_body.
  rewrite <- Gx3_body.
  rewrite <- Gx4_body.
  rewrite <- Gb11n1_body.
  rewrite <- Gb11a2_body.
  rewrite <- Gb11_body.
  rewrite <- Gb12n1_body.
  rewrite <- Gb12a2_body.
  rewrite <- Gb12_body.
  rewrite <- Gb21sn_body.
  rewrite <- Gb21n1_body.
  rewrite <- Gb21a2_body.
  rewrite <- Gb21_body.
  rewrite <- Gb22n1_body.
  rewrite <- Gb22a2_body.
  rewrite <- Gb22_body.
  rewrite <- Gb31sn_body.
  rewrite <- Gb31n1_body.
  rewrite <- Gb31a2_body.
  rewrite <- Gb31_body.
  rewrite <- Gb32n1_body.
  rewrite <- Gb32a2_body.
  rewrite <- Gb32_body.
  rewrite <- Gb41sn_body.
  rewrite <- Gb41n1_body.
  rewrite <- Gb41a2_body.
  rewrite <- Gb41_body.
  rewrite <- Gb42n1_body.
  rewrite <- Gb42a2_body.
  rewrite <- Gb42_body.
  rewrite <- Gout_body.
  exact eq_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Forward-simulation tactics (ported from [Bridge_VGG16]).                   *)
(* -------------------------------------------------------------------------- *)

Ltac rw_fact s :=
  match goal with
  | [ H : SEM.to_pcg_exp (@CG.vrd ?d s) _ = _ |- _ ] => rewrite H
  end.

Ltac clear_fact s :=
  match goal with
  | [ H : SEM.to_pcg_exp (@CG.vrd ?d s) _ = _ |- _ ] => clear H
  end.

(* Discharge a block lemma's input-value premise [Hin] from the matching   *)
(* buffer-read fact WITHOUT an [assumption] context scan (that scan tries  *)
(* the 17 large [Hr*] hypotheses and triggers deep wrapper conversions).   *)
Ltac xin_fact s :=
  match goal with
  | [ H : SEM.to_pcg_exp (@CG.vrd ?d s) _ = _ |- _ ] => exact H
  end.

Ltac su_fact :=
  match goal with
  | [ H : PCG.StructUndefined (PCG.acc' OSE.tmp_path) _ |- _ ] => exact H
  end.

(* Solve a block rewrite's side condition regardless of the shelving order: *)
(* the input-value premise by [xin_fact], the tmp-undefinedness by [su_fact], *)
(* the ReLU premises by the corresponding [Hr*] hypothesis.                  *)
Ltac block_side_tac s Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- (PCG.idx (PCG.idx (PCG.idx (PCG.idx (OB.BatchNorm4d _ _ _ _)
                  _) _) _) _ <= R0)%R => exact Hrn
          | |- (PCG.idx (PCG.idx (PCG.idx (PCG.idx (OE.Add4d _ _)
                  _) _) _) _ <= R0)%R => exact Hra
          end ].


(* First-order congruence for [PCG.assign]: used to peel the explicit     *)
(* assign chain when closing block-level bridge lemmas (the higher-order   *)
(* unification behind [f_equal3] picks misaligned solutions here).         *)
Lemma assign_eq : forall (d : data) (a a' : PCG.acc d) (v v' : PCG.exp d)
  (c c' : PCG.env),
  a = a' -> v = v' -> c = c' ->
  PCG.assign a v c = PCG.assign a' v' c'.
Proof. intros d a a' v v' c c' -> -> ->. reflexivity. Qed.

(* Peel every pending [assign] above the current read: used by the bump   *)
(* steps of [fold_and_bump] and by [param_fact]; a no-op when the env is   *)
(* already a variable.  Needed because block-level rewrites deposit a      *)
(* whole assign chain at once.                                             *)
Ltac bump_rw :=
  repeat (first [ rewrite BL.vrd_after_other_vwt_ary_gen by str_neq_tac
                | rewrite vrd_num_after_other_vwt_ary by str_neq_tac ]).

(* Normalize the read of a never-written buffer at the current folded env  *)
(* back to [rho]: establish [Rd d s y = Rd d s rho] by walking the         *)
(* [remember] equation chain, then rewrite it away.  Needed after a block  *)
(* rewrite, whose instantiated chain reads parameters at the current env   *)
(* while the wrappers/[Hr*] premises read them at [rho].                   *)
Ltac norm_param s rho :=
  match goal with
  | |- context [Rd ?d s ?y] =>
    let H := fresh "HP" in
    assert (Rd d s y = Rd d s rho) as H;
    [ unfold Rd;
      repeat match goal with
      | [ ei : _ = PCG.assign _ _ _ |- _ ] => rewrite ei; bump_rw
      end;
      exact eq_refl
    | rewrite H; clear H ]
  end.

(* Same for the scalar [bn_eps] read ([eps_e]-form). *)
Ltac norm_eps rho :=
  match goal with
  | |- context [eps_e ?y] =>
    let H := fresh "HEPS" in
    assert (eps_e y = eps_e rho) as H;
    [ unfold eps_e, Rd;
      repeat match goal with
      | [ ei : _ = PCG.assign _ _ _ |- _ ] => rewrite ei; bump_rw
      end;
      exact eq_refl
    | rewrite H; clear H ]
  end.

(* Establish the read fact of a never-written (parameter) buffer [s] at the *)
(* current folded environment by walking the [remember] equation chain back *)
(* to [rho] (passed explicitly: Ltac bodies cannot close over proof         *)
(* variables); used once per parameter read, then cleared.                  *)
Ltac param_fact s rho :=
  match goal with
  | |- context [SEM.to_pcg_exp (@CG.vrd ?d s) ?y] =>
    assert (SEM.to_pcg_exp (@CG.vrd d s) y = Rd d s rho);
    [ repeat match goal with
      | [ ei : _ = PCG.assign _ _ _ |- _ ] =>
        rewrite ei; bump_rw
      end;
      exact eq_refl | ]
  end.

(* Fold the freshly extended environment [assign (vwt so) v eta] into a new *)
(* variable, bump every buffer-read fact and the [StructUndefined tmp] fact *)
(* to the new variable, and record the own-read fact for [so] in the folded *)
(* form [XV].  Identical to [Bridge_VGG16.fold_and_bump] except that the    *)
(* fact bump also covers scalar reads ([vrd num], e.g. "bn_eps") via        *)
(* [vrd_num_after_other_vwt_ary].                                           *)
Ltac fold_and_bump so XV :=
  match goal with
  | |- context [ PCG.assign (OSE.as_PCG_acc (@CG.vwt ?td so)) ?v ?eta ] =>
    let x := fresh "NS" in
    let e := fresh "HE" in
    remember (PCG.assign (OSE.as_PCG_acc (@CG.vwt td so)) v eta) as x eqn:e;
    (* NOTE: [eta] may itself be a whole assign chain (after a block-level
       rewrite), so facts are matched at ANY env and re-proved by walking
       the chain with [bump_rw] down to the chain tail (the invariant is
       that every live fact is about that tail). *)
    repeat match goal with
    | [ H : SEM.to_pcg_exp (@CG.vrd ?d ?s) _ = ?g |- _ ] =>
      assert (SEM.to_pcg_exp (@CG.vrd d s) x = g) by
        (rewrite e; bump_rw; exact H);
      clear H
    end;
    match goal with
    | [ H : PCG.StructUndefined (PCG.acc' OSE.tmp_path) _ |- _ ] =>
      assert (PCG.StructUndefined (PCG.acc' OSE.tmp_path) x) by
        (rewrite e;
         repeat (apply BL.SU_tmp_after_assign_vwt;
                 [ intros u Heq2; discriminate | idtac ]);
         exact H);
      clear H
    end;
    assert (SEM.to_pcg_exp (@CG.vrd td so) x = XV) by
      (rewrite e; apply SEM.vrd_after_own_vwt; discriminate)
  end.
(* -------------------------------------------------------------------------- *)
(* Block-level bridge lemmas (B1 for the residual structure): each BasicBlock*)
(* gets its own fold-disciplined forward simulation with a local [remember]  *)
(* chain, so no proof state ever spans more than one block.  The main        *)
(* theorem then needs only 15 rewrites (4 stem layers, 8 blocks, 3           *)
(* classifier layers).                                                       *)
(* -------------------------------------------------------------------------- *)

(* Block bridge: l1_b1 (identity, 64 @ 56). *)
Lemma bridge_bb_l1b1 : forall (rho : PCG.env) (X : PCG.exp (T4 1 64 56 56)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 64 56 56) "pool_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho)) X) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_id_ast 64 56 "pool_out" "l1_b1_w1" "l1_b1_b1" "l1_b1_bn1_gamma" "l1_b1_bn1_beta"
    "l1_b1_w2" "l1_b1_b2" "l1_b1_bn2_gamma" "l1_b1_bn2_beta"
    "l1_b1_conv1_out" "l1_b1_bn1_out" "l1_b1_relu1_out"
    "l1_b1_conv2_out" "l1_b1_bn2_out" "l1_b1_add_out" "l1_b1_out") rho =
  (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_out")
         (@OE.ReLU4d 1 64 56 56 (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho)) X))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_add_out")
         (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho)) X)
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_bn2_out")
         (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_conv2_out")
         (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_relu1_out")
         (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_bn1_out")
         (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b1_conv1_out")
         (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X)
        rho))))))).
Proof.
  intros rho X Hin Htmp Hr11n Hr11a.
  unfold bb_id_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l1_b1_b1") (CG.vrd "l1_b1_w1") (CG.vrd "pool_out")
              (CG.vwt "l1_b1_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 56 56 3 3 64 64 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l1_b1_b1" rho. rw_fact "l1_b1_b1". clear_fact "l1_b1_b1".
  param_fact "l1_b1_w1" rho. rw_fact "l1_b1_w1". clear_fact "l1_b1_w1".
  rw_fact "pool_out".
  rewrite conv4d_s1_eq_56.
  fold_and_bump "l1_b1_conv1_out" (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l1_b1_conv1_out") (BR2.bn1_mean (CG.vrd "l1_b1_conv1_out"))
              (BR2.bn1_var (CG.vrd "l1_b1_conv1_out"))
              (CG.vrd "l1_b1_bn1_gamma") (CG.vrd "l1_b1_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l1_b1_bn1_out")) ?e] =>
    rewrite (HB_bn 64 56 56 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l1_b1_conv1_out". clear_fact "l1_b1_conv1_out".
  param_fact "l1_b1_bn1_gamma" rho. rw_fact "l1_b1_bn1_gamma". clear_fact "l1_b1_bn1_gamma".
  param_fact "l1_b1_bn1_beta" rho. rw_fact "l1_b1_bn1_beta". clear_fact "l1_b1_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l1_b1_bn1_out" (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l1_b1_bn1_out") (CG.vwt "l1_b1_relu1_out")) ?e] =>
    rewrite (HB_relu 1 64 56 56 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l1_b1_bn1_out"; exact (Hr11n b c i0 i1) ].
  rw_fact "l1_b1_bn1_out". clear_fact "l1_b1_bn1_out".
  fold_and_bump "l1_b1_relu1_out" (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l1_b1_b2") (CG.vrd "l1_b1_w2") (CG.vrd "l1_b1_relu1_out")
              (CG.vwt "l1_b1_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 56 56 3 3 64 64 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l1_b1_b2" rho. rw_fact "l1_b1_b2". clear_fact "l1_b1_b2".
  param_fact "l1_b1_w2" rho. rw_fact "l1_b1_w2". clear_fact "l1_b1_w2".
  rw_fact "l1_b1_relu1_out". clear_fact "l1_b1_relu1_out".
  rewrite conv4d_s1_eq_56.
  fold_and_bump "l1_b1_conv2_out" (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l1_b1_conv2_out") (BR2.bn1_mean (CG.vrd "l1_b1_conv2_out"))
              (BR2.bn1_var (CG.vrd "l1_b1_conv2_out"))
              (CG.vrd "l1_b1_bn2_gamma") (CG.vrd "l1_b1_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l1_b1_bn2_out")) ?e] =>
    rewrite (HB_bn 64 56 56 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l1_b1_conv2_out". clear_fact "l1_b1_conv2_out".
  param_fact "l1_b1_bn2_gamma" rho. rw_fact "l1_b1_bn2_gamma". clear_fact "l1_b1_bn2_gamma".
  param_fact "l1_b1_bn2_beta" rho. rw_fact "l1_b1_bn2_beta". clear_fact "l1_b1_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l1_b1_bn2_out" (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l1_b1_bn2_out")
              (CG.vrd "pool_out") (CG.vwt "l1_b1_add_out")) ?e] =>
    rewrite (HB_add 1 64 56 56 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l1_b1_bn2_out". clear_fact "l1_b1_bn2_out".
  rw_fact "pool_out". clear_fact "pool_out".
  fold_and_bump "l1_b1_add_out" (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b2" rho) (Rd _ "l1_b1_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b1_b1" rho) (Rd _ "l1_b1_w1" rho) X) (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho) (eps_e rho)) X).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l1_b1_add_out") (CG.vwt "l1_b1_out")) ?e] =>
    rewrite (HB_relu 1 64 56 56 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l1_b1_add_out"; exact (Hr11a b c i0 i1) ].
  rw_fact "l1_b1_add_out". clear_fact "l1_b1_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l1_b2 (identity, 64 @ 56). *)
Lemma bridge_bb_l1b2 : forall (rho : PCG.env) (X : PCG.exp (T4 1 64 56 56)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 64 56 56) "l1_b1_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho)) X) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_id_ast 64 56 "l1_b1_out" "l1_b2_w1" "l1_b2_b1" "l1_b2_bn1_gamma" "l1_b2_bn1_beta"
    "l1_b2_w2" "l1_b2_b2" "l1_b2_bn2_gamma" "l1_b2_bn2_beta"
    "l1_b2_conv1_out" "l1_b2_bn1_out" "l1_b2_relu1_out"
    "l1_b2_conv2_out" "l1_b2_bn2_out" "l1_b2_add_out" "l1_b2_out") rho =
  (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_out")
         (@OE.ReLU4d 1 64 56 56 (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho)) X))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_add_out")
         (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho)) X)
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_bn2_out")
         (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_conv2_out")
         (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_relu1_out")
         (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_bn1_out")
         (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 64 56 56) "l1_b2_conv1_out")
         (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X)
        rho))))))).
Proof.
  intros rho X Hin Htmp Hr12n Hr12a.
  unfold bb_id_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l1_b2_b1") (CG.vrd "l1_b2_w1") (CG.vrd "l1_b1_out")
              (CG.vwt "l1_b2_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 56 56 3 3 64 64 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l1_b2_b1" rho. rw_fact "l1_b2_b1". clear_fact "l1_b2_b1".
  param_fact "l1_b2_w1" rho. rw_fact "l1_b2_w1". clear_fact "l1_b2_w1".
  rw_fact "l1_b1_out".
  rewrite conv4d_s1_eq_56.
  fold_and_bump "l1_b2_conv1_out" (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l1_b2_conv1_out") (BR2.bn1_mean (CG.vrd "l1_b2_conv1_out"))
              (BR2.bn1_var (CG.vrd "l1_b2_conv1_out"))
              (CG.vrd "l1_b2_bn1_gamma") (CG.vrd "l1_b2_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l1_b2_bn1_out")) ?e] =>
    rewrite (HB_bn 64 56 56 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l1_b2_conv1_out". clear_fact "l1_b2_conv1_out".
  param_fact "l1_b2_bn1_gamma" rho. rw_fact "l1_b2_bn1_gamma". clear_fact "l1_b2_bn1_gamma".
  param_fact "l1_b2_bn1_beta" rho. rw_fact "l1_b2_bn1_beta". clear_fact "l1_b2_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l1_b2_bn1_out" (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l1_b2_bn1_out") (CG.vwt "l1_b2_relu1_out")) ?e] =>
    rewrite (HB_relu 1 64 56 56 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l1_b2_bn1_out"; exact (Hr12n b c i0 i1) ].
  rw_fact "l1_b2_bn1_out". clear_fact "l1_b2_bn1_out".
  fold_and_bump "l1_b2_relu1_out" (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l1_b2_b2") (CG.vrd "l1_b2_w2") (CG.vrd "l1_b2_relu1_out")
              (CG.vwt "l1_b2_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 56 56 3 3 64 64 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l1_b2_b2" rho. rw_fact "l1_b2_b2". clear_fact "l1_b2_b2".
  param_fact "l1_b2_w2" rho. rw_fact "l1_b2_w2". clear_fact "l1_b2_w2".
  rw_fact "l1_b2_relu1_out". clear_fact "l1_b2_relu1_out".
  rewrite conv4d_s1_eq_56.
  fold_and_bump "l1_b2_conv2_out" (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l1_b2_conv2_out") (BR2.bn1_mean (CG.vrd "l1_b2_conv2_out"))
              (BR2.bn1_var (CG.vrd "l1_b2_conv2_out"))
              (CG.vrd "l1_b2_bn2_gamma") (CG.vrd "l1_b2_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l1_b2_bn2_out")) ?e] =>
    rewrite (HB_bn 64 56 56 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l1_b2_conv2_out". clear_fact "l1_b2_conv2_out".
  param_fact "l1_b2_bn2_gamma" rho. rw_fact "l1_b2_bn2_gamma". clear_fact "l1_b2_bn2_gamma".
  param_fact "l1_b2_bn2_beta" rho. rw_fact "l1_b2_bn2_beta". clear_fact "l1_b2_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l1_b2_bn2_out" (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l1_b2_bn2_out")
              (CG.vrd "l1_b1_out") (CG.vwt "l1_b2_add_out")) ?e] =>
    rewrite (HB_add 1 64 56 56 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l1_b2_bn2_out". clear_fact "l1_b2_bn2_out".
  rw_fact "l1_b1_out". clear_fact "l1_b1_out".
  fold_and_bump "l1_b2_add_out" (@OE.Add4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b2" rho) (Rd _ "l1_b2_w2" rho) (@OE.ReLU4d 1 64 56 56 (@OB.BatchNorm4d 1 64 56 56 (@RD.Conv4d_3x3_s1 1 64 64 56 56 (Rd _ "l1_b2_b1" rho) (Rd _ "l1_b2_w1" rho) X) (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho) (eps_e rho)) X).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l1_b2_add_out") (CG.vwt "l1_b2_out")) ?e] =>
    rewrite (HB_relu 1 64 56 56 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l1_b2_add_out"; exact (Hr12a b c i0 i1) ].
  rw_fact "l1_b2_add_out". clear_fact "l1_b2_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l2_b1 (projection 64 -> 128 @ 56). *)
Lemma bridge_bb_l2b1 : forall (rho : PCG.env) (X : PCG.exp (T4 1 64 56 56)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 64 56 56) "l1_b2_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X) (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho))) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_proj_ast 64 128 56 "l1_b2_out"
    "l2_b1_w1" "l2_b1_b1" "l2_b1_bn1_gamma" "l2_b1_bn1_beta"
    "l2_b1_w2" "l2_b1_b2" "l2_b1_bn2_gamma" "l2_b1_bn2_beta"
    "l2_b1_shortcut_w" "l2_b1_shortcut_b"
    "l2_b1_shortcut_gamma" "l2_b1_shortcut_beta"
    "l2_b1_shortcut_out" "l2_b1_sbn_out"
    "l2_b1_conv1_out" "l2_b1_bn1_out" "l2_b1_relu1_out"
    "l2_b1_conv2_out" "l2_b1_bn2_out" "l2_b1_add_out" "l2_b1_out") rho =
  (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_out")
         (@OE.ReLU4d 1 128 28 28 (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X) (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_add_out")
         (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X) (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_bn2_out")
         (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_conv2_out")
         (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_relu1_out")
         (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_bn1_out")
         (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_conv1_out")
         (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X)
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_sbn_out")
         (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X) (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b1_shortcut_out")
         (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X)
        rho))))))))).
Proof.
  intros rho X Hin Htmp Hr21n Hr21a.
  unfold bb_proj_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 0 2
              (CG.vrd "l2_b1_shortcut_b") (CG.vrd "l2_b1_shortcut_w") (CG.vrd "l1_b2_out")
              (CG.vwt "l2_b1_shortcut_out")) ?e] =>
    rewrite (HB_conv4d 1 56 56 1 1 64 128 0 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l2_b1_shortcut_b" rho. rw_fact "l2_b1_shortcut_b". clear_fact "l2_b1_shortcut_b".
  param_fact "l2_b1_shortcut_w" rho. rw_fact "l2_b1_shortcut_w". clear_fact "l2_b1_shortcut_w".
  rw_fact "l1_b2_out".
  fold_and_bump "l2_b1_shortcut_out" (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l2_b1_shortcut_out") (BR2.bn1_mean (CG.vrd "l2_b1_shortcut_out"))
              (BR2.bn1_var (CG.vrd "l2_b1_shortcut_out"))
              (CG.vrd "l2_b1_shortcut_gamma") (CG.vrd "l2_b1_shortcut_beta") (CG.vrd "bn_eps")
              (CG.vwt "l2_b1_sbn_out")) ?e] =>
    rewrite (HB_bn 128 28 28 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l2_b1_shortcut_out". clear_fact "l2_b1_shortcut_out".
  param_fact "l2_b1_shortcut_gamma" rho. rw_fact "l2_b1_shortcut_gamma". clear_fact "l2_b1_shortcut_gamma".
  param_fact "l2_b1_shortcut_beta" rho. rw_fact "l2_b1_shortcut_beta". clear_fact "l2_b1_shortcut_beta".
  rw_fact "bn_eps".
  fold_and_bump "l2_b1_sbn_out" (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X) (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 2
              (CG.vrd "l2_b1_b1") (CG.vrd "l2_b1_w1") (CG.vrd "l1_b2_out")
              (CG.vwt "l2_b1_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 56 56 3 3 64 128 1 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l2_b1_b1" rho. rw_fact "l2_b1_b1". clear_fact "l2_b1_b1".
  param_fact "l2_b1_w1" rho. rw_fact "l2_b1_w1". clear_fact "l2_b1_w1".
  rw_fact "l1_b2_out". clear_fact "l1_b2_out".
  fold_and_bump "l2_b1_conv1_out" (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l2_b1_conv1_out") (BR2.bn1_mean (CG.vrd "l2_b1_conv1_out"))
              (BR2.bn1_var (CG.vrd "l2_b1_conv1_out"))
              (CG.vrd "l2_b1_bn1_gamma") (CG.vrd "l2_b1_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l2_b1_bn1_out")) ?e] =>
    rewrite (HB_bn 128 28 28 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l2_b1_conv1_out". clear_fact "l2_b1_conv1_out".
  param_fact "l2_b1_bn1_gamma" rho. rw_fact "l2_b1_bn1_gamma". clear_fact "l2_b1_bn1_gamma".
  param_fact "l2_b1_bn1_beta" rho. rw_fact "l2_b1_bn1_beta". clear_fact "l2_b1_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l2_b1_bn1_out" (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l2_b1_bn1_out") (CG.vwt "l2_b1_relu1_out")) ?e] =>
    rewrite (HB_relu 1 128 28 28 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l2_b1_bn1_out"; exact (Hr21n b c i0 i1) ].
  rw_fact "l2_b1_bn1_out". clear_fact "l2_b1_bn1_out".
  fold_and_bump "l2_b1_relu1_out" (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l2_b1_b2") (CG.vrd "l2_b1_w2") (CG.vrd "l2_b1_relu1_out")
              (CG.vwt "l2_b1_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 28 28 3 3 128 128 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l2_b1_b2" rho. rw_fact "l2_b1_b2". clear_fact "l2_b1_b2".
  param_fact "l2_b1_w2" rho. rw_fact "l2_b1_w2". clear_fact "l2_b1_w2".
  rw_fact "l2_b1_relu1_out". clear_fact "l2_b1_relu1_out".
  rewrite conv4d_s1_eq_28.
  fold_and_bump "l2_b1_conv2_out" (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l2_b1_conv2_out") (BR2.bn1_mean (CG.vrd "l2_b1_conv2_out"))
              (BR2.bn1_var (CG.vrd "l2_b1_conv2_out"))
              (CG.vrd "l2_b1_bn2_gamma") (CG.vrd "l2_b1_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l2_b1_bn2_out")) ?e] =>
    rewrite (HB_bn 128 28 28 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l2_b1_conv2_out". clear_fact "l2_b1_conv2_out".
  param_fact "l2_b1_bn2_gamma" rho. rw_fact "l2_b1_bn2_gamma". clear_fact "l2_b1_bn2_gamma".
  param_fact "l2_b1_bn2_beta" rho. rw_fact "l2_b1_bn2_beta". clear_fact "l2_b1_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l2_b1_bn2_out" (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l2_b1_bn2_out")
              (CG.vrd "l2_b1_sbn_out") (CG.vwt "l2_b1_add_out")) ?e] =>
    rewrite (HB_add 1 128 28 28 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l2_b1_bn2_out". clear_fact "l2_b1_bn2_out".
  rw_fact "l2_b1_sbn_out". clear_fact "l2_b1_sbn_out".
  fold_and_bump "l2_b1_add_out" (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b1_b2" rho) (Rd _ "l2_b1_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s2 1 64 128 56 56 (Rd _ "l2_b1_b1" rho) (Rd _ "l2_b1_w1" rho) X) (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_1x1_s2 1 64 128 56 56 (Rd _ "l2_b1_shortcut_b" rho) (Rd _ "l2_b1_shortcut_w" rho) X) (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho) (eps_e rho))).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l2_b1_add_out") (CG.vwt "l2_b1_out")) ?e] =>
    rewrite (HB_relu 1 128 28 28 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l2_b1_add_out"; exact (Hr21a b c i0 i1) ].
  rw_fact "l2_b1_add_out". clear_fact "l2_b1_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l2_b2 (identity, 128 @ 28). *)
Lemma bridge_bb_l2b2 : forall (rho : PCG.env) (X : PCG.exp (T4 1 128 28 28)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 128 28 28) "l2_b1_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho)) X) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_id_ast 128 28 "l2_b1_out" "l2_b2_w1" "l2_b2_b1" "l2_b2_bn1_gamma" "l2_b2_bn1_beta"
    "l2_b2_w2" "l2_b2_b2" "l2_b2_bn2_gamma" "l2_b2_bn2_beta"
    "l2_b2_conv1_out" "l2_b2_bn1_out" "l2_b2_relu1_out"
    "l2_b2_conv2_out" "l2_b2_bn2_out" "l2_b2_add_out" "l2_b2_out") rho =
  (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_out")
         (@OE.ReLU4d 1 128 28 28 (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho)) X))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_add_out")
         (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho)) X)
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_bn2_out")
         (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_conv2_out")
         (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_relu1_out")
         (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_bn1_out")
         (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 128 28 28) "l2_b2_conv1_out")
         (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X)
        rho))))))).
Proof.
  intros rho X Hin Htmp Hr22n Hr22a.
  unfold bb_id_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l2_b2_b1") (CG.vrd "l2_b2_w1") (CG.vrd "l2_b1_out")
              (CG.vwt "l2_b2_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 28 28 3 3 128 128 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l2_b2_b1" rho. rw_fact "l2_b2_b1". clear_fact "l2_b2_b1".
  param_fact "l2_b2_w1" rho. rw_fact "l2_b2_w1". clear_fact "l2_b2_w1".
  rw_fact "l2_b1_out".
  rewrite conv4d_s1_eq_28.
  fold_and_bump "l2_b2_conv1_out" (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l2_b2_conv1_out") (BR2.bn1_mean (CG.vrd "l2_b2_conv1_out"))
              (BR2.bn1_var (CG.vrd "l2_b2_conv1_out"))
              (CG.vrd "l2_b2_bn1_gamma") (CG.vrd "l2_b2_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l2_b2_bn1_out")) ?e] =>
    rewrite (HB_bn 128 28 28 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l2_b2_conv1_out". clear_fact "l2_b2_conv1_out".
  param_fact "l2_b2_bn1_gamma" rho. rw_fact "l2_b2_bn1_gamma". clear_fact "l2_b2_bn1_gamma".
  param_fact "l2_b2_bn1_beta" rho. rw_fact "l2_b2_bn1_beta". clear_fact "l2_b2_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l2_b2_bn1_out" (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l2_b2_bn1_out") (CG.vwt "l2_b2_relu1_out")) ?e] =>
    rewrite (HB_relu 1 128 28 28 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l2_b2_bn1_out"; exact (Hr22n b c i0 i1) ].
  rw_fact "l2_b2_bn1_out". clear_fact "l2_b2_bn1_out".
  fold_and_bump "l2_b2_relu1_out" (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l2_b2_b2") (CG.vrd "l2_b2_w2") (CG.vrd "l2_b2_relu1_out")
              (CG.vwt "l2_b2_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 28 28 3 3 128 128 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l2_b2_b2" rho. rw_fact "l2_b2_b2". clear_fact "l2_b2_b2".
  param_fact "l2_b2_w2" rho. rw_fact "l2_b2_w2". clear_fact "l2_b2_w2".
  rw_fact "l2_b2_relu1_out". clear_fact "l2_b2_relu1_out".
  rewrite conv4d_s1_eq_28.
  fold_and_bump "l2_b2_conv2_out" (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l2_b2_conv2_out") (BR2.bn1_mean (CG.vrd "l2_b2_conv2_out"))
              (BR2.bn1_var (CG.vrd "l2_b2_conv2_out"))
              (CG.vrd "l2_b2_bn2_gamma") (CG.vrd "l2_b2_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l2_b2_bn2_out")) ?e] =>
    rewrite (HB_bn 128 28 28 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l2_b2_conv2_out". clear_fact "l2_b2_conv2_out".
  param_fact "l2_b2_bn2_gamma" rho. rw_fact "l2_b2_bn2_gamma". clear_fact "l2_b2_bn2_gamma".
  param_fact "l2_b2_bn2_beta" rho. rw_fact "l2_b2_bn2_beta". clear_fact "l2_b2_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l2_b2_bn2_out" (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l2_b2_bn2_out")
              (CG.vrd "l2_b1_out") (CG.vwt "l2_b2_add_out")) ?e] =>
    rewrite (HB_add 1 128 28 28 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l2_b2_bn2_out". clear_fact "l2_b2_bn2_out".
  rw_fact "l2_b1_out". clear_fact "l2_b1_out".
  fold_and_bump "l2_b2_add_out" (@OE.Add4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b2" rho) (Rd _ "l2_b2_w2" rho) (@OE.ReLU4d 1 128 28 28 (@OB.BatchNorm4d 1 128 28 28 (@RD.Conv4d_3x3_s1 1 128 128 28 28 (Rd _ "l2_b2_b1" rho) (Rd _ "l2_b2_w1" rho) X) (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho) (eps_e rho)) X).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l2_b2_add_out") (CG.vwt "l2_b2_out")) ?e] =>
    rewrite (HB_relu 1 128 28 28 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l2_b2_add_out"; exact (Hr22a b c i0 i1) ].
  rw_fact "l2_b2_add_out". clear_fact "l2_b2_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l3_b1 (projection 128 -> 256 @ 28). *)
Lemma bridge_bb_l3b1 : forall (rho : PCG.env) (X : PCG.exp (T4 1 128 28 28)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 128 28 28) "l2_b2_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X) (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho))) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_proj_ast 128 256 28 "l2_b2_out"
    "l3_b1_w1" "l3_b1_b1" "l3_b1_bn1_gamma" "l3_b1_bn1_beta"
    "l3_b1_w2" "l3_b1_b2" "l3_b1_bn2_gamma" "l3_b1_bn2_beta"
    "l3_b1_shortcut_w" "l3_b1_shortcut_b"
    "l3_b1_shortcut_gamma" "l3_b1_shortcut_beta"
    "l3_b1_shortcut_out" "l3_b1_sbn_out"
    "l3_b1_conv1_out" "l3_b1_bn1_out" "l3_b1_relu1_out"
    "l3_b1_conv2_out" "l3_b1_bn2_out" "l3_b1_add_out" "l3_b1_out") rho =
  (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_out")
         (@OE.ReLU4d 1 256 14 14 (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X) (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_add_out")
         (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X) (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_bn2_out")
         (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_conv2_out")
         (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_relu1_out")
         (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_bn1_out")
         (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_conv1_out")
         (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X)
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_sbn_out")
         (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X) (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b1_shortcut_out")
         (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X)
        rho))))))))).
Proof.
  intros rho X Hin Htmp Hr31n Hr31a.
  unfold bb_proj_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 0 2
              (CG.vrd "l3_b1_shortcut_b") (CG.vrd "l3_b1_shortcut_w") (CG.vrd "l2_b2_out")
              (CG.vwt "l3_b1_shortcut_out")) ?e] =>
    rewrite (HB_conv4d 1 28 28 1 1 128 256 0 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l3_b1_shortcut_b" rho. rw_fact "l3_b1_shortcut_b". clear_fact "l3_b1_shortcut_b".
  param_fact "l3_b1_shortcut_w" rho. rw_fact "l3_b1_shortcut_w". clear_fact "l3_b1_shortcut_w".
  rw_fact "l2_b2_out".
  fold_and_bump "l3_b1_shortcut_out" (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l3_b1_shortcut_out") (BR2.bn1_mean (CG.vrd "l3_b1_shortcut_out"))
              (BR2.bn1_var (CG.vrd "l3_b1_shortcut_out"))
              (CG.vrd "l3_b1_shortcut_gamma") (CG.vrd "l3_b1_shortcut_beta") (CG.vrd "bn_eps")
              (CG.vwt "l3_b1_sbn_out")) ?e] =>
    rewrite (HB_bn 256 14 14 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l3_b1_shortcut_out". clear_fact "l3_b1_shortcut_out".
  param_fact "l3_b1_shortcut_gamma" rho. rw_fact "l3_b1_shortcut_gamma". clear_fact "l3_b1_shortcut_gamma".
  param_fact "l3_b1_shortcut_beta" rho. rw_fact "l3_b1_shortcut_beta". clear_fact "l3_b1_shortcut_beta".
  rw_fact "bn_eps".
  fold_and_bump "l3_b1_sbn_out" (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X) (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 2
              (CG.vrd "l3_b1_b1") (CG.vrd "l3_b1_w1") (CG.vrd "l2_b2_out")
              (CG.vwt "l3_b1_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 28 28 3 3 128 256 1 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l3_b1_b1" rho. rw_fact "l3_b1_b1". clear_fact "l3_b1_b1".
  param_fact "l3_b1_w1" rho. rw_fact "l3_b1_w1". clear_fact "l3_b1_w1".
  rw_fact "l2_b2_out". clear_fact "l2_b2_out".
  fold_and_bump "l3_b1_conv1_out" (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l3_b1_conv1_out") (BR2.bn1_mean (CG.vrd "l3_b1_conv1_out"))
              (BR2.bn1_var (CG.vrd "l3_b1_conv1_out"))
              (CG.vrd "l3_b1_bn1_gamma") (CG.vrd "l3_b1_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l3_b1_bn1_out")) ?e] =>
    rewrite (HB_bn 256 14 14 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l3_b1_conv1_out". clear_fact "l3_b1_conv1_out".
  param_fact "l3_b1_bn1_gamma" rho. rw_fact "l3_b1_bn1_gamma". clear_fact "l3_b1_bn1_gamma".
  param_fact "l3_b1_bn1_beta" rho. rw_fact "l3_b1_bn1_beta". clear_fact "l3_b1_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l3_b1_bn1_out" (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l3_b1_bn1_out") (CG.vwt "l3_b1_relu1_out")) ?e] =>
    rewrite (HB_relu 1 256 14 14 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l3_b1_bn1_out"; exact (Hr31n b c i0 i1) ].
  rw_fact "l3_b1_bn1_out". clear_fact "l3_b1_bn1_out".
  fold_and_bump "l3_b1_relu1_out" (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l3_b1_b2") (CG.vrd "l3_b1_w2") (CG.vrd "l3_b1_relu1_out")
              (CG.vwt "l3_b1_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 14 14 3 3 256 256 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l3_b1_b2" rho. rw_fact "l3_b1_b2". clear_fact "l3_b1_b2".
  param_fact "l3_b1_w2" rho. rw_fact "l3_b1_w2". clear_fact "l3_b1_w2".
  rw_fact "l3_b1_relu1_out". clear_fact "l3_b1_relu1_out".
  rewrite conv4d_s1_eq_14.
  fold_and_bump "l3_b1_conv2_out" (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l3_b1_conv2_out") (BR2.bn1_mean (CG.vrd "l3_b1_conv2_out"))
              (BR2.bn1_var (CG.vrd "l3_b1_conv2_out"))
              (CG.vrd "l3_b1_bn2_gamma") (CG.vrd "l3_b1_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l3_b1_bn2_out")) ?e] =>
    rewrite (HB_bn 256 14 14 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l3_b1_conv2_out". clear_fact "l3_b1_conv2_out".
  param_fact "l3_b1_bn2_gamma" rho. rw_fact "l3_b1_bn2_gamma". clear_fact "l3_b1_bn2_gamma".
  param_fact "l3_b1_bn2_beta" rho. rw_fact "l3_b1_bn2_beta". clear_fact "l3_b1_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l3_b1_bn2_out" (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l3_b1_bn2_out")
              (CG.vrd "l3_b1_sbn_out") (CG.vwt "l3_b1_add_out")) ?e] =>
    rewrite (HB_add 1 256 14 14 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l3_b1_bn2_out". clear_fact "l3_b1_bn2_out".
  rw_fact "l3_b1_sbn_out". clear_fact "l3_b1_sbn_out".
  fold_and_bump "l3_b1_add_out" (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b1_b2" rho) (Rd _ "l3_b1_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s2 1 128 256 28 28 (Rd _ "l3_b1_b1" rho) (Rd _ "l3_b1_w1" rho) X) (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_1x1_s2 1 128 256 28 28 (Rd _ "l3_b1_shortcut_b" rho) (Rd _ "l3_b1_shortcut_w" rho) X) (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho) (eps_e rho))).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l3_b1_add_out") (CG.vwt "l3_b1_out")) ?e] =>
    rewrite (HB_relu 1 256 14 14 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l3_b1_add_out"; exact (Hr31a b c i0 i1) ].
  rw_fact "l3_b1_add_out". clear_fact "l3_b1_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l3_b2 (identity, 256 @ 14). *)
Lemma bridge_bb_l3b2 : forall (rho : PCG.env) (X : PCG.exp (T4 1 256 14 14)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 256 14 14) "l3_b1_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho)) X) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_id_ast 256 14 "l3_b1_out" "l3_b2_w1" "l3_b2_b1" "l3_b2_bn1_gamma" "l3_b2_bn1_beta"
    "l3_b2_w2" "l3_b2_b2" "l3_b2_bn2_gamma" "l3_b2_bn2_beta"
    "l3_b2_conv1_out" "l3_b2_bn1_out" "l3_b2_relu1_out"
    "l3_b2_conv2_out" "l3_b2_bn2_out" "l3_b2_add_out" "l3_b2_out") rho =
  (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_out")
         (@OE.ReLU4d 1 256 14 14 (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho)) X))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_add_out")
         (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho)) X)
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_bn2_out")
         (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_conv2_out")
         (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_relu1_out")
         (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_bn1_out")
         (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 256 14 14) "l3_b2_conv1_out")
         (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X)
        rho))))))).
Proof.
  intros rho X Hin Htmp Hr32n Hr32a.
  unfold bb_id_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l3_b2_b1") (CG.vrd "l3_b2_w1") (CG.vrd "l3_b1_out")
              (CG.vwt "l3_b2_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 14 14 3 3 256 256 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l3_b2_b1" rho. rw_fact "l3_b2_b1". clear_fact "l3_b2_b1".
  param_fact "l3_b2_w1" rho. rw_fact "l3_b2_w1". clear_fact "l3_b2_w1".
  rw_fact "l3_b1_out".
  rewrite conv4d_s1_eq_14.
  fold_and_bump "l3_b2_conv1_out" (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l3_b2_conv1_out") (BR2.bn1_mean (CG.vrd "l3_b2_conv1_out"))
              (BR2.bn1_var (CG.vrd "l3_b2_conv1_out"))
              (CG.vrd "l3_b2_bn1_gamma") (CG.vrd "l3_b2_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l3_b2_bn1_out")) ?e] =>
    rewrite (HB_bn 256 14 14 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l3_b2_conv1_out". clear_fact "l3_b2_conv1_out".
  param_fact "l3_b2_bn1_gamma" rho. rw_fact "l3_b2_bn1_gamma". clear_fact "l3_b2_bn1_gamma".
  param_fact "l3_b2_bn1_beta" rho. rw_fact "l3_b2_bn1_beta". clear_fact "l3_b2_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l3_b2_bn1_out" (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l3_b2_bn1_out") (CG.vwt "l3_b2_relu1_out")) ?e] =>
    rewrite (HB_relu 1 256 14 14 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l3_b2_bn1_out"; exact (Hr32n b c i0 i1) ].
  rw_fact "l3_b2_bn1_out". clear_fact "l3_b2_bn1_out".
  fold_and_bump "l3_b2_relu1_out" (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l3_b2_b2") (CG.vrd "l3_b2_w2") (CG.vrd "l3_b2_relu1_out")
              (CG.vwt "l3_b2_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 14 14 3 3 256 256 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l3_b2_b2" rho. rw_fact "l3_b2_b2". clear_fact "l3_b2_b2".
  param_fact "l3_b2_w2" rho. rw_fact "l3_b2_w2". clear_fact "l3_b2_w2".
  rw_fact "l3_b2_relu1_out". clear_fact "l3_b2_relu1_out".
  rewrite conv4d_s1_eq_14.
  fold_and_bump "l3_b2_conv2_out" (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l3_b2_conv2_out") (BR2.bn1_mean (CG.vrd "l3_b2_conv2_out"))
              (BR2.bn1_var (CG.vrd "l3_b2_conv2_out"))
              (CG.vrd "l3_b2_bn2_gamma") (CG.vrd "l3_b2_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l3_b2_bn2_out")) ?e] =>
    rewrite (HB_bn 256 14 14 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l3_b2_conv2_out". clear_fact "l3_b2_conv2_out".
  param_fact "l3_b2_bn2_gamma" rho. rw_fact "l3_b2_bn2_gamma". clear_fact "l3_b2_bn2_gamma".
  param_fact "l3_b2_bn2_beta" rho. rw_fact "l3_b2_bn2_beta". clear_fact "l3_b2_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l3_b2_bn2_out" (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l3_b2_bn2_out")
              (CG.vrd "l3_b1_out") (CG.vwt "l3_b2_add_out")) ?e] =>
    rewrite (HB_add 1 256 14 14 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l3_b2_bn2_out". clear_fact "l3_b2_bn2_out".
  rw_fact "l3_b1_out". clear_fact "l3_b1_out".
  fold_and_bump "l3_b2_add_out" (@OE.Add4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b2" rho) (Rd _ "l3_b2_w2" rho) (@OE.ReLU4d 1 256 14 14 (@OB.BatchNorm4d 1 256 14 14 (@RD.Conv4d_3x3_s1 1 256 256 14 14 (Rd _ "l3_b2_b1" rho) (Rd _ "l3_b2_w1" rho) X) (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho) (eps_e rho)) X).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l3_b2_add_out") (CG.vwt "l3_b2_out")) ?e] =>
    rewrite (HB_relu 1 256 14 14 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l3_b2_add_out"; exact (Hr32a b c i0 i1) ].
  rw_fact "l3_b2_add_out". clear_fact "l3_b2_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l4_b1 (projection 256 -> 512 @ 14). *)
Lemma bridge_bb_l4b1 : forall (rho : PCG.env) (X : PCG.exp (T4 1 256 14 14)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 256 14 14) "l3_b2_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X) (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho))) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_proj_ast 256 512 14 "l3_b2_out"
    "l4_b1_w1" "l4_b1_b1" "l4_b1_bn1_gamma" "l4_b1_bn1_beta"
    "l4_b1_w2" "l4_b1_b2" "l4_b1_bn2_gamma" "l4_b1_bn2_beta"
    "l4_b1_shortcut_w" "l4_b1_shortcut_b"
    "l4_b1_shortcut_gamma" "l4_b1_shortcut_beta"
    "l4_b1_shortcut_out" "l4_b1_sbn_out"
    "l4_b1_conv1_out" "l4_b1_bn1_out" "l4_b1_relu1_out"
    "l4_b1_conv2_out" "l4_b1_bn2_out" "l4_b1_add_out" "l4_b1_out") rho =
  (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_out")
         (@OE.ReLU4d 1 512 7 7 (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X) (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_add_out")
         (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X) (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_bn2_out")
         (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_conv2_out")
         (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_relu1_out")
         (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_bn1_out")
         (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_conv1_out")
         (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X)
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_sbn_out")
         (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X) (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b1_shortcut_out")
         (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X)
        rho))))))))).
Proof.
  intros rho X Hin Htmp Hr41n Hr41a.
  unfold bb_proj_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 0 2
              (CG.vrd "l4_b1_shortcut_b") (CG.vrd "l4_b1_shortcut_w") (CG.vrd "l3_b2_out")
              (CG.vwt "l4_b1_shortcut_out")) ?e] =>
    rewrite (HB_conv4d 1 14 14 1 1 256 512 0 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l4_b1_shortcut_b" rho. rw_fact "l4_b1_shortcut_b". clear_fact "l4_b1_shortcut_b".
  param_fact "l4_b1_shortcut_w" rho. rw_fact "l4_b1_shortcut_w". clear_fact "l4_b1_shortcut_w".
  rw_fact "l3_b2_out".
  fold_and_bump "l4_b1_shortcut_out" (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l4_b1_shortcut_out") (BR2.bn1_mean (CG.vrd "l4_b1_shortcut_out"))
              (BR2.bn1_var (CG.vrd "l4_b1_shortcut_out"))
              (CG.vrd "l4_b1_shortcut_gamma") (CG.vrd "l4_b1_shortcut_beta") (CG.vrd "bn_eps")
              (CG.vwt "l4_b1_sbn_out")) ?e] =>
    rewrite (HB_bn 512 7 7 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l4_b1_shortcut_out". clear_fact "l4_b1_shortcut_out".
  param_fact "l4_b1_shortcut_gamma" rho. rw_fact "l4_b1_shortcut_gamma". clear_fact "l4_b1_shortcut_gamma".
  param_fact "l4_b1_shortcut_beta" rho. rw_fact "l4_b1_shortcut_beta". clear_fact "l4_b1_shortcut_beta".
  rw_fact "bn_eps".
  fold_and_bump "l4_b1_sbn_out" (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X) (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 2
              (CG.vrd "l4_b1_b1") (CG.vrd "l4_b1_w1") (CG.vrd "l3_b2_out")
              (CG.vwt "l4_b1_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 14 14 3 3 256 512 1 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l4_b1_b1" rho. rw_fact "l4_b1_b1". clear_fact "l4_b1_b1".
  param_fact "l4_b1_w1" rho. rw_fact "l4_b1_w1". clear_fact "l4_b1_w1".
  rw_fact "l3_b2_out". clear_fact "l3_b2_out".
  fold_and_bump "l4_b1_conv1_out" (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l4_b1_conv1_out") (BR2.bn1_mean (CG.vrd "l4_b1_conv1_out"))
              (BR2.bn1_var (CG.vrd "l4_b1_conv1_out"))
              (CG.vrd "l4_b1_bn1_gamma") (CG.vrd "l4_b1_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l4_b1_bn1_out")) ?e] =>
    rewrite (HB_bn 512 7 7 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l4_b1_conv1_out". clear_fact "l4_b1_conv1_out".
  param_fact "l4_b1_bn1_gamma" rho. rw_fact "l4_b1_bn1_gamma". clear_fact "l4_b1_bn1_gamma".
  param_fact "l4_b1_bn1_beta" rho. rw_fact "l4_b1_bn1_beta". clear_fact "l4_b1_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l4_b1_bn1_out" (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l4_b1_bn1_out") (CG.vwt "l4_b1_relu1_out")) ?e] =>
    rewrite (HB_relu 1 512 7 7 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l4_b1_bn1_out"; exact (Hr41n b c i0 i1) ].
  rw_fact "l4_b1_bn1_out". clear_fact "l4_b1_bn1_out".
  fold_and_bump "l4_b1_relu1_out" (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l4_b1_b2") (CG.vrd "l4_b1_w2") (CG.vrd "l4_b1_relu1_out")
              (CG.vwt "l4_b1_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 7 7 3 3 512 512 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l4_b1_b2" rho. rw_fact "l4_b1_b2". clear_fact "l4_b1_b2".
  param_fact "l4_b1_w2" rho. rw_fact "l4_b1_w2". clear_fact "l4_b1_w2".
  rw_fact "l4_b1_relu1_out". clear_fact "l4_b1_relu1_out".
  rewrite conv4d_s1_eq_7.
  fold_and_bump "l4_b1_conv2_out" (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l4_b1_conv2_out") (BR2.bn1_mean (CG.vrd "l4_b1_conv2_out"))
              (BR2.bn1_var (CG.vrd "l4_b1_conv2_out"))
              (CG.vrd "l4_b1_bn2_gamma") (CG.vrd "l4_b1_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l4_b1_bn2_out")) ?e] =>
    rewrite (HB_bn 512 7 7 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l4_b1_conv2_out". clear_fact "l4_b1_conv2_out".
  param_fact "l4_b1_bn2_gamma" rho. rw_fact "l4_b1_bn2_gamma". clear_fact "l4_b1_bn2_gamma".
  param_fact "l4_b1_bn2_beta" rho. rw_fact "l4_b1_bn2_beta". clear_fact "l4_b1_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l4_b1_bn2_out" (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l4_b1_bn2_out")
              (CG.vrd "l4_b1_sbn_out") (CG.vwt "l4_b1_add_out")) ?e] =>
    rewrite (HB_add 1 512 7 7 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l4_b1_bn2_out". clear_fact "l4_b1_bn2_out".
  rw_fact "l4_b1_sbn_out". clear_fact "l4_b1_sbn_out".
  fold_and_bump "l4_b1_add_out" (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b1_b2" rho) (Rd _ "l4_b1_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s2 1 256 512 14 14 (Rd _ "l4_b1_b1" rho) (Rd _ "l4_b1_w1" rho) X) (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho) (eps_e rho)) (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_1x1_s2 1 256 512 14 14 (Rd _ "l4_b1_shortcut_b" rho) (Rd _ "l4_b1_shortcut_w" rho) X) (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho) (eps_e rho))).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l4_b1_add_out") (CG.vwt "l4_b1_out")) ?e] =>
    rewrite (HB_relu 1 512 7 7 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l4_b1_add_out"; exact (Hr41a b c i0 i1) ].
  rw_fact "l4_b1_add_out". clear_fact "l4_b1_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* Block bridge: l4_b2 (identity, 512 @ 7). *)
Lemma bridge_bb_l4b2 : forall (rho : PCG.env) (X : PCG.exp (T4 1 512 7 7)),
  SEM.to_pcg_exp (@CG.vrd (T4 1 512 7 7) "l4_b1_out") rho = X ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  (forall (b : fin 1) (c0 : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)) b) c0) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c0 : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho)) X) b) c0) i0) i1 <= R0)%R) ->
  SEM.eval (bb_id_ast 512 7 "l4_b1_out" "l4_b2_w1" "l4_b2_b1" "l4_b2_bn1_gamma" "l4_b2_bn1_beta"
    "l4_b2_w2" "l4_b2_b2" "l4_b2_bn2_gamma" "l4_b2_bn2_beta"
    "l4_b2_conv1_out" "l4_b2_bn1_out" "l4_b2_relu1_out"
    "l4_b2_conv2_out" "l4_b2_bn2_out" "l4_b2_add_out" "l4_b2_out") rho =
  (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_out")
         (@OE.ReLU4d 1 512 7 7 (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho)) X))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_add_out")
         (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho)) X)
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_bn2_out")
         (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_conv2_out")
         (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho))))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_relu1_out")
         (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_bn1_out")
         (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho))
        (PCG.assign (@CG.vwt (T4 1 512 7 7) "l4_b2_conv1_out")
         (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X)
        rho))))))).
Proof.
  intros rho X Hin Htmp Hr42n Hr42a.
  unfold bb_id_ast, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l4_b2_b1") (CG.vrd "l4_b2_w1") (CG.vrd "l4_b1_out")
              (CG.vwt "l4_b2_conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 7 7 3 3 512 512 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l4_b2_b1" rho. rw_fact "l4_b2_b1". clear_fact "l4_b2_b1".
  param_fact "l4_b2_w1" rho. rw_fact "l4_b2_w1". clear_fact "l4_b2_w1".
  rw_fact "l4_b1_out".
  rewrite conv4d_s1_eq_7.
  fold_and_bump "l4_b2_conv1_out" (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l4_b2_conv1_out") (BR2.bn1_mean (CG.vrd "l4_b2_conv1_out"))
              (BR2.bn1_var (CG.vrd "l4_b2_conv1_out"))
              (CG.vrd "l4_b2_bn1_gamma") (CG.vrd "l4_b2_bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "l4_b2_bn1_out")) ?e] =>
    rewrite (HB_bn 512 7 7 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l4_b2_conv1_out". clear_fact "l4_b2_conv1_out".
  param_fact "l4_b2_bn1_gamma" rho. rw_fact "l4_b2_bn1_gamma". clear_fact "l4_b2_bn1_gamma".
  param_fact "l4_b2_bn1_beta" rho. rw_fact "l4_b2_bn1_beta". clear_fact "l4_b2_bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "l4_b2_bn1_out" (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l4_b2_bn1_out") (CG.vwt "l4_b2_relu1_out")) ?e] =>
    rewrite (HB_relu 1 512 7 7 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l4_b2_bn1_out"; exact (Hr42n b c i0 i1) ].
  rw_fact "l4_b2_bn1_out". clear_fact "l4_b2_bn1_out".
  fold_and_bump "l4_b2_relu1_out" (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 1 1
              (CG.vrd "l4_b2_b2") (CG.vrd "l4_b2_w2") (CG.vrd "l4_b2_relu1_out")
              (CG.vwt "l4_b2_conv2_out")) ?e] =>
    rewrite (HB_conv4d 1 7 7 3 3 512 512 1 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "l4_b2_b2" rho. rw_fact "l4_b2_b2". clear_fact "l4_b2_b2".
  param_fact "l4_b2_w2" rho. rw_fact "l4_b2_w2". clear_fact "l4_b2_w2".
  rw_fact "l4_b2_relu1_out". clear_fact "l4_b2_relu1_out".
  rewrite conv4d_s1_eq_7.
  fold_and_bump "l4_b2_conv2_out" (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "l4_b2_conv2_out") (BR2.bn1_mean (CG.vrd "l4_b2_conv2_out"))
              (BR2.bn1_var (CG.vrd "l4_b2_conv2_out"))
              (CG.vrd "l4_b2_bn2_gamma") (CG.vrd "l4_b2_bn2_beta") (CG.vrd "bn_eps")
              (CG.vwt "l4_b2_bn2_out")) ?e] =>
    rewrite (HB_bn 512 7 7 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "l4_b2_conv2_out". clear_fact "l4_b2_conv2_out".
  param_fact "l4_b2_bn2_gamma" rho. rw_fact "l4_b2_bn2_gamma". clear_fact "l4_b2_bn2_gamma".
  param_fact "l4_b2_bn2_beta" rho. rw_fact "l4_b2_bn2_beta". clear_fact "l4_b2_bn2_beta".
  rw_fact "bn_eps".
  fold_and_bump "l4_b2_bn2_out" (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho)).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.Add4d_comm (CG.vrd "l4_b2_bn2_out")
              (CG.vrd "l4_b1_out") (CG.vwt "l4_b2_add_out")) ?e] =>
    rewrite (HB_add 1 512 7 7 _ _ _ e)
  end;
  [| str_neq_tac | str_neq_tac ].
  rw_fact "l4_b2_bn2_out". clear_fact "l4_b2_bn2_out".
  rw_fact "l4_b1_out". clear_fact "l4_b1_out".
  fold_and_bump "l4_b2_add_out" (@OE.Add4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b2" rho) (Rd _ "l4_b2_w2" rho) (@OE.ReLU4d 1 512 7 7 (@OB.BatchNorm4d 1 512 7 7 (@RD.Conv4d_3x3_s1 1 512 512 7 7 (Rd _ "l4_b2_b1" rho) (Rd _ "l4_b2_w1" rho) X) (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho) (eps_e rho)))) (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho) (eps_e rho)) X).
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "l4_b2_add_out") (CG.vwt "l4_b2_out")) ?e] =>
    rewrite (HB_relu 1 512 7 7 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "l4_b2_add_out"; exact (Hr42a b c i0 i1) ].
  rw_fact "l4_b2_add_out". clear_fact "l4_b2_add_out".
  (* Close: unfold the [remember] equations to expose the explicit chain,
     then peel the chain by first-order congruence (plain [exact eq_refl]
     triggers a pathological whole-chain conversion here; [apply f_equal3]
     picks misaligned higher-order solutions -- both measured). *)
  repeat match goal with
  | [ e : _ = PCG.assign _ _ _ |- _ ] => rewrite e
  end.
  repeat (apply assign_eq; [ exact eq_refl | exact eq_refl | ]).
  exact eq_refl.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-block side-condition tactics for the main proof's block rewrites.     *)
(* -------------------------------------------------------------------------- *)

Ltac block_tac_l1b1 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l1_b1_b1" rho;
            norm_param "l1_b1_w1" rho;
            norm_param "l1_b1_bn1_gamma" rho;
            norm_param "l1_b1_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l1_b1_b1" rho;
            norm_param "l1_b1_w1" rho;
            norm_param "l1_b1_bn1_gamma" rho;
            norm_param "l1_b1_bn1_beta" rho;
            norm_param "l1_b1_b2" rho;
            norm_param "l1_b1_w2" rho;
            norm_param "l1_b1_bn2_gamma" rho;
            norm_param "l1_b1_bn2_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l1b2 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l1_b2_b1" rho;
            norm_param "l1_b2_w1" rho;
            norm_param "l1_b2_bn1_gamma" rho;
            norm_param "l1_b2_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l1_b2_b1" rho;
            norm_param "l1_b2_w1" rho;
            norm_param "l1_b2_bn1_gamma" rho;
            norm_param "l1_b2_bn1_beta" rho;
            norm_param "l1_b2_b2" rho;
            norm_param "l1_b2_w2" rho;
            norm_param "l1_b2_bn2_gamma" rho;
            norm_param "l1_b2_bn2_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l2b1 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l2_b1_b1" rho;
            norm_param "l2_b1_w1" rho;
            norm_param "l2_b1_bn1_gamma" rho;
            norm_param "l2_b1_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l2_b1_b1" rho;
            norm_param "l2_b1_w1" rho;
            norm_param "l2_b1_bn1_gamma" rho;
            norm_param "l2_b1_bn1_beta" rho;
            norm_param "l2_b1_b2" rho;
            norm_param "l2_b1_w2" rho;
            norm_param "l2_b1_bn2_gamma" rho;
            norm_param "l2_b1_bn2_beta" rho;
            norm_param "l2_b1_shortcut_b" rho;
            norm_param "l2_b1_shortcut_w" rho;
            norm_param "l2_b1_shortcut_gamma" rho;
            norm_param "l2_b1_shortcut_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l2b2 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l2_b2_b1" rho;
            norm_param "l2_b2_w1" rho;
            norm_param "l2_b2_bn1_gamma" rho;
            norm_param "l2_b2_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l2_b2_b1" rho;
            norm_param "l2_b2_w1" rho;
            norm_param "l2_b2_bn1_gamma" rho;
            norm_param "l2_b2_bn1_beta" rho;
            norm_param "l2_b2_b2" rho;
            norm_param "l2_b2_w2" rho;
            norm_param "l2_b2_bn2_gamma" rho;
            norm_param "l2_b2_bn2_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l3b1 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l3_b1_b1" rho;
            norm_param "l3_b1_w1" rho;
            norm_param "l3_b1_bn1_gamma" rho;
            norm_param "l3_b1_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l3_b1_b1" rho;
            norm_param "l3_b1_w1" rho;
            norm_param "l3_b1_bn1_gamma" rho;
            norm_param "l3_b1_bn1_beta" rho;
            norm_param "l3_b1_b2" rho;
            norm_param "l3_b1_w2" rho;
            norm_param "l3_b1_bn2_gamma" rho;
            norm_param "l3_b1_bn2_beta" rho;
            norm_param "l3_b1_shortcut_b" rho;
            norm_param "l3_b1_shortcut_w" rho;
            norm_param "l3_b1_shortcut_gamma" rho;
            norm_param "l3_b1_shortcut_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l3b2 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l3_b2_b1" rho;
            norm_param "l3_b2_w1" rho;
            norm_param "l3_b2_bn1_gamma" rho;
            norm_param "l3_b2_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l3_b2_b1" rho;
            norm_param "l3_b2_w1" rho;
            norm_param "l3_b2_bn1_gamma" rho;
            norm_param "l3_b2_bn1_beta" rho;
            norm_param "l3_b2_b2" rho;
            norm_param "l3_b2_w2" rho;
            norm_param "l3_b2_bn2_gamma" rho;
            norm_param "l3_b2_bn2_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l4b1 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l4_b1_b1" rho;
            norm_param "l4_b1_w1" rho;
            norm_param "l4_b1_bn1_gamma" rho;
            norm_param "l4_b1_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l4_b1_b1" rho;
            norm_param "l4_b1_w1" rho;
            norm_param "l4_b1_bn1_gamma" rho;
            norm_param "l4_b1_bn1_beta" rho;
            norm_param "l4_b1_b2" rho;
            norm_param "l4_b1_w2" rho;
            norm_param "l4_b1_bn2_gamma" rho;
            norm_param "l4_b1_bn2_beta" rho;
            norm_param "l4_b1_shortcut_b" rho;
            norm_param "l4_b1_shortcut_w" rho;
            norm_param "l4_b1_shortcut_gamma" rho;
            norm_param "l4_b1_shortcut_beta" rho;
            norm_eps rho; exact Hra
          end ].

Ltac block_tac_l4b2 s rho Hrn Hra :=
  first [ xin_fact s | su_fact
        | match goal with
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OB.BatchNorm4d _ _ _ _) _) _) _) _ <= R0)%R =>
            norm_param "l4_b2_b1" rho;
            norm_param "l4_b2_w1" rho;
            norm_param "l4_b2_bn1_gamma" rho;
            norm_param "l4_b2_bn1_beta" rho;
            norm_eps rho; exact Hrn
          | |- forall _ _ _ _, (PCG.idx (PCG.idx (PCG.idx (PCG.idx
                  (OE.Add4d _ _) _) _) _) _ <= R0)%R =>
            norm_param "l4_b2_b1" rho;
            norm_param "l4_b2_w1" rho;
            norm_param "l4_b2_bn1_gamma" rho;
            norm_param "l4_b2_bn1_beta" rho;
            norm_param "l4_b2_b2" rho;
            norm_param "l4_b2_w2" rho;
            norm_param "l4_b2_bn2_gamma" rho;
            norm_param "l4_b2_bn2_beta" rho;
            norm_eps rho; exact Hra
          end ].

Theorem Bridge_ResNet18 : forall (rho : PCG.env) (p : DE.path),
  @PCG.in_acc (ary '{1} (ary '{1000} num)) p
    (@CG.vwt (ary '{1} (ary '{1000} num)) "output") ->
  net_fresh rho ->
  (forall (b : fin 1) (c : fin 64) (i0 i1 : fin 112),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gx2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb11n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb11a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb12n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 64) (i0 i1 : fin 56),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb12a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb21n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb21a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb22n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 128) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb22a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb31n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb31a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb32n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 256) (i0 i1 : fin 14),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb32a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb41n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb41a2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb42n1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 512) (i0 i1 : fin 7),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (Gb42a2 rho) b) c) i0) i1 <= R0)%R) ->
  SEM.eval resnet18_AST rho p =
  RD.resnet18_comm (batch:=1) (channel:=3) (m:=224)
    (Rd _ "input" rho) (Rd _ "conv1_w" rho) (Rd _ "conv1_b" rho)
    (Rd _ "bn1_gamma" rho) (Rd _ "bn1_beta" rho) (Rd num "bn_eps" rho)
    (Rd _ "l1_b1_w1" rho) (Rd _ "l1_b1_b1" rho)
    (Rd _ "l1_b1_bn1_gamma" rho) (Rd _ "l1_b1_bn1_beta" rho)
    (Rd _ "l1_b1_w2" rho) (Rd _ "l1_b1_b2" rho)
    (Rd _ "l1_b1_bn2_gamma" rho) (Rd _ "l1_b1_bn2_beta" rho)
    (Rd _ "l1_b2_w1" rho) (Rd _ "l1_b2_b1" rho)
    (Rd _ "l1_b2_bn1_gamma" rho) (Rd _ "l1_b2_bn1_beta" rho)
    (Rd _ "l1_b2_w2" rho) (Rd _ "l1_b2_b2" rho)
    (Rd _ "l1_b2_bn2_gamma" rho) (Rd _ "l1_b2_bn2_beta" rho)
    (Rd _ "l2_b1_w1" rho) (Rd _ "l2_b1_b1" rho)
    (Rd _ "l2_b1_bn1_gamma" rho) (Rd _ "l2_b1_bn1_beta" rho)
    (Rd _ "l2_b1_w2" rho) (Rd _ "l2_b1_b2" rho)
    (Rd _ "l2_b1_bn2_gamma" rho) (Rd _ "l2_b1_bn2_beta" rho)
    (Rd _ "l2_b1_shortcut_w" rho) (Rd _ "l2_b1_shortcut_b" rho)
    (Rd _ "l2_b1_shortcut_gamma" rho) (Rd _ "l2_b1_shortcut_beta" rho)
    (Rd _ "l2_b2_w1" rho) (Rd _ "l2_b2_b1" rho)
    (Rd _ "l2_b2_bn1_gamma" rho) (Rd _ "l2_b2_bn1_beta" rho)
    (Rd _ "l2_b2_w2" rho) (Rd _ "l2_b2_b2" rho)
    (Rd _ "l2_b2_bn2_gamma" rho) (Rd _ "l2_b2_bn2_beta" rho)
    (Rd _ "l3_b1_w1" rho) (Rd _ "l3_b1_b1" rho)
    (Rd _ "l3_b1_bn1_gamma" rho) (Rd _ "l3_b1_bn1_beta" rho)
    (Rd _ "l3_b1_w2" rho) (Rd _ "l3_b1_b2" rho)
    (Rd _ "l3_b1_bn2_gamma" rho) (Rd _ "l3_b1_bn2_beta" rho)
    (Rd _ "l3_b1_shortcut_w" rho) (Rd _ "l3_b1_shortcut_b" rho)
    (Rd _ "l3_b1_shortcut_gamma" rho) (Rd _ "l3_b1_shortcut_beta" rho)
    (Rd _ "l3_b2_w1" rho) (Rd _ "l3_b2_b1" rho)
    (Rd _ "l3_b2_bn1_gamma" rho) (Rd _ "l3_b2_bn1_beta" rho)
    (Rd _ "l3_b2_w2" rho) (Rd _ "l3_b2_b2" rho)
    (Rd _ "l3_b2_bn2_gamma" rho) (Rd _ "l3_b2_bn2_beta" rho)
    (Rd _ "l4_b1_w1" rho) (Rd _ "l4_b1_b1" rho)
    (Rd _ "l4_b1_bn1_gamma" rho) (Rd _ "l4_b1_bn1_beta" rho)
    (Rd _ "l4_b1_w2" rho) (Rd _ "l4_b1_b2" rho)
    (Rd _ "l4_b1_bn2_gamma" rho) (Rd _ "l4_b1_bn2_beta" rho)
    (Rd _ "l4_b1_shortcut_w" rho) (Rd _ "l4_b1_shortcut_b" rho)
    (Rd _ "l4_b1_shortcut_gamma" rho) (Rd _ "l4_b1_shortcut_beta" rho)
    (Rd _ "l4_b2_w1" rho) (Rd _ "l4_b2_b1" rho)
    (Rd _ "l4_b2_bn1_gamma" rho) (Rd _ "l4_b2_bn1_beta" rho)
    (Rd _ "l4_b2_w2" rho) (Rd _ "l4_b2_b2" rho)
    (Rd _ "l4_b2_bn2_gamma" rho) (Rd _ "l4_b2_bn2_beta" rho)
    (Rd _ "fc_w" rho) (Rd _ "fc_b" rho)
    (@CG.vwt (ary '{1} (ary '{1000} num)) "output") rho p.
(* -------------------------------------------------------------------------- *)
(* The whole-network bridge (main proof)                                     *)
(* -------------------------------------------------------------------------- *)
Proof.
  intros rho p Hinacc Hfresh
    Hr2 Hr11n Hr11a Hr12n Hr12a Hr21n Hr21a Hr22n Hr22a
    Hr31n Hr31a Hr32n Hr32a Hr41n Hr41a Hr42n Hr42a.
  destruct Hfresh as [Htmp HfreshA].
  (* Route-A side: collapse [resnet18_comm] to the functional assignment. *)
  erewrite RD.A_ResNet18; [| exact Hinacc | exact HfreshA ].
  cbv [DR.A]. cbv beta.
  (* Route-B side: 4 stem layers + 8 block rewrites + 3 classifier layers,
     all under the fold discipline; [bb_id_ast]/[bb_proj_ast] stay folded so
     each block collapses in a single rewrite. *)
  unfold resnet18_AST, ast_conv, ast_bn, ast_relu, ast_add.
  assert (SEM.to_pcg_exp (@CG.vrd num "bn_eps") rho = eps_e rho) by exact eq_refl.
  (* ---- stem ---- *)
  (* conv1: 7x7 s2 p3 *)
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Conv4d_ast_comm 3 2
              (CG.vrd "conv1_b") (CG.vrd "conv1_w") (CG.vrd "input")
              (CG.vwt "conv1_out")) ?e] =>
    rewrite (HB_conv4d 1 224 224 7 7 3 64 3 2
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "conv1_b" rho. rw_fact "conv1_b". clear_fact "conv1_b".
  param_fact "conv1_w" rho. rw_fact "conv1_w". clear_fact "conv1_w".
  param_fact "input" rho. rw_fact "input". clear_fact "input".
  fold_and_bump "conv1_out" (Gx1 rho).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEB.BatchNorm4d_comm
              (CG.vrd "conv1_out") (BR2.bn1_mean (CG.vrd "conv1_out"))
              (BR2.bn1_var (CG.vrd "conv1_out"))
              (CG.vrd "bn1_gamma") (CG.vrd "bn1_beta") (CG.vrd "bn_eps")
              (CG.vwt "bn1_out")) ?e] =>
    rewrite (HB_bn 64 112 112 (Nat.lt_0_succ _) _ _ _ _ _ _ _ e)
  end;
  [| reflexivity | reflexivity | str_neq_tac | str_neq_tac | str_neq_tac | str_neq_tac ].
  rw_fact "conv1_out". clear_fact "conv1_out".
  param_fact "bn1_gamma" rho. rw_fact "bn1_gamma". clear_fact "bn1_gamma".
  param_fact "bn1_beta" rho. rw_fact "bn1_beta". clear_fact "bn1_beta".
  rw_fact "bn_eps".
  fold_and_bump "bn1_out" (Gx2 rho).
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.ReLU4d_comm (CG.vrd "bn1_out") (CG.vwt "relu1_out")) ?e] =>
    rewrite (HB_relu 1 64 112 112 _ _ e)
  end;
  [| discriminate | discriminate | str_neq_tac |
     intros b c i0 i1; rw_fact "bn1_out"; exact (Hr2 b c i0 i1) ].
  rw_fact "bn1_out". clear_fact "bn1_out".
  fold_and_bump "relu1_out" (Gx3 rho).
  (* pool1: 3x3 s2 p1 *)
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (BR2.Maxpool4d_pad_ast_comm 3 2 1
              (CG.vrd "relu1_out") (CG.vwt "pool_out")) ?e] =>
    rewrite (HB_maxp 1 64 112 112 3 2 1
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      (ltac:(repeat constructor)) (ltac:(repeat constructor))
      _ _ e)
  end;
  [| str_neq1_tac | str_neq_tac | str_neq1_tac | su_fact ].
  rw_fact "relu1_out". clear_fact "relu1_out".
  fold_and_bump "pool_out" (Gx4 rho).
  (* stage 1, block 1 -> l1_b1_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l1b1 _ (Gx4 rho));
    [| block_tac_l1b1 "pool_out" rho Hr11n Hr11a
     | block_tac_l1b1 "pool_out" rho Hr11n Hr11a
     | block_tac_l1b1 "pool_out" rho Hr11n Hr11a
     | block_tac_l1b1 "pool_out" rho Hr11n Hr11a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l1_b1_b1" rho.
  norm_param "l1_b1_w1" rho.
  norm_param "l1_b1_bn1_gamma" rho.
  norm_param "l1_b1_bn1_beta" rho.
  norm_param "l1_b1_b2" rho.
  norm_param "l1_b1_w2" rho.
  norm_param "l1_b1_bn2_gamma" rho.
  norm_param "l1_b1_bn2_beta" rho.
  norm_eps rho.
  fold_and_bump "l1_b1_out" (Gb11 rho).
  (* stage 1, block 2 -> l1_b2_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l1b2 _ (Gb11 rho));
    [| block_tac_l1b2 "l1_b1_out" rho Hr12n Hr12a
     | block_tac_l1b2 "l1_b1_out" rho Hr12n Hr12a
     | block_tac_l1b2 "l1_b1_out" rho Hr12n Hr12a
     | block_tac_l1b2 "l1_b1_out" rho Hr12n Hr12a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l1_b2_b1" rho.
  norm_param "l1_b2_w1" rho.
  norm_param "l1_b2_bn1_gamma" rho.
  norm_param "l1_b2_bn1_beta" rho.
  norm_param "l1_b2_b2" rho.
  norm_param "l1_b2_w2" rho.
  norm_param "l1_b2_bn2_gamma" rho.
  norm_param "l1_b2_bn2_beta" rho.
  norm_eps rho.
  fold_and_bump "l1_b2_out" (Gb12 rho).
  (* stage 2, block 1 -> l2_b1_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l2b1 _ (Gb12 rho));
    [| block_tac_l2b1 "l1_b2_out" rho Hr21n Hr21a
     | block_tac_l2b1 "l1_b2_out" rho Hr21n Hr21a
     | block_tac_l2b1 "l1_b2_out" rho Hr21n Hr21a
     | block_tac_l2b1 "l1_b2_out" rho Hr21n Hr21a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l2_b1_b1" rho.
  norm_param "l2_b1_w1" rho.
  norm_param "l2_b1_bn1_gamma" rho.
  norm_param "l2_b1_bn1_beta" rho.
  norm_param "l2_b1_b2" rho.
  norm_param "l2_b1_w2" rho.
  norm_param "l2_b1_bn2_gamma" rho.
  norm_param "l2_b1_bn2_beta" rho.
  norm_param "l2_b1_shortcut_b" rho.
  norm_param "l2_b1_shortcut_w" rho.
  norm_param "l2_b1_shortcut_gamma" rho.
  norm_param "l2_b1_shortcut_beta" rho.
  norm_eps rho.
  fold_and_bump "l2_b1_out" (Gb21 rho).
  (* stage 2, block 2 -> l2_b2_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l2b2 _ (Gb21 rho));
    [| block_tac_l2b2 "l2_b1_out" rho Hr22n Hr22a
     | block_tac_l2b2 "l2_b1_out" rho Hr22n Hr22a
     | block_tac_l2b2 "l2_b1_out" rho Hr22n Hr22a
     | block_tac_l2b2 "l2_b1_out" rho Hr22n Hr22a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l2_b2_b1" rho.
  norm_param "l2_b2_w1" rho.
  norm_param "l2_b2_bn1_gamma" rho.
  norm_param "l2_b2_bn1_beta" rho.
  norm_param "l2_b2_b2" rho.
  norm_param "l2_b2_w2" rho.
  norm_param "l2_b2_bn2_gamma" rho.
  norm_param "l2_b2_bn2_beta" rho.
  norm_eps rho.
  fold_and_bump "l2_b2_out" (Gb22 rho).
  (* stage 3, block 1 -> l3_b1_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l3b1 _ (Gb22 rho));
    [| block_tac_l3b1 "l2_b2_out" rho Hr31n Hr31a
     | block_tac_l3b1 "l2_b2_out" rho Hr31n Hr31a
     | block_tac_l3b1 "l2_b2_out" rho Hr31n Hr31a
     | block_tac_l3b1 "l2_b2_out" rho Hr31n Hr31a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l3_b1_b1" rho.
  norm_param "l3_b1_w1" rho.
  norm_param "l3_b1_bn1_gamma" rho.
  norm_param "l3_b1_bn1_beta" rho.
  norm_param "l3_b1_b2" rho.
  norm_param "l3_b1_w2" rho.
  norm_param "l3_b1_bn2_gamma" rho.
  norm_param "l3_b1_bn2_beta" rho.
  norm_param "l3_b1_shortcut_b" rho.
  norm_param "l3_b1_shortcut_w" rho.
  norm_param "l3_b1_shortcut_gamma" rho.
  norm_param "l3_b1_shortcut_beta" rho.
  norm_eps rho.
  fold_and_bump "l3_b1_out" (Gb31 rho).
  (* stage 3, block 2 -> l3_b2_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l3b2 _ (Gb31 rho));
    [| block_tac_l3b2 "l3_b1_out" rho Hr32n Hr32a
     | block_tac_l3b2 "l3_b1_out" rho Hr32n Hr32a
     | block_tac_l3b2 "l3_b1_out" rho Hr32n Hr32a
     | block_tac_l3b2 "l3_b1_out" rho Hr32n Hr32a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l3_b2_b1" rho.
  norm_param "l3_b2_w1" rho.
  norm_param "l3_b2_bn1_gamma" rho.
  norm_param "l3_b2_bn1_beta" rho.
  norm_param "l3_b2_b2" rho.
  norm_param "l3_b2_w2" rho.
  norm_param "l3_b2_bn2_gamma" rho.
  norm_param "l3_b2_bn2_beta" rho.
  norm_eps rho.
  fold_and_bump "l3_b2_out" (Gb32 rho).
  (* stage 4, block 1 -> l4_b1_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l4b1 _ (Gb32 rho));
    [| block_tac_l4b1 "l3_b2_out" rho Hr41n Hr41a
     | block_tac_l4b1 "l3_b2_out" rho Hr41n Hr41a
     | block_tac_l4b1 "l3_b2_out" rho Hr41n Hr41a
     | block_tac_l4b1 "l3_b2_out" rho Hr41n Hr41a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l4_b1_b1" rho.
  norm_param "l4_b1_w1" rho.
  norm_param "l4_b1_bn1_gamma" rho.
  norm_param "l4_b1_bn1_beta" rho.
  norm_param "l4_b1_b2" rho.
  norm_param "l4_b1_w2" rho.
  norm_param "l4_b1_bn2_gamma" rho.
  norm_param "l4_b1_bn2_beta" rho.
  norm_param "l4_b1_shortcut_b" rho.
  norm_param "l4_b1_shortcut_w" rho.
  norm_param "l4_b1_shortcut_gamma" rho.
  norm_param "l4_b1_shortcut_beta" rho.
  norm_eps rho.
  fold_and_bump "l4_b1_out" (Gb41 rho).
  (* stage 4, block 2 -> l4_b2_out *)
  rewrite BL.eval_seq'.
  rewrite (bridge_bb_l4b2 _ (Gb41 rho));
    [| block_tac_l4b2 "l4_b1_out" rho Hr42n Hr42a
     | block_tac_l4b2 "l4_b1_out" rho Hr42n Hr42a
     | block_tac_l4b2 "l4_b1_out" rho Hr42n Hr42a
     | block_tac_l4b2 "l4_b1_out" rho Hr42n Hr42a ].
  (* Normalize the deposited chain's parameter reads back to [rho]. *)
  norm_param "l4_b2_b1" rho.
  norm_param "l4_b2_w1" rho.
  norm_param "l4_b2_bn1_gamma" rho.
  norm_param "l4_b2_bn1_beta" rho.
  norm_param "l4_b2_b2" rho.
  norm_param "l4_b2_w2" rho.
  norm_param "l4_b2_bn2_gamma" rho.
  norm_param "l4_b2_bn2_beta" rho.
  norm_eps rho.
  fold_and_bump "l4_b2_out" (Gb42 rho).

  (* ---- classifier ---- *)
  (* avgpool *)
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.GlobalAvgPool4d_comm
              (CG.vrd "l4_b2_out") (CG.vwt "avgpool_out")) ?e] =>
    rewrite (HB_gap 1 512 7 7
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      _ _ e)
  end;
  [| str_neq1_tac | str_neq_tac | str_neq1_tac | su_fact ].
  rw_fact "l4_b2_out". clear_fact "l4_b2_out".
  fold_and_bump "avgpool_out" (@OR.GlobalAvgPool4d 1 512 7 7 (Gb42 rho)).
  (* fc *)
  rewrite BL.eval_seq'.
  match goal with
  |- context [SEM.eval (CEO.Linear2d_comm
              (CG.vrd "fc_w") (CG.vrd "fc_b") (CG.vrd "avgpool_out")
              (CG.vwt "fc_out")) ?e] =>
    rewrite (HB_linear 1 512 1000
      (Nat.lt_0_succ _) (Nat.lt_0_succ _) (Nat.lt_0_succ _)
      _ _ _ _ e)
  end;
  [| str_neq1_tac | str_neq1_tac | str_neq1_tac |
     str_neq_tac | str_neq_tac | str_neq_tac | str_neq1_tac | su_fact ].
  param_fact "fc_w" rho. rw_fact "fc_w". clear_fact "fc_w".
  param_fact "fc_b" rho. rw_fact "fc_b". clear_fact "fc_b".
  rw_fact "avgpool_out". clear_fact "avgpool_out".
  fold_and_bump "fc_out"
    (@OP.Linear2d 1 512 1000 (Rd _ "fc_w" rho) (Rd _ "fc_b" rho)
       (@OR.GlobalAvgPool4d 1 512 7 7 (Gb42 rho))).
  (* output: softmax *)
  match goal with
  |- context [SEM.eval (CEO.Softmax2d_comm (CG.vrd "fc_out") (CG.vwt "output")) ?e] =>
    rewrite (HB_softmax 1 1000 (Nat.lt_0_succ _) (Nat.lt_0_succ _) _ _ e)
  end;
  [| str_neq1_tac | str_neq_tac | str_neq1_tac | su_fact ].
  rw_fact "fc_out".
  (* Observe at [p] inside the output buffer, fold the route-B value into
     [Gout], and close by the whole-network value equality (B1) instead of
     a kernel conversion over the fully nested term. *)
  rewrite (SEM.assign_in_acc_independent_of_env _ _ _ _ rho _ Hinacc).
  rewrite <- Gout_body.
  rewrite resnet18_out_eq.
  exact eq_refl.
Qed.

Print Assumptions Bridge_ResNet18.
