(* ========================================================================= *)
(* Bridge_AlexNet.v                                                          *)
(*                                                                           *)
(* Whole-network route-A/route-B bridge for AlexNet (classic 5-conv + 3-fc   *)
(* structure), following the [Bridge_LeNet5] template:                       *)
(*                                                                           *)
(*   eval (AST-level AlexNet) rho p  =  alexnet_comm (route A) ... rho p     *)
(*                                                                           *)
(* pointwise at every path [p] inside the output accumulator.                *)
(*                                                                           *)
(* Route B (code generation): the concrete repo AST nets                     *)
(*   ([CNN_Examples_AlexNet], [CNN_Examples_MiniAlexNet]) are mini variants  *)
(*   (CIFAR-style 2-conv blocks + 2 fc), NOT the classic AlexNet of route A. *)
(*   This file therefore ASSEMBLES the classic structure from the bridged    *)
(*   per-layer AST commands, mirroring [AlexNet_DPIA.AlexNet] layer by       *)
(*   layer at batch = 1, channel = 3, input 224x224:                         *)
(*     conv1(11x11,p2,s4)-relu-pool1(3x3,s2)                                 *)
(*     conv2(5x5,p2,s1)-relu-pool2(3x3,s2)                                   *)
(*     conv3(3x3,p1,s1)-relu  conv4(3x3,p1,s1)-relu                          *)
(*     conv5(3x3,p1,s1)-relu-pool5(3x3,s2)                                   *)
(*     flatten - fc1(4096)-relu - fc2(4096)-relu - fc3(1000) - softmax       *)
(*   using [Bridge_ReduceConv2.Conv4d_ast_comm] (the new general AST conv),  *)
(*   [CNN_Examples_Base_Ops.ReLU4d_comm]/[Linear2d_comm]/[Softmax2d_comm],   *)
(*   [Bridge_ReduceConv2.Maxpool4d_pad_ast_comm],                            *)
(*   [CNN_Examples_Base.Flatten4d_comm] and                                  *)
(*   [CNN_Examples_Base.ReLU2d_comm], writing the named buffers              *)
(*   "c1" "r1" "p1" "c2" "r2" "p2" "c3" "r3" "c4" "r4" "c5" "r5" "p5"        *)
(*   "flat" "fc1" "fc1r" "fc2" "fc2r" "fc3" "output".                        *)
(* Route A (DPIA): [AlexNet_DPIA.alexnet_comm] with its proved whole-        *)
(*   network collapse [AlexNet_DPIA.A_AlexNet].                              *)
(*                                                                           *)
(* As in [Bridge_LeNet5], the operator bridges universally quantify the      *)
(*   output acceptor in their independence side conditions (e.g.             *)
(*   [Bridge_ReduceConv2.Conv4d_sem], [Operators_Sem_Equiv.Linear2d_sem]),   *)
(*   which is unsatisfiable for buffer-read inputs.  This file therefore     *)
(*   re-proves single-output variants                                        *)
(*   ([Conv4d_sem_single], [Maxpool4d_pad_sem_single],                       *)
(*   [Linear2d_sem_single], [Softmax2d_sem_single], [Flatten4d_sem_single])  *)
(*   by replaying the original proofs with the universally quantified        *)
(*   independence premises replaced by the concrete ones; the heavy          *)
(*   machinery (sum/max flattening, continuation lemmas, padding             *)
(*   independence, index encode/decode) is reused from                       *)
(*   [Bridge_ReduceConv2] and [Operators_Sem_Equiv], and the functional      *)
(*   interpretation lemmas from [Bridge_ReduceConv2]/[Bridge_Elementwise]    *)
(*   (plus three new ones: [interp_ReLU2d], [interp_Linear2d],               *)
(*   [interp_Softmax2d]).                                                    *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

From Stdlib Require Import Reals String Arith Lia Bool.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.
Require Import Ionia.finType Ionia.vector Ionia.DataExp Ionia.CNN_Defs
  Ionia.CNN_CodeGen_Core Ionia.Proof_CodeGen Ionia.DPIA_Rules
  Ionia.CNN_CodeGen_Semantics Ionia.CNN_Examples_Base
  Ionia.CNN_Examples_Base_Ops Ionia.CNN_OP Ionia.Operators_Sem_Equiv
  Ionia.LeNet5_Functional Ionia.FusionTactics Ionia.Bridge_ReduceConv.
Require Ionia.Ops_Conv Ionia.Ops_Elementwise Ionia.Ops_PoolPad Ionia.Ops_Reduce
  Ionia.AlexNet_DPIA Ionia.Bridge_Elementwise Ionia.Bridge_ReduceConv2.

Open Scope string_scope.

(* See [Bridge_LeNet5]: the buffer name types are local [Definition]s, so the
   whole-file matching below relies on keyed unification. *)
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
Module V := Ionia.vector.
Module BRC := Ionia.Bridge_ReduceConv.
Module FTac := Ionia.FusionTactics.
Module OC := Ionia.Ops_Conv.
Module OE := Ionia.Ops_Elementwise.
Module OP := Ionia.Ops_PoolPad.
Module OR := Ionia.Ops_Reduce.
Module AD := Ionia.AlexNet_DPIA.
Module BEL := Ionia.Bridge_Elementwise.
Module BRC2 := Ionia.Bridge_ReduceConv2.

(* Variable lookup used by [SEM.to_pcg_exp] and [SEM.eval]. *)
Definition env_val (rho : PCG.env) (s : string) : R :=
  match rho (DE.Var s) with Some r => r | None => R0 end.

(* -------------------------------------------------------------------------- *)
(* Generic interpretation helpers (mirrors of the [Bridge_Pilot] helpers)     *)
(* -------------------------------------------------------------------------- *)

Lemma to_pcg_exp_BLe : forall (x y : DE.exp num) (rho : PCG.env),
  DE.eval_bexp (env_val rho) (CD.leExp x y) =
  PCG.leExp (SEM.to_pcg_exp x rho) (SEM.to_pcg_exp y rho).
Proof.
  intros x y rho. cbv [SEM.to_pcg_exp CD.leExp env_val PCG.leExp].
  simpl. reflexivity.
Qed.

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
(* Buffer name infrastructure (verbatim from [Bridge_LeNet5])                 *)
(* -------------------------------------------------------------------------- *)

Lemma in_acc_vwt_bracket : forall (n : nat) (f : fle n) (d : data)
  (p : DE.path) (s : string),
  @PCG.in_acc (ary f d) p (@CG.vwt (ary f d) s) ->
  exists u : string, p = DE.Var (s ++ "[" ++ u)%string.
Proof.
  intros n f d p s Hin.
  rewrite SEM.vwt_ary in Hin. simpl in Hin. destruct Hin as [i Hi].
  rewrite SEM.PCG_idxAcc_mk_vec in Hi.
  destruct (SEM.in_acc_vwt _ _ _ Hi) as [w Hw]. subst p.
  exists ((writeNat (fin2nat i) ++ "]") ++ w)%string.
  f_equal. rewrite SEM.append_assoc_str. reflexivity.
Qed.

Lemma vrd_after_other_vwt_ary : forall (n : nat) (f : fle n) (d : data)
  (si t : string),
  (forall u v : string, (si ++ "[" ++ u <> t ++ v)%string) ->
  forall (v : PCG.exp (ary f d)) (rho : PCG.env),
    SEM.to_pcg_exp (@CG.vrd (ary f d) t)
      (PCG.assign (@CG.vwt (ary f d) si) v rho) =
    SEM.to_pcg_exp (@CG.vrd (ary f d) t) rho.
Proof.
  intros n f d si t Hdiv v rho.
  apply (@SEM.exp_independent_of_acc_eval (ary f d) (ary f d)
           (@CG.vrd (ary f d) t) (@CG.vwt (ary f d) si)).
  - intros p Hp. destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply SEM.exp_indep_vrd_Var. intros w Hw.
    exact (Hdiv u w (eq_sym Hw)).
  - intros q Hq. apply PCG.assign_not_in_acc. exact Hq.
Qed.

Lemma exp_indep_vrd_ary_Var : forall (n : nat) (f : fle n) (d : data)
  (t q : string),
  (forall v : string, (t ++ "[" ++ v <> q)%string) ->
  @SEM.exp_independent_of_path (ary f d) (@CG.vrd (ary f d) t) (DE.Var q).
Proof.
  intros n f d. revert n f.
  induction d as [| n' f' d' IHd]; intros n f t q Hdiv.
  - rewrite SEM.vrd_ary. simpl. intro i.
    rewrite V.v_nth_mk_vec with (H := fin_proof i).
    rewrite nat2fin_fin2nat.
    rewrite SEM.vrd_num. simpl.
    destruct (String.eqb _ "0") eqn:E0; [exact I|].
    destruct (String.eqb _ "1") eqn:E1; [exact I|].
    intro Heq. injection Heq as Heq.
    apply (Hdiv (writeNat (fin2nat i) ++ "]")%string).
    exact Heq.
  - rewrite SEM.vrd_ary. simpl. intro i.
    rewrite V.v_nth_mk_vec with (H := fin_proof i).
    rewrite nat2fin_fin2nat.
    apply (IHd n' f'). intros v Hv.
    apply (Hdiv (writeNat (fin2nat i) ++ "]" ++ "[" ++ v)%string).
    rewrite <- (SEM.append_assoc_str (writeNat (fin2nat i)) "]" ("[" ++ v)%string).
    rewrite SEM.append_assoc_str in Hv. exact Hv.
Qed.

Lemma vrd_after_other_vwt_ary_gen : forall (n1 : nat) (f1 : fle n1) (d1 : data)
  (n2 : nat) (f2 : fle n2) (d2 : data) (si t : string),
  (forall u v : string, (si ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  forall (v : PCG.exp (ary f2 d2)) (rho : PCG.env),
    SEM.to_pcg_exp (@CG.vrd (ary f1 d1) t)
      (PCG.assign (@CG.vwt (ary f2 d2) si) v rho) =
    SEM.to_pcg_exp (@CG.vrd (ary f1 d1) t) rho.
Proof.
  intros n1 f1 d1 n2 f2 d2 si t Hdiv v rho.
  apply (@SEM.exp_independent_of_acc_eval (ary f1 d1) (ary f2 d2)
           (@CG.vrd (ary f1 d1) t) (@CG.vwt (ary f2 d2) si)).
  - intros p Hp. destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hdiv u w (eq_sym Hw)).
  - intros q Hq. apply PCG.assign_not_in_acc. exact Hq.
Qed.

Lemma SU_tmp_after_assign_vwt : forall (n : nat) (f : fle n) (d : data)
  (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (v : PCG.exp (ary f d)) (rho : PCG.env),
    @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
    @PCG.StructUndefined num (PCG.acc' OSE.tmp_path)
      (PCG.assign (@CG.vwt (ary f d) s) v rho).
Proof.
  intros n f d s Hneq v rho H.
  change ((PCG.assign (@CG.vwt (ary f d) s) v rho) (@PCG.acc' num OSE.tmp_path)
            = None).
  rewrite PCG.assign_not_in_acc.
  - exact H.
  - intro Hin. destruct (in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
    simpl in Heq. injection Heq as Heq. exact (Hneq u Heq).
Qed.

Lemma eval_seq' : forall (c1 c2 : CG.comm) (rho : PCG.env),
  SEM.eval (CG.seq (c1, c2)) rho = SEM.eval c2 (SEM.eval c1 rho).
Proof. intros. reflexivity. Qed.

Ltac str_neq_tac := intros u v Heq; discriminate.
Ltac str_neq1_tac := intros u Heq; discriminate.
Ltac str_neq2_tac := intros u v Heq; discriminate.

Ltac su_tmp_tac :=
  repeat (apply SU_tmp_after_assign_vwt; [ intros u Heq; discriminate | ]);
  assumption.

Lemma to_pcg_exp_vrd_env_empty : forall (d : data) (s : string),
  (s <> "0")%string -> (s <> "1")%string ->
  SEM.to_pcg_exp (@CG.vrd d s) PCG.env_empty = PCG.exp_default d.
Proof.
  induction d as [| n f d IHd]; intros s Hs0 Hs1.
  - rewrite SEM.vrd_num.
    rewrite (proj2 (String.eqb_neq s "0") Hs0).
    rewrite (proj2 (String.eqb_neq s "1") Hs1).
    rewrite SEM.to_pcg_exp_REvar. reflexivity.
  - rewrite SEM.vrd_ary, SEM.to_pcg_exp_ary.
    cbn [PCG.exp_default]. unfold PCG.mkvSeq.
    apply V.mk_vec_ext. intro i.
    rewrite V.v_nth_mk_vec with (H := fin_proof i).
    rewrite nat2fin_fin2nat.
    apply IHd.
    + apply SEM.indexed_name_neq_0.
    + apply SEM.indexed_name_neq_1.
Qed.

Lemma PCG_idx_exp_default : forall (n : nat) (d : data) (i : fin n),
  PCG.idx (PCG.exp_default (ary '{n} d)) i = PCG.exp_default d.
Proof.
  intros n d i. cbn [PCG.exp_default]. unfold PCG.mkvSeq, PCG.idx.
  apply V.v_idx_mk_vec.
Qed.

Lemma in_acc_acc'_Var : forall (d : data) (q : DE.path) (s : string),
  @PCG.in_acc d (DE.Var s) (@PCG.acc' d q) -> q = DE.Var s.
Proof.
  induction d as [| n f d IHd]; intros q s Hin.
  - exact Hin.
  - simpl in Hin. destruct Hin as [i Hi].
    rewrite SEM.PCG_idxAcc_mk_vec in Hi.
    apply IHd in Hi. discriminate.
Qed.

Lemma in_acc_tmp_scalar : forall p : DE.path,
  @PCG.in_acc num p OSE.tmp_scalar_acc -> p = OSE.tmp_path.
Proof. intros p Hp. exact (eq_sym Hp). Qed.

Lemma vrd_ary_indep_tmp : forall (n : nat) (f : fle n) (d : data) (s : string),
  (forall u : string, (s ++ "[" ++ u <> "__tmp")%string) ->
  @SEM.exp_independent_of_acc (ary f d) num (@CG.vrd (ary f d) s) OSE.tmp_scalar_acc.
Proof.
  intros n f d s Hneq p Hp. apply in_acc_tmp_scalar in Hp. subst p.
  apply exp_indep_vrd_ary_Var. exact Hneq.
Qed.

Lemma vrd_ary_indep_vwt_ary : forall (n1 : nat) (f1 : fle n1) (d1 : data)
  (n2 : nat) (f2 : fle n2) (d2 : data) (s t : string),
  (forall u v : string, (s ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  @SEM.exp_independent_of_acc (ary f1 d1) (ary f2 d2)
    (@CG.vrd (ary f1 d1) s) (@CG.vwt (ary f2 d2) t).
Proof.
  intros n1 f1 d1 n2 f2 d2 s t Hdiv p Hp.
  destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
  apply exp_indep_vrd_ary_Var. intros w Hw.
  exact (Hdiv w u Hw).
Qed.

(* tmp disjointness of a 2d output buffer (linear2d/softmax2d/flatten4d) *)
Lemma tmp_disj_vwt2 : forall (n1 n2 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (b : fin n1) (out : fin n2),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p ((@CG.vwt (ary '{n1} (ary '{n2} num)) s) |{ b} |{ out}).
Proof.
  intros n1 n2 s Hneq p b out Hp Hin.
  apply in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

(* tmp disjointness of a 4d output buffer (conv4d/maxpool4d_pad shape) *)
Lemma tmp_disj_vwt4 : forall (n1 n2 n3 n4 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (b : fin n1) (nu : fin n2) (i0 : fin n3) (j0 : fin n4),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p
        ((@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} (ary '{n4} num)))) s)
           |{ b} |{ nu} |{ i0} |{ j0}).
Proof.
  intros n1 n2 n3 n4 s Hneq p b nu i0 j0 Hp Hin.
  apply in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

(* -------------------------------------------------------------------------- *)
(* Functional interpretation lemmas: ReLU2d / Linear2d / Softmax2d            *)
(* (route-B [CNN_OP] expression -> route-A [LeNet5_Functional]/[Ops_PoolPad]/ *)
(*  [Ops_Reduce] expression under [to_pcg_exp])                               *)
(* -------------------------------------------------------------------------- *)

Lemma interp_ReLU2d : forall (m1 m2 : nat)
  (input : DE.exp (ary '{m1} (ary '{m2} num))) (rho : PCG.env),
  (forall (i0 : fin m1) (i1 : fin m2),
     DE.eval_bexp (env_val rho) (CD.leExp (DE.idx (DE.idx input i0) i1) CD.zero) =
     DE.bexp2bool (CD.leExp (DE.idx (DE.idx input i0) i1) CD.zero)) ->
  SEM.to_pcg_exp (COP.ReLU2d input) rho =
  LF.ReLU2d (SEM.to_pcg_exp input rho).
Proof.
  intros m1 m2 input rho Hb.
  unfold COP.ReLU2d, LF.ReLU2d.
  apply to_pcg_mkvSeq_ext; intro i0.
  apply to_pcg_mkvSeq_ext; intro i1.
  rewrite <- (Hb i0 i1).
  remember (DE.eval_bexp (env_val rho) (CD.leExp (DE.idx (DE.idx input i0) i1) CD.zero)) as b eqn:E.
  rewrite to_pcg_exp_BLe in E.
  rewrite SEM.to_pcg_exp_zero in E.
  repeat rewrite SEM.to_pcg_exp_idx in E.
  unfold PCG.zero.
  destruct b; rewrite <- E.
  - reflexivity.
  - repeat rewrite SEM.to_pcg_exp_idx. reflexivity.
Qed.

Lemma interp_Linear2d : forall (batch m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Linear2d w b input) rho =
  OP.Linear2d (SEM.to_pcg_exp w rho) (SEM.to_pcg_exp b rho)
    (SEM.to_pcg_exp input rho).
Proof.
  intros batch m outnum w b input rho.
  unfold COP.Linear2d, OP.Linear2d.
  apply to_pcg_mkvSeq_ext; intro bi.
  apply to_pcg_mkvSeq_ext; intro out.
  rewrite OSE.to_pcg_exp_add, BRC.to_pcg_sum_mkvSeq, SEM.to_pcg_exp_idx.
  apply f_equal2; [ | reflexivity ].
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_mul.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

Lemma interp_Softmax2d : forall (batch m : nat) (Hb : batch > 0)
  (input : DE.exp (ary '{batch} (ary '{m} num))) (rho : PCG.env),
  SEM.to_pcg_exp (COP.Softmax2d input) rho =
  OR.Softmax2d (SEM.to_pcg_exp input rho).
Proof.
  intros batch m Hb input rho.
  unfold COP.Softmax2d, OR.Softmax2d. cbv [CD.let_binding]. cbv beta.
  apply to_pcg_mkvSeq_ext; intro b.
  apply to_pcg_mkvSeq_ext; intro j.
  rewrite OSE.to_pcg_exp_div, OSE.to_pcg_exp_pExp.
  repeat rewrite SEM.to_pcg_exp_idx.
  apply f_equal2; [ reflexivity | ].
  rewrite SEM.to_pcg_exp_mkvSeq.
  rewrite (PCG.idx_mkvSeq _ _ _ Hb). cbv beta.
  rewrite BRC.to_pcg_sum_mkvSeq.
  apply f_equal. apply V.mk_vec_ext; intro i.
  rewrite OSE.to_pcg_exp_pExp.
  repeat rewrite SEM.to_pcg_exp_idx.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* ReLU layer bridges between named buffers (4d and 2d versions of the        *)
(* [Bridge_LeNet5] ReLU bridges)                                              *)
(* -------------------------------------------------------------------------- *)

Lemma bridge_ReLU4d_buf : forall {batch channel m1 m2 : nat} (sin sout : string)
  (eta : PCG.env),
  (sin <> "0")%string -> (sin <> "1")%string ->
  (forall u v : string, (sout ++ "[" ++ u <> sin ++ "[" ++ v)%string) ->
  (forall (b : fin batch) (c : fin channel) (i0 : fin m1) (i1 : fin m2),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx
        (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin) eta)
        b) c) i0) i1 <= R0)%R) ->
  SEM.eval
    (@CEO.ReLU4d_comm batch channel m1 m2
       (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin)
       (@CG.vwt (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sout)) eta =
  PCG.assign (@CG.vwt (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sout)
    (OE.ReLU4d
      (SEM.to_pcg_exp (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin) eta))
    eta.
Proof.
  intros batch channel m1 m2 sin sout eta Hs0 Hs1 Hnames Hle.
  assert (Hb : forall (b : fin batch) (c : fin channel) (i0 : fin m1) (i1 : fin m2),
    DE.eval_bexp (env_val eta)
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin) b) c) i0) i1) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin) b) c) i0) i1) CD.zero)).
  { intros b c i0 i1.
    rewrite (to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin) b) c) i0) i1) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (DE.idx (DE.idx (DE.idx
          (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin) b) c) i0) i1)
          PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (env_val PCG.env_empty) by reflexivity.
      apply to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite !PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle b c i0 i1).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sin)
    (@CG.vwt (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) sout)).
  { intros p Hp. destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEO.ReLU4d_equiv_sem eta Hindep Hb).
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
    (LF.ReLU2d
      (SEM.to_pcg_exp (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) eta))
    eta.
Proof.
  intros m1 m2 sin sout eta Hs0 Hs1 Hnames Hle.
  assert (Hb : forall (i0 : fin m1) (i1 : fin m2),
    DE.eval_bexp (env_val eta)
      (CD.leExp (DE.idx (DE.idx
        (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx
        (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1) CD.zero)).
  { intros i0 i1.
    rewrite (to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx
        (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (DE.idx
          (@CG.vrd (ary '{m1} (ary '{m2} num)) sin) i0) i1)
          PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (env_val PCG.env_empty) by reflexivity.
      apply to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite !PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle i0 i1).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{m1} (ary '{m2} num)) sin)
    (@CG.vwt (ary '{m1} (ary '{m2} num)) sout)).
  { intros p Hp. destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEB.ReLU2d_equiv_sem eta Hindep Hb).
  cbv [CG.A]. rewrite SEM.eval_assign.
  f_equal. apply interp_ReLU2d. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv4d: single-output semantic equivalence                                 *)
(* (replay of [Bridge_ReduceConv2.Conv4d_sem] with the universally            *)
(*  quantified output-independence premises replaced by the concrete ones)    *)
(* -------------------------------------------------------------------------- *)

Lemma conv4d_cell_indep_single : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (bias : DE.exp (ary '{filernum} num))
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum}
    (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc bias output ->
  forall (b : fin batch) (nu : fin filernum)
    (i0 : fin ((m1 - n1 + 2 * p) / s + 1)) (j0 : fin ((m2 - n2 + 2 * p) / s + 1)),
  SEM.exp_independent_of_acc
    (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel =>
      (CD.sum (DE.mkvSeq (fun i1 : fin n1 =>
        (CD.sum (DE.mkvSeq (fun j1 : fin n2 =>
          BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input
            b nu i0 j0 ch i1 j1)))))))))
      (DE.idx bias nu))
    output.
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s bias w input output Hio Hwo Hbo
    b nu i0 j0.
  apply SEM.exp_independent_of_acc_add.
  - apply OSE.exp_independent_of_acc_sum; intro ch.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold BRC2.conv4d_idx_cell.
    apply SEM.exp_independent_of_acc_mul.
    + repeat apply OSE.safe_idx_nat_independent.
      apply SEM.exp_independent_of_acc_idx.
      apply SEM.exp_independent_of_acc_idx.
      apply BRC2.Padding4d_independent.
      exact Hio.
    + repeat apply SEM.exp_independent_of_acc_idx.
      exact Hwo.
  - apply SEM.exp_independent_of_acc_idx.
    exact Hbo.
Qed.

Theorem Conv4d_sem_single : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hs : s > 0) (Hbatch : batch > 0) (Hchannel : channel > 0)
  (Hfilernum : filernum > 0) (Hn1 : n1 > 0) (Hn2 : n2 > 0)
  (bias : DE.exp (ary '{filernum} num))
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum}
    (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc bias OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc bias output ->
  BRC2.tmp_disjoint_from_output_conv4d batch m1 m2 n1 n2 filernum p s output ->
  forall (rho : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Conv4d p s bias w input)) rho =
  SEM.eval (BRC2.Conv4d_ast_comm p s bias w input output) rho.
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s Hs Hbatch Hchannel Hfilernum Hn1 Hn2
    bias w input output Hi Hw Hbias Hio Hwo Hbo Hdisj rho Hundef.
  unfold CG.A, COP.Conv4d, CD.let_binding, BRC2.Conv4d_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
        DE.mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
          CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply (conv4d_cell_indep_single batch m1 m2 n1 n2 channel filernum p s bias w input output Hio Hwo Hbo). }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - assert (Hcell_b : forall nu i0 j0,
      SEM.exp_independent_of_acc
        (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
        (output |{ b})).
    { intros nu i0 j0 p0 Hp.
      apply (conv4d_cell_indep_single batch m1 m2 n1 n2 channel filernum p s bias w input output Hio Hwo Hbo).
      apply SEM.in_acc_ary_inv with (i := b).
      exact Hp. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros nu;
      apply SEM.exp_independent_of_acc_mkvSeq; intros i0;
      apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_b ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros nu eta' HPeta'. split.
    + assert (Hcell_nu : forall i0 j0,
        SEM.exp_independent_of_acc
          (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
          ((output |{ b}) |{ nu})).
      { intros i0 j0 p0 Hp.
        apply (conv4d_cell_indep_single batch m1 m2 n1 n2 channel filernum p s bias w input output Hio Hwo Hbo).
        apply SEM.in_acc_ary_inv with (i := b).
        apply SEM.in_acc_ary_inv with (i := nu).
        exact Hp. }
      rewrite SEM.eval_mkvSeq; [ | intros i0;
        apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_nu ].
      rewrite !SEM.eval_seqfor.
      apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros i0 eta'' HPeta''. split.
      * assert (Hcell_i0 : forall j0,
          SEM.exp_independent_of_acc
            (CD.add (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1))))))) (DE.idx bias nu))
            (((output |{ b}) |{ nu}) |{ i0})).
        { intros j0 p0 Hp.
          apply (conv4d_cell_indep_single batch m1 m2 n1 n2 channel filernum p s bias w input output Hio Hwo Hbo).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
          exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- set (e := DE.mkvSeq ((BRC2.conv4d_flat_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0)).
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
                    by (unfold e, BRC2.conv4d_flat_cell, DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec; reflexivity);
                  rewrite Heq; reflexivity). }
           rewrite SEM.eval_assign.
           rewrite <- (SEM.eval_assign_aux 1 num _ _ eta''').
           change (SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval (@CG.loopacc num (fun tmp : string =>
             (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * n1 * n2) =>
               CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp))) eta''').
           assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1))))))) eta''' =
             SEM.to_pcg_exp (CD.sum e) eta''').
           { unfold e.
             apply (BRC2.conv4d_sum_flatten batch m1 m2 n1 n2 channel filernum p s
               w input Hs Hbatch Hchannel Hfilernum Hn1 Hn2). }
           assert (Heq_aux : SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun ch : fin channel => CD.sum (DE.mkvSeq (fun i1 : fin n1 => CD.sum (DE.mkvSeq (fun j1 : fin n2 => (BRC2.conv4d_idx_cell batch m1 m2 n1 n2 channel filernum p s w input) b nu i0 j0 ch i1 j1)))))))) 1 eta''' =
             SEM.eval_aux (c (CD.sum e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal.
             rewrite !OSE.to_pcg_exp_add. f_equal.
             { exact Hsum_eq. } }
           rewrite Heq_aux.
           apply SEM.eval_csum_equiv.
           ++ exact HPeta'''.
           ++ unfold e, BRC2.conv4d_flat_cell.
              apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              apply SEM.exp_independent_of_acc_mul.
              ** repeat apply OSE.safe_idx_nat_independent.
                 apply SEM.exp_independent_of_acc_idx.
                 apply SEM.exp_independent_of_acc_idx.
                 apply BRC2.Padding4d_independent.
                 exact Hi.
              ** repeat apply SEM.exp_independent_of_acc_idx.
                 exact Hw.
           ++ apply BRC2.conv4d_cell_continuation_ok; assumption.
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

(* -------------------------------------------------------------------------- *)
(* Maxpool4d_pad: single-output semantic equivalence                          *)
(* -------------------------------------------------------------------------- *)

Lemma maxp4dp_cell_indep_single : forall (batch filernum m1 m2 kersize stride padding : nat)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum}
    (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
    (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))),
  SEM.exp_independent_of_acc input output ->
  forall (b : fin batch) (nu : fin filernum)
    (i0 : fin ((m1 - kersize + 2 * padding) / stride + 1))
    (j0 : fin ((m2 - kersize + 2 * padding) / stride + 1)),
  SEM.exp_independent_of_acc
    (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize =>
      CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu])
        (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
    output.
Proof.
  intros batch filernum m1 m2 kersize stride padding input output Hio b nu i0 j0.
  apply OSE.exp_independent_of_acc_max; intro i1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  apply OSE.exp_independent_of_acc_max; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
  repeat apply OSE.safe_idx_nat_independent.
  apply SEM.exp_independent_of_acc_idx.
  apply SEM.exp_independent_of_acc_idx.
  apply BRC2.Padding4d_independent.
  exact Hio.
Qed.

Theorem Maxpool4d_pad_sem_single : forall
  (batch filernum m1 m2 kersize stride padding : nat)
  (Hs : stride > 0) (Hbatch : batch > 0) (Hfilernum : filernum > 0) (Hk : kersize > 0)
  (input : DE.exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{filernum}
    (ary '{((m1 - kersize + 2 * padding) / stride + 1)}
    (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  BRC2.tmp_disjoint_from_output_maxp4dp batch filernum m1 m2 kersize stride padding output ->
  forall (rho : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, BRC2.maxp4dp_exp kersize stride padding input)) rho =
  SEM.eval (BRC2.Maxpool4d_pad_ast_comm kersize stride padding input output) rho.
Proof.
  intros batch filernum m1 m2 kersize stride padding Hs Hbatch Hfilernum Hk
    input output Hi Hio Hdisj rho Hundef.
  unfold CG.A, BRC2.maxp4dp_exp, CD.let_binding, BRC2.Maxpool4d_pad_ast_comm. cbv beta.
  set (row := fun b : fin batch =>
    DE.mkvSeq (fun nu : fin filernum =>
      DE.mkvSeq (fun i0 : fin ((m1 - kersize + 2 * padding) / stride + 1) =>
        DE.mkvSeq (fun j0 : fin ((m2 - kersize + 2 * padding) / stride + 1) =>
          CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))))).
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro nu.
    apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply (maxp4dp_cell_indep_single batch filernum m1 m2 kersize stride padding input output Hio). }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - assert (Hcell_b : forall (nu : fin filernum)
        (i0 : fin ((m1 - kersize + 2 * padding) / stride + 1))
        (j0 : fin ((m2 - kersize + 2 * padding) / stride + 1)),
      SEM.exp_independent_of_acc
        (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
        (output |{ b})).
    { intros nu i0 j0 p0 Hp.
      apply (maxp4dp_cell_indep_single batch filernum m1 m2 kersize stride padding input output Hio).
      apply SEM.in_acc_ary_inv with (i := b).
      exact Hp. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros nu;
      apply SEM.exp_independent_of_acc_mkvSeq; intros i0;
      apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_b ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros nu eta' HPeta'. split.
    + assert (Hcell_nu : forall (i0 : fin ((m1 - kersize + 2 * padding) / stride + 1))
          (j0 : fin ((m2 - kersize + 2 * padding) / stride + 1)),
        SEM.exp_independent_of_acc
          (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
          ((output |{ b}) |{ nu})).
      { intros i0 j0 p0 Hp.
        apply (maxp4dp_cell_indep_single batch filernum m1 m2 kersize stride padding input output Hio).
        apply SEM.in_acc_ary_inv with (i := b).
        apply SEM.in_acc_ary_inv with (i := nu).
        exact Hp. }
      rewrite SEM.eval_mkvSeq; [ | intros i0;
        apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_nu ].
      rewrite !SEM.eval_seqfor.
      apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros i0 eta'' HPeta''. split.
      * assert (Hcell_i0 : forall (j0 : fin ((m2 - kersize + 2 * padding) / stride + 1)),
          SEM.exp_independent_of_acc
            (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))
            (((output |{ b}) |{ nu}) |{ i0})).
        { intros j0 p0 Hp.
          apply (maxp4dp_cell_indep_single batch filernum m1 m2 kersize stride padding input output Hio).
          apply SEM.in_acc_ary_inv with (i := b).
          apply SEM.in_acc_ary_inv with (i := nu).
          apply SEM.in_acc_ary_inv with (i := i0).
          exact Hp. }
        rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_i0 ].
        rewrite !SEM.eval_seqfor.
        apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta'' |].
        intros j0 eta''' HPeta'''. split.
        -- set (e := DE.mkvSeq ((BRC2.maxp4dp_flat_cell batch filernum m1 m2 kersize stride padding input) b nu i0 j0)).
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
               { unfold e, BRC2.maxp4dp_flat_cell, DE.idx, DE.mkvSeq.
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
           { unfold e.
             apply (BRC2.maxp4dp_nested_max_flat batch filernum m1 m2 kersize
               stride padding input Hs Hbatch Hfilernum Hk). }
           assert (Heq_aux : SEM.eval_aux (c (CD.max (DE.mkvSeq (fun i1 : fin kersize => CD.max (DE.mkvSeq (fun j1 : fin kersize => CD.safe_idx_nat (CD.safe_idx_nat ((COP.Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))) 1 eta''' =
             SEM.eval_aux (c (CD.max e)) 1 eta''').
           { unfold c. rewrite !SEM.eval_assign_aux. f_equal. exact Hmax_eq. }
           rewrite Heq_aux.
           apply SEM.eval_cmax_equiv.
           ++ exact HPeta'''.
           ++ unfold e, BRC2.maxp4dp_flat_cell.
              apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
              repeat apply OSE.safe_idx_nat_independent.
              apply SEM.exp_independent_of_acc_idx.
              apply SEM.exp_independent_of_acc_idx.
              apply BRC2.Padding4d_independent.
              exact Hi.
           ++ apply BRC2.maxp4dp_cell_continuation_ok; assumption.
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

(* -------------------------------------------------------------------------- *)
(* Linear2d: single-output semantic equivalence                               *)
(* (replay of [Operators_Sem_Equiv.Linear2d_sem])                             *)
(* -------------------------------------------------------------------------- *)

Lemma linear2d_cell_indep_single : forall (batch m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{outnum} num))),
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc b output ->
  forall (bi : fin batch) (out : fin outnum),
  SEM.exp_independent_of_acc
    (CD.add (CD.sum (DE.mkvSeq (fun i : fin m =>
      CD.mul (DE.idx (DE.idx input bi) i) (DE.idx (DE.idx w out) i))))
      (DE.idx b out))
    output.
Proof.
  intros batch m outnum w b input output Hio Hwo Hbo bi out.
  apply SEM.exp_independent_of_acc_add.
  - apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply SEM.exp_independent_of_acc_mul.
    + apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hio.
    + apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hwo.
  - apply SEM.exp_independent_of_acc_idx. exact Hbo.
Qed.

Theorem Linear2d_sem_single : forall (batch m outnum : nat)
  (Hbatch : batch > 0) (Hm : m > 0) (Houtnum : outnum > 0)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{outnum} num))),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc b OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc b output ->
  OSE.tmp_disjoint_from_output2d batch outnum output ->
  forall (rho : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Linear2d w b input)) rho =
  SEM.eval (@CEO.Linear2d_comm batch m outnum w b input output) rho.
Proof.
  intros batch m outnum Hbatch Hm Houtnum w b input output
    Hi Hw Hb Hio Hwo Hbo Hdisj rho Hundef.
  unfold CG.A, COP.Linear2d, CEO.Linear2d_comm.
  set (row := fun bi : fin batch => DE.mkvSeq (fun out : fin outnum =>
    CD.add (CD.sum (DE.mkvSeq (fun i : fin m => CD.mul input|[bi]|[i] w|[out]|[i]))) b|[out])).
  assert (Hrow_indep : forall bi, SEM.exp_independent_of_acc (row bi) output).
  { intros bi. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros out.
    apply (linear2d_cell_indep_single batch m outnum w b input output Hio Hwo Hbo). }
  rewrite SEM.eval_mkvSeq; [ | intros bi; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros bi eta HPeta. split.
  - assert (Hcell_indep_bi : forall out,
      SEM.exp_independent_of_acc
        (CD.add (CD.sum (DE.mkvSeq (fun i : fin m => CD.mul input|[bi]|[i] w|[out]|[i]))) b|[out])
        (output |{ bi})).
    { intros out. unfold SEM.exp_independent_of_acc. intros p Hp.
      apply (linear2d_cell_indep_single batch m outnum w b input output Hio Hwo Hbo bi out).
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
            CG.vwt tmp |:= CD.add e|[i] (CG.vrd tmp)) ';
          (output|{bi}|{out}) |:= CD.add (CG.vrd tmp) b|[out]))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (CD.mul input|[bi]|[i] w|[out]|[i]) (CG.vrd tmp))
                    = CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add e|[i] (CG.vrd tmp))).
        { apply FTac.seqfor_extensionality; intro i.
          assert (Heq : CD.mul input|[bi]|[i] w|[out]|[i] = e|[i]).
          { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      rewrite SEM.eval_assign.
      rewrite <- (SEM.eval_assign_aux 1 num _ _ eta').
      change (SEM.eval_aux (c (CD.sum e)) 1 eta' =
        SEM.eval (@CG.loopacc num (fun tmp : string =>
          let wtmp := CG.vwt tmp in let v := CG.vrd tmp in
          wtmp |:= CD.zero '; CG.seqfor (fun i : fin m =>
            wtmp |:= CD.add e|[i] v)
          '; c v)) eta').
      apply (@SEM.eval_csum_equiv m e c eta').
      * exact HPeta'.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro i.
        apply SEM.exp_independent_of_acc_mul.
        -- apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hi.
        -- apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hw.
      * apply (OSE.Linear2d_cell_continuation_ok Hi Hw Hb bi out Hdisj).
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

(* -------------------------------------------------------------------------- *)
(* Softmax2d: single-output semantic equivalence                              *)
(* (replay of [Operators_Sem_Equiv.Softmax2d_sem])                            *)
(* -------------------------------------------------------------------------- *)

Lemma softmax2d_batch_continuation_ok_single : forall (batch m : nat)
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{m} num))),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  forall (b : fin batch),
  (forall p j, @PCG.in_acc num p OSE.tmp_scalar_acc -> (output |{ b}) |{ j} <> p) ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => CG.seqfor (fun j : fin m =>
      (output|{b}|{j}) |:= CD.div (CD.pExp input|[b]|[j]) r))
    (CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i]))).
Proof.
  intros batch m input output Hi Hio b Hdisj_row.
  set (e_final := CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i]))).
  set (g := fun (j : fin m) (r : DE.exp num) => CD.div (CD.pExp input|[b]|[j]) r).
  assert (Hdisj_acc : OSE.tmp_disjoint_from_acc (output |{ b})).
  { intros p Hp Hout. unfold PCG.in_acc in Hout. simpl in Hout.
    destruct Hout as [j Hj]. simpl in Hj. assert (Hc := Hdisj_row p j Hp Hj). contradiction. }
  assert (Hinput_row : SEM.exp_independent_of_acc input (output |{ b})).
  { intros p Hp. apply (Hio p). unfold PCG.in_acc in Hp |- *. simpl in Hp |- *.
    exists b. destruct Hp as [j Hj]. exists j. exact Hj. }
  apply OSE.seqfor_scalar_assign_continuation_ok.
  - exact Hdisj_acc.
  - unfold e_final. apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hi.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hi.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hi.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
  - intros j. unfold g. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hinput_row.
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
  (Hbatch : batch > 0) (Hm : m > 0)
  (input : DE.exp (ary '{batch} (ary '{m} num)))
  (output : DE.acc (ary '{batch} (ary '{m} num))),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  (forall (p : DE.path) (b : fin batch) (j : fin m),
     @PCG.in_acc num p OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num p ((output |{ b}) |{ j})) ->
  forall (rho : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Softmax2d input)) rho =
  SEM.eval (@CEO.Softmax2d_comm batch m input output) rho.
Proof.
  intros batch m Hbatch Hm input output Hi Hio Hdisj rho Hundef.
  unfold CG.A, COP.Softmax2d, CEO.Softmax2d_comm, CD.let_binding.
  set (s := DE.mkvSeq (fun b : fin batch =>
    CD.sum (DE.mkvSeq (fun i : fin m => CD.pExp input|[b]|[i])))).
  set (row := fun b : fin batch => DE.mkvSeq (fun j : fin m =>
    CD.div (CD.pExp input|[b]|[j]) (s|[b]))).
  assert (Hs_indep : SEM.exp_independent_of_acc s output).
  { unfold s. apply SEM.exp_independent_of_acc_mkvSeq. intro b'.
    apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx. exact Hio. }
  assert (Hrow_indep : forall b, SEM.exp_independent_of_acc (row b) output).
  { intros b. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros j.
    apply SEM.exp_independent_of_acc_div.
    - apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx. exact Hio.
    - apply SEM.exp_independent_of_acc_idx. exact Hs_indep. }
  rewrite SEM.eval_mkvSeq; [ | intros b; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros b eta HPeta. split.
  - assert (Hinput_row : SEM.exp_independent_of_acc input (output |{ b})).
    { intros p Hp. apply (Hio p). unfold PCG.in_acc in Hp |- *. simpl in Hp |- *.
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
            CG.vwt tmp |:= CD.add e|[i] (CG.vrd tmp)) ';
          CG.seqfor (fun j : fin m =>
            (output|{b})|{j} |:= CD.div (CD.pExp input|[b]|[j]) (CG.vrd tmp))))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add (CD.pExp input|[b]|[i]) (CG.vrd tmp))
                    = CG.seqfor (fun i : fin m =>
                        CG.vwt tmp |:= CD.add e|[i] (CG.vrd tmp))).
        { apply FTac.seqfor_extensionality; intro i.
          assert (Heq_i : CD.pExp input|[b]|[i] = e|[i]).
          { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq_i. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      apply (@SEM.eval_csum_equiv m e c eta).
      * exact HPeta.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro i.
        apply OSE.exp_independent_of_acc_pExp. repeat apply SEM.exp_independent_of_acc_idx. exact Hi.
      * apply (softmax2d_batch_continuation_ok_single batch m input output Hi Hio b).
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

(* -------------------------------------------------------------------------- *)
(* Flatten4d: single-output semantic equivalence                              *)
(* (replay of [Operators_Sem_Equiv.Flatten4d_sem])                            *)
(* -------------------------------------------------------------------------- *)

Lemma flatten4d_cell_indep_single : forall (batch channel m1 m2 : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel * m1 * m2} num))),
  SEM.exp_independent_of_acc input output ->
  forall (b : fin batch),
  SEM.exp_independent_of_acc (CD.join (CD.join input|[b])) output.
Proof.
  intros batch channel m1 m2 input output Hio b.
  rewrite (OSE.join_mkvSeq (CD.join input|[b])).
  rewrite (OSE.join_mkvSeq input|[b]).
  apply SEM.exp_independent_of_acc_mkvSeq. intro i.
  destruct (V.idx_1d_to_2d i) as [x y].
  repeat apply SEM.exp_independent_of_acc_idx.
  apply SEM.exp_independent_of_acc_mkvSeq. intro k.
  destruct (V.idx_1d_to_2d k) as [z w].
  repeat apply SEM.exp_independent_of_acc_idx.
  exact Hio.
Qed.

Lemma flatten4d_batch_sem_single : forall (batch channel m1 m2 : nat)
  (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel * m1 * m2} num))),
  SEM.exp_independent_of_acc input output ->
  forall (b : fin batch) (rho : PCG.env),
  SEM.eval (CG.assign ((output |{ b}), CD.join (CD.join input|[b]))) rho =
  SEM.eval (CG.seqfor (fun c : fin channel => CG.seqfor (fun i : fin m1 => CG.seqfor (fun j : fin m2 =>
    CG.assign (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j), input|[b]|[c]|[i]|[j]))))) rho.
Proof.
  intros batch channel m1 m2 Hc Hm1 Hm2 input output Hio b rho.
  rewrite (OSE.join_mkvSeq (CD.join input|[b])).
  rewrite (OSE.join_mkvSeq input|[b]).
  rewrite SEM.eval_mkvSeq.
  - rewrite !SEM.eval_seqfor.
    assert (Heq1 : PCG.seqfor (fun c : fin channel =>
      SEM.eval (CG.seqfor (fun i : fin m1 => CG.seqfor (fun j : fin m2 =>
        DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j])))) =
      PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
        let '(i, j) := V.idx_1d_to_2d k in
        SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j])))).
    { apply PCG.seqfor_extensionality. intro c.
      rewrite (OSE.seqfor_2d_CG Hm1 Hm2 (fun i j =>
        DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j])). reflexivity. }
    assert (Heq_m : channel * (m1 * m2) = (channel * m1) * m2) by (apply Nat.mul_assoc).
    assert (Heq2 : PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
      let '(i, j) := V.idx_1d_to_2d k in
      SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))) =
      PCG.seqfor (fun k : fin ((channel * m1) * m2) =>
        (fun k' : fin (channel * (m1 * m2)) =>
          let '(c, k0) := V.idx_1d_to_2d k' in
          let '(i, j) := V.idx_1d_to_2d k0 in
          SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))
        (OSE.fin_cast (eq_sym Heq_m) k))).
    { assert (Heq2' : PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
        let '(i, j) := V.idx_1d_to_2d k in
        SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))) =
        PCG.seqfor (fun k' : fin (channel * (m1 * m2)) =>
          let '(c, k0) := V.idx_1d_to_2d k' in
          let '(i, j) := V.idx_1d_to_2d k0 in
          SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))).
      { apply OSE.seqfor_2d_body; [assumption | apply Nat.mul_pos_pos; assumption ]. }
      rewrite Heq2'. rewrite -> (@OSE.seqfor_body_cast (channel * (m1 * m2)) ((channel * m1) * m2) Heq_m
        (fun k' : fin (channel * (m1 * m2)) =>
          let '(c, k0) := V.idx_1d_to_2d k' in
          let '(i, j) := V.idx_1d_to_2d k0 in
          SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))). reflexivity. }
    rewrite Heq1. rewrite Heq2.
    assert (Heq3 : PCG.seqfor (fun i : fin (channel * m1 * m2) =>
      SEM.eval (DE.idxAcc (output |{ b}) i |:=
        (let '(i0, j) := V.idx_1d_to_2d i in
          ((DE.mkvSeq (fun k : fin (channel * m1) =>
            let '(i1, j0) := V.idx_1d_to_2d k in ((input|[b])|[i1])|[j0]))
          |[i0])|[j]))) =
      PCG.seqfor (fun k : fin ((channel * m1) * m2) =>
        let '(c, k0) := V.idx_1d_to_2d (OSE.fin_cast (eq_sym Heq_m) k) in
        let '(i, j) := V.idx_1d_to_2d k0 in
        SEM.eval (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))).
    { apply PCG.seqfor_extensionality. intro k.
      destruct (V.idx_1d_to_2d (OSE.fin_cast (eq_sym Heq_m) k)) as [c k_inner] eqn:Hck.
      destruct (V.idx_1d_to_2d k_inner) as [i j] eqn:Hki.
      assert (Hcast : OSE.fin_cast (Nat.mul_assoc channel m1 m2) (OSE.fin_cast (eq_sym Heq_m) k) = k).
      { apply fin_eq. simpl. repeat rewrite OSE.fin_cast_nat. reflexivity. }
      assert (Hidx : k = CEB.flatten_idx c i j).
      { pose proof (OSE.flatten_idx_1d_to_2d_cast channel m1 m2 (OSE.fin_cast (eq_sym Heq_m) k)) as Hflat0.
        simpl in Hflat0. rewrite Hck in Hflat0. rewrite Hki in Hflat0. simpl in Hflat0.
        rewrite <- Hcast. exact Hflat0. }
      rewrite Hidx.
      apply (f_equal (fun e => SEM.eval (CG.assign (DE.idxAcc (output |{ b}) (CEB.flatten_idx c i j), e)))).
      unfold DE.idx, DE.mkvSeq, CD.join, V.v_join in *.
      destruct (V.idx_1d_to_2d (CEB.flatten_idx c i j)) as [ci j0] eqn:Hck'.
      rewrite V.v_idx_mk_vec.
      destruct (V.idx_1d_to_2d ci) as [c' i'] eqn:Hci'.
      assert (Hdecode : c = c' /\ i = i' /\ j = j0).
      { assert (Hflat : CEB.flatten_idx c i j = CEB.flatten_idx c' i' j0).
        { apply fin_eq'.
          pose proof (OSE.flatten_idx_1d_to_2d channel m1 m2 (CEB.flatten_idx c i j)) as Hflat0.
          simpl in Hflat0. rewrite Hck' in Hflat0. rewrite Hci' in Hflat0. simpl in Hflat0.
          exact Hflat0. }
        apply (OSE.flatten_idx_injective Hm1 Hm2) in Hflat.
        exact Hflat. }
      destruct Hdecode as [Hcc [Hii Hjj]].
      symmetry in Hcc. symmetry in Hii. symmetry in Hjj.
      subst c'. subst i'. subst j0.
      reflexivity. }
    rewrite Heq3. reflexivity.
  - intro k. destruct (V.idx_1d_to_2d k) as [ci j] eqn:?.
    repeat apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_mkvSeq. intro k0.
    destruct (V.idx_1d_to_2d k0) as [x y] eqn:?.
    repeat apply SEM.exp_independent_of_acc_idx.
    unfold SEM.exp_independent_of_acc. intros p Hp.
    apply (Hio p). simpl. exists b. exact Hp.
Qed.

Theorem Flatten4d_sem_single : forall (batch channel m1 m2 : nat)
  (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : DE.acc (ary '{batch} (ary '{channel * m1 * m2} num))),
  SEM.exp_independent_of_acc input output ->
  OSE.tmp_disjoint_from_output2d batch (channel * m1 * m2) output ->
  forall (rho : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Flatten4d input)) rho =
  SEM.eval (@CEB.Flatten4d_comm batch channel m1 m2 input output) rho.
Proof.
  intros batch channel m1 m2 Hc Hm1 Hm2 input output Hio Hdisj rho Hundef.
  unfold CG.A, COP.Flatten4d, CEB.Flatten4d_comm.
  rewrite SEM.eval_mkvSeq; [ | intros b; apply (flatten4d_cell_indep_single batch channel m1 m2 input output Hio) ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [ exact Hundef | ].
  intros b eta HPeta. split.
  - rewrite SEM.eval_assign. rewrite !SEM.eval_seqfor.
    apply (flatten4d_batch_sem_single batch channel m1 m2 Hc Hm1 Hm2 input output Hio b eta).
  - rewrite SEM.eval_assign.
    apply SEM.PCG_assign_preserves_StructUndefined.
    + exact HPeta.
    + intros p Hp Hout. simpl in Hout. destruct Hout as [out Hout'].
      apply (Hdisj p b out Hp). exact Hout'.
Qed.

(* -------------------------------------------------------------------------- *)
(* The assembled whole-network AST (batch 1, 3x224x224 input; loopacc-based   *)
(* layer commands; classic AlexNet structure)                                 *)
(* -------------------------------------------------------------------------- *)

Definition Tin  : data := ary '{1} (ary '{3} (ary '{224} (ary '{224} num))).
Definition Tw1  : data := ary '{64} (ary '{3} (ary '{11} (ary '{11} num))).
Definition Tb1  : data := ary '{64} num.
Definition Tc1  : data := ary '{1} (ary '{64} (ary '{55} (ary '{55} num))).
Definition Tp1  : data := ary '{1} (ary '{64} (ary '{27} (ary '{27} num))).
Definition Tw2  : data := ary '{192} (ary '{64} (ary '{5} (ary '{5} num))).
Definition Tb2  : data := ary '{192} num.
Definition Tc2  : data := ary '{1} (ary '{192} (ary '{27} (ary '{27} num))).
Definition Tp2  : data := ary '{1} (ary '{192} (ary '{13} (ary '{13} num))).
Definition Tw3  : data := ary '{384} (ary '{192} (ary '{3} (ary '{3} num))).
Definition Tb3  : data := ary '{384} num.
Definition Tc3  : data := ary '{1} (ary '{384} (ary '{13} (ary '{13} num))).
Definition Tw4  : data := ary '{256} (ary '{384} (ary '{3} (ary '{3} num))).
Definition Tb4  : data := ary '{256} num.
Definition Tc4  : data := ary '{1} (ary '{256} (ary '{13} (ary '{13} num))).
Definition Tw5  : data := ary '{256} (ary '{256} (ary '{3} (ary '{3} num))).
Definition Tb5  : data := ary '{256} num.
Definition Tc5  : data := ary '{1} (ary '{256} (ary '{13} (ary '{13} num))).
Definition Tp5  : data := ary '{1} (ary '{256} (ary '{6} (ary '{6} num))).
Definition Tflat: data := ary '{1} (ary '{(256*6*6)} num).
Definition Tf1w : data := ary '{4096} (ary '{(256*6*6)} num).
Definition Tf1b : data := ary '{4096} num.
Definition Tfc  : data := ary '{1} (ary '{4096} num).
Definition Tf2w : data := ary '{4096} (ary '{4096} num).
Definition Tf2b : data := ary '{4096} num.
Definition Tf3w : data := ary '{1000} (ary '{4096} num).
Definition Tf3b : data := ary '{1000} num.
Definition Tout : data := ary '{1} (ary '{1000} num).

Definition alexnet_gen_comm : CG.comm :=
  CG.seq ( @BRC2.Conv4d_ast_comm 1 224 224 11 11 3 64 2 4
             (@CG.vrd Tb1 "c1_b") (@CG.vrd Tw1 "c1_w")
             (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1"),
  CG.seq ( @CEO.ReLU4d_comm 1 64 55 55
             (@CG.vrd Tc1 "c1") (@CG.vwt Tc1 "r1"),
  CG.seq ( @BRC2.Maxpool4d_pad_ast_comm 1 64 55 55 3 2 0
             (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1"),
  CG.seq ( @BRC2.Conv4d_ast_comm 1 27 27 5 5 64 192 2 1
             (@CG.vrd Tb2 "c2_b") (@CG.vrd Tw2 "c2_w")
             (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2"),
  CG.seq ( @CEO.ReLU4d_comm 1 192 27 27
             (@CG.vrd Tc2 "c2") (@CG.vwt Tc2 "r2"),
  CG.seq ( @BRC2.Maxpool4d_pad_ast_comm 1 192 27 27 3 2 0
             (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2"),
  CG.seq ( @BRC2.Conv4d_ast_comm 1 13 13 3 3 192 384 1 1
             (@CG.vrd Tb3 "c3_b") (@CG.vrd Tw3 "c3_w")
             (@CG.vrd Tp2 "p2") (@CG.vwt Tc3 "c3"),
  CG.seq ( @CEO.ReLU4d_comm 1 384 13 13
             (@CG.vrd Tc3 "c3") (@CG.vwt Tc3 "r3"),
  CG.seq ( @BRC2.Conv4d_ast_comm 1 13 13 3 3 384 256 1 1
             (@CG.vrd Tb4 "c4_b") (@CG.vrd Tw4 "c4_w")
             (@CG.vrd Tc3 "r3") (@CG.vwt Tc4 "c4"),
  CG.seq ( @CEO.ReLU4d_comm 1 256 13 13
             (@CG.vrd Tc4 "c4") (@CG.vwt Tc4 "r4"),
  CG.seq ( @BRC2.Conv4d_ast_comm 1 13 13 3 3 256 256 1 1
             (@CG.vrd Tb5 "c5_b") (@CG.vrd Tw5 "c5_w")
             (@CG.vrd Tc4 "r4") (@CG.vwt Tc5 "c5"),
  CG.seq ( @CEO.ReLU4d_comm 1 256 13 13
             (@CG.vrd Tc5 "c5") (@CG.vwt Tc5 "r5"),
  CG.seq ( @BRC2.Maxpool4d_pad_ast_comm 1 256 13 13 3 2 0
             (@CG.vrd Tc5 "r5") (@CG.vwt Tp5 "p5"),
  CG.seq ( @CEB.Flatten4d_comm 1 256 6 6
             (@CG.vrd Tp5 "p5") (@CG.vwt Tflat "flat"),
  CG.seq ( @CEO.Linear2d_comm 1 (256*6*6) 4096
             (@CG.vrd Tf1w "f1_w") (@CG.vrd Tf1b "f1_b")
             (@CG.vrd Tflat "flat") (@CG.vwt Tfc "fc1"),
  CG.seq ( @CEB.ReLU2d_comm 1 4096
             (@CG.vrd Tfc "fc1") (@CG.vwt Tfc "fc1r"),
  CG.seq ( @CEO.Linear2d_comm 1 4096 4096
             (@CG.vrd Tf2w "f2_w") (@CG.vrd Tf2b "f2_b")
             (@CG.vrd Tfc "fc1r") (@CG.vwt Tfc "fc2"),
  CG.seq ( @CEB.ReLU2d_comm 1 4096
             (@CG.vrd Tfc "fc2") (@CG.vwt Tfc "fc2r"),
  CG.seq ( @CEO.Linear2d_comm 1 4096 1000
             (@CG.vrd Tf3w "f3_w") (@CG.vrd Tf3b "f3_b")
             (@CG.vrd Tfc "fc2r") (@CG.vwt Tout "fc3"),
             @CEO.Softmax2d_comm 1 1000
             (@CG.vrd Tout "fc3") (@CG.vwt Tout "output")
  ))))))))))))))))))).

(* -------------------------------------------------------------------------- *)
(* Functional layer values (route A), as functions of the initial env         *)
(* -------------------------------------------------------------------------- *)

Definition G1 (rho : PCG.env) : PCG.exp Tc1 :=
  OC.Conv4d 2 4
    (SEM.to_pcg_exp (@CG.vrd Tb1 "c1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw1 "c1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tin "input") rho).

Definition G2 (rho : PCG.env) : PCG.exp Tc2 :=
  OC.Conv4d 2 1
    (SEM.to_pcg_exp (@CG.vrd Tb2 "c2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw2 "c2_w") rho)
    (AD.Maxpool4d_pad 3 2 0 (OE.ReLU4d (G1 rho))).

Definition G3 (rho : PCG.env) : PCG.exp Tc3 :=
  OC.Conv4d 1 1
    (SEM.to_pcg_exp (@CG.vrd Tb3 "c3_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw3 "c3_w") rho)
    (AD.Maxpool4d_pad 3 2 0 (OE.ReLU4d (G2 rho))).

Definition G4 (rho : PCG.env) : PCG.exp Tc4 :=
  OC.Conv4d 1 1
    (SEM.to_pcg_exp (@CG.vrd Tb4 "c4_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw4 "c4_w") rho)
    (OE.ReLU4d (G3 rho)).

Definition G5 (rho : PCG.env) : PCG.exp Tc5 :=
  OC.Conv4d 1 1
    (SEM.to_pcg_exp (@CG.vrd Tb5 "c5_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw5 "c5_w") rho)
    (OE.ReLU4d (G4 rho)).

Definition G6 (rho : PCG.env) : PCG.exp Tfc :=
  OP.Linear2d
    (SEM.to_pcg_exp (@CG.vrd Tf1w "f1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf1b "f1_b") rho)
    (AD.Flatten4d (AD.Maxpool4d_pad 3 2 0 (OE.ReLU4d (G5 rho)))).

Definition G7 (rho : PCG.env) : PCG.exp Tfc :=
  OP.Linear2d
    (SEM.to_pcg_exp (@CG.vrd Tf2w "f2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf2b "f2_b") rho)
    (LF.ReLU2d (G6 rho)).

(* Freshness of the initial environment: the loopacc temporary and the
   route-A intermediate accumulators are all undefined. *)
Definition net_fresh (rho : PCG.env) : Prop :=
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho /\
  PCG.StructUndefined (@AD.a1_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a2_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a3_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a4_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a5_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a6_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a7_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a8_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a9_acc 1 224 224) rho /\
  PCG.StructUndefined (@AD.a10_acc 1) rho /\
  PCG.StructUndefined (@AD.a11_acc 1) rho.

(* -------------------------------------------------------------------------- *)
(* Per-layer buffer bridges (AST comm eval = single functional assign)        *)
(* -------------------------------------------------------------------------- *)

Lemma HB_c1 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Conv4d_ast_comm 1 224 224 11 11 3 64 2 4
             (@CG.vrd Tb1 "c1_b") (@CG.vrd Tw1 "c1_w")
             (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1")) eta =
  PCG.assign (@CG.vwt Tc1 "c1")
    (OC.Conv4d 2 4
       (SEM.to_pcg_exp (@CG.vrd Tb1 "c1_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tw1 "c1_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tin "input") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tin "input") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tw1 "c1_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tb1 "c1_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tw1 "c1_w") (@CG.vwt Tc1 "c1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tb1 "c1_b") (@CG.vwt Tc1 "c1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_conv4d 1 224 224 11 11 64 2 4
    (@CG.vwt Tc1 "c1"))
    by (exact (tmp_disj_vwt4 1 64 55 55 "c1" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv4d_sem_single 1 224 224 11 11 3 64 2 4
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tb1 "c1_b") (@CG.vrd Tw1 "c1_w") (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Conv4d 1 224 224 11 11 3 64 2 4
    (@CG.vrd Tb1 "c1_b") (@CG.vrd Tw1 "c1_w") (@CG.vrd Tin "input")
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eta).
  reflexivity.
Qed.

Lemma HB_p1 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Maxpool4d_pad_ast_comm 1 64 55 55 3 2 0
             (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1")) eta =
  PCG.assign (@CG.vwt Tp1 "p1")
    (AD.Maxpool4d_pad 3 2 0 (SEM.to_pcg_exp (@CG.vrd Tc1 "r1") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc1 "r1") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_maxp4dp 1 64 55 55 3 2 0
    (@CG.vwt Tp1 "p1"))
    by (exact (tmp_disj_vwt4 1 64 27 27 "p1" (ltac:(str_neq1_tac)))).
  rewrite <- (Maxpool4d_pad_sem_single 1 64 55 55 3 2 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1") Hi Hio Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Maxpool4d_pad 1 64 55 55 3 2 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tc1 "r1") eta).
  reflexivity.
Qed.

Lemma HB_c2 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Conv4d_ast_comm 1 27 27 5 5 64 192 2 1
             (@CG.vrd Tb2 "c2_b") (@CG.vrd Tw2 "c2_w")
             (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2")) eta =
  PCG.assign (@CG.vwt Tc2 "c2")
    (OC.Conv4d 2 1
       (SEM.to_pcg_exp (@CG.vrd Tb2 "c2_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tw2 "c2_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tp1 "p1") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tp1 "p1") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tw2 "c2_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tb2 "c2_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tw2 "c2_w") (@CG.vwt Tc2 "c2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tb2 "c2_b") (@CG.vwt Tc2 "c2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_conv4d 1 27 27 5 5 192 2 1
    (@CG.vwt Tc2 "c2"))
    by (exact (tmp_disj_vwt4 1 192 27 27 "c2" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv4d_sem_single 1 27 27 5 5 64 192 2 1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tb2 "c2_b") (@CG.vrd Tw2 "c2_w") (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Conv4d 1 27 27 5 5 64 192 2 1
    (@CG.vrd Tb2 "c2_b") (@CG.vrd Tw2 "c2_w") (@CG.vrd Tp1 "p1")
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eta).
  reflexivity.
Qed.

Lemma HB_p2 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Maxpool4d_pad_ast_comm 1 192 27 27 3 2 0
             (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2")) eta =
  PCG.assign (@CG.vwt Tp2 "p2")
    (AD.Maxpool4d_pad 3 2 0 (SEM.to_pcg_exp (@CG.vrd Tc2 "r2") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc2 "r2") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_maxp4dp 1 192 27 27 3 2 0
    (@CG.vwt Tp2 "p2"))
    by (exact (tmp_disj_vwt4 1 192 13 13 "p2" (ltac:(str_neq1_tac)))).
  rewrite <- (Maxpool4d_pad_sem_single 1 192 27 27 3 2 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2") Hi Hio Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Maxpool4d_pad 1 192 27 27 3 2 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tc2 "r2") eta).
  reflexivity.
Qed.

Lemma HB_c3 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Conv4d_ast_comm 1 13 13 3 3 192 384 1 1
             (@CG.vrd Tb3 "c3_b") (@CG.vrd Tw3 "c3_w")
             (@CG.vrd Tp2 "p2") (@CG.vwt Tc3 "c3")) eta =
  PCG.assign (@CG.vwt Tc3 "c3")
    (OC.Conv4d 1 1
       (SEM.to_pcg_exp (@CG.vrd Tb3 "c3_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tw3 "c3_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tp2 "p2") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tp2 "p2") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tw3 "c3_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tb3 "c3_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tp2 "p2") (@CG.vwt Tc3 "c3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tw3 "c3_w") (@CG.vwt Tc3 "c3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tb3 "c3_b") (@CG.vwt Tc3 "c3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_conv4d 1 13 13 3 3 384 1 1
    (@CG.vwt Tc3 "c3"))
    by (exact (tmp_disj_vwt4 1 384 13 13 "c3" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv4d_sem_single 1 13 13 3 3 192 384 1 1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tb3 "c3_b") (@CG.vrd Tw3 "c3_w") (@CG.vrd Tp2 "p2") (@CG.vwt Tc3 "c3")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Conv4d 1 13 13 3 3 192 384 1 1
    (@CG.vrd Tb3 "c3_b") (@CG.vrd Tw3 "c3_w") (@CG.vrd Tp2 "p2")
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eta).
  reflexivity.
Qed.

Lemma HB_c4 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Conv4d_ast_comm 1 13 13 3 3 384 256 1 1
             (@CG.vrd Tb4 "c4_b") (@CG.vrd Tw4 "c4_w")
             (@CG.vrd Tc3 "r3") (@CG.vwt Tc4 "c4")) eta =
  PCG.assign (@CG.vwt Tc4 "c4")
    (OC.Conv4d 1 1
       (SEM.to_pcg_exp (@CG.vrd Tb4 "c4_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tw4 "c4_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tc3 "r3") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc3 "r3") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tw4 "c4_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tb4 "c4_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc3 "r3") (@CG.vwt Tc4 "c4"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tw4 "c4_w") (@CG.vwt Tc4 "c4"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tb4 "c4_b") (@CG.vwt Tc4 "c4"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_conv4d 1 13 13 3 3 256 1 1
    (@CG.vwt Tc4 "c4"))
    by (exact (tmp_disj_vwt4 1 256 13 13 "c4" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv4d_sem_single 1 13 13 3 3 384 256 1 1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tb4 "c4_b") (@CG.vrd Tw4 "c4_w") (@CG.vrd Tc3 "r3") (@CG.vwt Tc4 "c4")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Conv4d 1 13 13 3 3 384 256 1 1
    (@CG.vrd Tb4 "c4_b") (@CG.vrd Tw4 "c4_w") (@CG.vrd Tc3 "r3")
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eta).
  reflexivity.
Qed.

Lemma HB_c5 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Conv4d_ast_comm 1 13 13 3 3 256 256 1 1
             (@CG.vrd Tb5 "c5_b") (@CG.vrd Tw5 "c5_w")
             (@CG.vrd Tc4 "r4") (@CG.vwt Tc5 "c5")) eta =
  PCG.assign (@CG.vwt Tc5 "c5")
    (OC.Conv4d 1 1
       (SEM.to_pcg_exp (@CG.vrd Tb5 "c5_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tw5 "c5_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tc4 "r4") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc4 "r4") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tw5 "c5_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tb5 "c5_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc4 "r4") (@CG.vwt Tc5 "c5"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tw5 "c5_w") (@CG.vwt Tc5 "c5"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tb5 "c5_b") (@CG.vwt Tc5 "c5"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_conv4d 1 13 13 3 3 256 1 1
    (@CG.vwt Tc5 "c5"))
    by (exact (tmp_disj_vwt4 1 256 13 13 "c5" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv4d_sem_single 1 13 13 3 3 256 256 1 1
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tb5 "c5_b") (@CG.vrd Tw5 "c5_w") (@CG.vrd Tc4 "r4") (@CG.vwt Tc5 "c5")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Conv4d 1 13 13 3 3 256 256 1 1
    (@CG.vrd Tb5 "c5_b") (@CG.vrd Tw5 "c5_w") (@CG.vrd Tc4 "r4")
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) eta).
  reflexivity.
Qed.

Lemma HB_p5 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@BRC2.Maxpool4d_pad_ast_comm 1 256 13 13 3 2 0
             (@CG.vrd Tc5 "r5") (@CG.vwt Tp5 "p5")) eta =
  PCG.assign (@CG.vwt Tp5 "p5")
    (AD.Maxpool4d_pad 3 2 0 (SEM.to_pcg_exp (@CG.vrd Tc5 "r5") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc5 "r5") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc5 "r5") (@CG.vwt Tp5 "p5"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : BRC2.tmp_disjoint_from_output_maxp4dp 1 256 13 13 3 2 0
    (@CG.vwt Tp5 "p5"))
    by (exact (tmp_disj_vwt4 1 256 6 6 "p5" (ltac:(str_neq1_tac)))).
  rewrite <- (Maxpool4d_pad_sem_single 1 256 13 13 3 2 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tc5 "r5") (@CG.vwt Tp5 "p5") Hi Hio Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Maxpool4d_pad 1 256 13 13 3 2 0
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tc5 "r5") eta).
  reflexivity.
Qed.

Lemma HB_flat : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEB.Flatten4d_comm 1 256 6 6
             (@CG.vrd Tp5 "p5") (@CG.vwt Tflat "flat")) eta =
  PCG.assign (@CG.vwt Tflat "flat")
    (AD.Flatten4d (SEM.to_pcg_exp (@CG.vrd Tp5 "p5") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tp5 "p5") (@CG.vwt Tflat "flat"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d 1 (256 * 6 * 6) (@CG.vwt Tflat "flat"))
    by (exact (tmp_disj_vwt2 1 (256*6*6) "flat" (ltac:(str_neq1_tac)))).
  rewrite <- (Flatten4d_sem_single 1 256 6 6
    ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tp5 "p5") (@CG.vwt Tflat "flat") Hio Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC2.interp_Flatten4d 1 256 6 6
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) (@CG.vrd Tp5 "p5") eta).
  reflexivity.
Qed.

Lemma HB_fc1 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear2d_comm 1 (256*6*6) 4096
             (@CG.vrd Tf1w "f1_w") (@CG.vrd Tf1b "f1_b")
             (@CG.vrd Tflat "flat") (@CG.vwt Tfc "fc1")) eta =
  PCG.assign (@CG.vwt Tfc "fc1")
    (OP.Linear2d
       (SEM.to_pcg_exp (@CG.vrd Tf1w "f1_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tf1b "f1_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tflat "flat") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tflat "flat") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tf1w "f1_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tf1b "f1_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tflat "flat") (@CG.vwt Tfc "fc1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tf1w "f1_w") (@CG.vwt Tfc "fc1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tf1b "f1_b") (@CG.vwt Tfc "fc1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d 1 4096 (@CG.vwt Tfc "fc1"))
    by (exact (tmp_disj_vwt2 1 4096 "fc1" (ltac:(str_neq1_tac)))).
  rewrite <- (Linear2d_sem_single 1 (256*6*6) 4096
    ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tf1w "f1_w") (@CG.vrd Tf1b "f1_b") (@CG.vrd Tflat "flat") (@CG.vwt Tfc "fc1")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (interp_Linear2d 1 (256*6*6) 4096
    (@CG.vrd Tf1w "f1_w") (@CG.vrd Tf1b "f1_b") (@CG.vrd Tflat "flat") eta).
  reflexivity.
Qed.

Lemma HB_fc2 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear2d_comm 1 4096 4096
             (@CG.vrd Tf2w "f2_w") (@CG.vrd Tf2b "f2_b")
             (@CG.vrd Tfc "fc1r") (@CG.vwt Tfc "fc2")) eta =
  PCG.assign (@CG.vwt Tfc "fc2")
    (OP.Linear2d
       (SEM.to_pcg_exp (@CG.vrd Tf2w "f2_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tf2b "f2_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc "fc1r") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tfc "fc1r") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tf2w "f2_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tf2b "f2_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tfc "fc1r") (@CG.vwt Tfc "fc2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tf2w "f2_w") (@CG.vwt Tfc "fc2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tf2b "f2_b") (@CG.vwt Tfc "fc2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d 1 4096 (@CG.vwt Tfc "fc2"))
    by (exact (tmp_disj_vwt2 1 4096 "fc2" (ltac:(str_neq1_tac)))).
  rewrite <- (Linear2d_sem_single 1 4096 4096
    ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tf2w "f2_w") (@CG.vrd Tf2b "f2_b") (@CG.vrd Tfc "fc1r") (@CG.vwt Tfc "fc2")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (interp_Linear2d 1 4096 4096
    (@CG.vrd Tf2w "f2_w") (@CG.vrd Tf2b "f2_b") (@CG.vrd Tfc "fc1r") eta).
  reflexivity.
Qed.

Lemma HB_fc3 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear2d_comm 1 4096 1000
             (@CG.vrd Tf3w "f3_w") (@CG.vrd Tf3b "f3_b")
             (@CG.vrd Tfc "fc2r") (@CG.vwt Tout "fc3")) eta =
  PCG.assign (@CG.vwt Tout "fc3")
    (OP.Linear2d
       (SEM.to_pcg_exp (@CG.vrd Tf3w "f3_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tf3b "f3_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc "fc2r") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tfc "fc2r") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tf3w "f3_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tf3b "f3_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tfc "fc2r") (@CG.vwt Tout "fc3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tf3w "f3_w") (@CG.vwt Tout "fc3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tf3b "f3_b") (@CG.vwt Tout "fc3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output2d 1 1000 (@CG.vwt Tout "fc3"))
    by (exact (tmp_disj_vwt2 1 1000 "fc3" (ltac:(str_neq1_tac)))).
  rewrite <- (Linear2d_sem_single 1 4096 1000
    ltac:(lia) ltac:(lia) ltac:(lia)
    (@CG.vrd Tf3w "f3_w") (@CG.vrd Tf3b "f3_b") (@CG.vrd Tfc "fc2r") (@CG.vwt Tout "fc3")
    Hi Hw Hb Hio Hwo Hbo Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (interp_Linear2d 1 4096 1000
    (@CG.vrd Tf3w "f3_w") (@CG.vrd Tf3b "f3_b") (@CG.vrd Tfc "fc2r") eta).
  reflexivity.
Qed.

Lemma HB_sm : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Softmax2d_comm 1 1000
             (@CG.vrd Tout "fc3") (@CG.vwt Tout "output")) eta =
  PCG.assign (@CG.vwt Tout "output")
    (OR.Softmax2d (SEM.to_pcg_exp (@CG.vrd Tout "fc3") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tout "fc3") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tout "fc3") (@CG.vwt Tout "output"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : forall (p : DE.path) (b : fin 1) (j : fin 1000),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p ((@CG.vwt Tout "output") |{ b} |{ j}))
    by (exact (tmp_disj_vwt2 1 1000 "output" (ltac:(str_neq1_tac)))).
  rewrite <- (Softmax2d_sem_single 1 1000
    ltac:(lia) ltac:(lia)
    (@CG.vrd Tout "fc3") (@CG.vwt Tout "output") Hi Hio Hdisj eta Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (interp_Softmax2d 1 1000 ltac:(lia) (@CG.vrd Tout "fc3") eta).
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The whole-network bridge                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_AlexNet : forall (rho : PCG.env) (p : DE.path),
  @PCG.in_acc Tout p (@CG.vwt Tout "output") ->
  net_fresh rho ->
  (forall (b : fin 1) (c : fin 64) (i0 i1 : fin 55),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (G1 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 192) (i0 i1 : fin 27),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (G2 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 384) (i0 i1 : fin 13),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (G3 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 256) (i0 i1 : fin 13),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (G4 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (c : fin 256) (i0 i1 : fin 13),
     (PCG.idx (PCG.idx (PCG.idx (PCG.idx (G5 rho) b) c) i0) i1 <= R0)%R) ->
  (forall (b : fin 1) (i : fin 4096),
     (PCG.idx (PCG.idx (G6 rho) b) i <= R0)%R) ->
  (forall (b : fin 1) (i : fin 4096),
     (PCG.idx (PCG.idx (G7 rho) b) i <= R0)%R) ->
  SEM.eval alexnet_gen_comm rho p =
  AD.alexnet_comm
    (SEM.to_pcg_exp (@CG.vrd Tin "input") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw1 "c1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb1 "c1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw2 "c2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb2 "c2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw3 "c3_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb3 "c3_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw4 "c4_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb4 "c4_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw5 "c5_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb5 "c5_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf1w "f1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf1b "f1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf2w "f2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf2b "f2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf3w "f3_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf3b "f3_b") rho)
    (@CG.vwt Tout "output") rho p.
Proof.
  intros rho p Hinacc Hfresh Hr1 Hr2 Hr3 Hr4 Hr5 Hr6 Hr7.
  destruct Hfresh as [Htmp [Hl1 [Hl2 [Hl3 [Hl4 [Hl5 [Hl6 [Hl7 [Hl8 [Hl9 [Hl10 Hl11]]]]]]]]]]].
  (* Route-A side: collapse [alexnet_comm] to the functional assignment. *)
  assert (HfreshA : @AD.alexnet_fresh 1 224 224 (@CG.vwt Tout "output") rho).
  { unfold AD.alexnet_fresh. repeat split; try assumption;
    intros p0 Hin0 Hin1;
    destruct (in_acc_vwt_bracket _ _ _ _ _ Hin0) as [u Heq]; subst p0;
    apply in_acc_acc'_Var in Hin1; injection Hin1 as Hin1; discriminate. }
  rewrite (AD.A_AlexNet
    (SEM.to_pcg_exp (@CG.vrd Tin "input") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw1 "c1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb1 "c1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw2 "c2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb2 "c2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw3 "c3_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb3 "c3_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw4 "c4_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb4 "c4_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tw5 "c5_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tb5 "c5_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf1w "f1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf1b "f1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf2w "f2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf2b "f2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf3w "f3_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tf3b "f3_b") rho)
    Hinacc HfreshA).
  cbv [DR.A]. cbv beta.
  (* Route-B side: 20-step forward simulation. *)
  unfold alexnet_gen_comm.
  (* c1: conv1 (11x11, p2, s4) *)
  rewrite eval_seq'.
  rewrite HB_c1; [| exact Htmp].
  (* r1: relu4d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU4d_buf (batch:=1) (channel:=64) (m1:=55) (m2:=55) "c1" "r1");
    [| discriminate | discriminate | str_neq_tac |
       intros b c i0 i1;
       rewrite SEM.vrd_after_own_vwt by discriminate;
       exact (Hr1 b c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* p1: maxpool 3x3 s2 *)
  rewrite eval_seq'.
  rewrite HB_p1; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* c2: conv2 (5x5, p2, s1) *)
  rewrite eval_seq'.
  rewrite HB_c2; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* r2: relu4d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU4d_buf (batch:=1) (channel:=192) (m1:=27) (m2:=27) "c2" "r2");
    [| discriminate | discriminate | str_neq_tac |
       intros b c i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr2 b c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* p2: maxpool 3x3 s2 *)
  rewrite eval_seq'.
  rewrite HB_p2; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* c3: conv3 (3x3, p1, s1) *)
  rewrite eval_seq'.
  rewrite HB_c3; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* r3: relu4d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU4d_buf (batch:=1) (channel:=384) (m1:=13) (m2:=13) "c3" "r3");
    [| discriminate | discriminate | str_neq_tac |
       intros b c i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr3 b c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* c4: conv4 (3x3, p1, s1) *)
  rewrite eval_seq'.
  rewrite HB_c4; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* r4: relu4d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU4d_buf (batch:=1) (channel:=256) (m1:=13) (m2:=13) "c4" "r4");
    [| discriminate | discriminate | str_neq_tac |
       intros b c i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr4 b c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* c5: conv5 (3x3, p1, s1) *)
  rewrite eval_seq'.
  rewrite HB_c5; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* r5: relu4d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU4d_buf (batch:=1) (channel:=256) (m1:=13) (m2:=13) "c5" "r5");
    [| discriminate | discriminate | str_neq_tac |
       intros b c i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr5 b c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* p5: maxpool 3x3 s2 *)
  rewrite eval_seq'.
  rewrite HB_p5; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* flat: flatten *)
  rewrite eval_seq'.
  rewrite HB_flat; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* fc1: linear *)
  rewrite eval_seq'.
  rewrite HB_fc1; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* fc1r: relu2d *)
  rewrite eval_seq'.
  erewrite (bridge_ReLU2d_buf (m1:=1) (m2:=4096) "fc1" "fc1r");
    [| discriminate | discriminate | str_neq_tac |
       intros i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr6 i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* fc2: linear *)
  rewrite eval_seq'.
  rewrite HB_fc2; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* fc2r: relu2d *)
  rewrite eval_seq'.
  erewrite (bridge_ReLU2d_buf (m1:=1) (m2:=4096) "fc2" "fc2r");
    [| discriminate | discriminate | str_neq_tac |
       intros i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr7 i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* fc3: linear *)
  rewrite eval_seq'.
  rewrite HB_fc3; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* output: softmax *)
  rewrite HB_sm; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* Observe at [p] inside the output buffer. *)
  rewrite (SEM.assign_in_acc_independent_of_env _ _ _ _ rho _ Hinacc).
  reflexivity.
Qed.

Print Assumptions Bridge_AlexNet.
