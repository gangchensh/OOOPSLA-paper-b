(* ========================================================================= *)
(* Bridge_LeNet5.v                                                           *)
(*                                                                           *)
(* Whole-network route-A/route-B bridge pilot for LeNet-5:                   *)
(*                                                                           *)
(*   eval (AST-level LeNet-5) rho p  =  lenet5_comm (route A) ... rho p      *)
(*                                                                           *)
(* pointwise at every path [p] inside the output accumulator.                *)
(*                                                                           *)
(* Route B (code generation): the sequential composition of per-layer AST    *)
(*   commands ([CEO.Conv3d_comm], [CEB.ReLU3d_comm], [CEO.Maxpool3d_comm],   *)
(*   [CEB.Flatten3d_comm], [CEO.Linear1d_comm], [CEB.ReLU1d_comm],           *)
(*   [CEO.Softmax1d_comm]) writing the named buffers                         *)
(*   "c1" "r1" "p1" "c2" "r2" "p2" "flat" "fc1" "fc1_relu" "fc2" "fc2_relu"  *)
(*   "fc3" "output" (the same buffer names as [CNN_Examples_LeNet5]).        *)
(* Route A (DPIA): [LeNet5_Imperative.lenet5_comm] with its proved           *)
(*   whole-network collapse [LeNet5_DPIA.A_LeNet5].                          *)
(*                                                                           *)
(* Two structural notes:                                                     *)
(*                                                                           *)
(* 1. Input/padding.  Route A's LeNet-5 takes a 1x28x28 input and zero-pads  *)
(*    inside conv1 (padding 2); route B's concrete [CNN_Examples_LeNet5.     *)
(*    lenet5_comm] instead takes a pre-padded 1x32x32 input with padding 0.  *)
(*    Since [Bridge_Pilot] established that both routes zero-pad, the        *)
(*    bridge is stated for the padding-2 AST conv1 on the shared 1x28x28     *)
(*    input, so no cropping hypothesis is needed.                            *)
(*                                                                           *)
(* 2. Concrete vs generic layer commands.  The concrete [new]-based          *)
(*    [lenet5_conv1_comm]/[lenet5_pool1_comm]/[lenet5_pool2_comm] of         *)
(*    [CNN_Examples_LeNet5] are code-generation artifacts whose [eval] does  *)
(*    NOT model the accumulator loop (see the comments at their definition   *)
(*    sites): under [eval] the conv writes [0 + bias] and the pool writes    *)
(*    the top-left window element.  Hence [eval CEL.lenet5_comm] cannot be   *)
(*    equal to the functional semantics, and the former axiom                *)
(*    [CEL.lenet5_equiv] is not derivable.  This file therefore bridges the  *)
(*    GENERIC loopacc-based AST net [lenet5_gen_comm] below — the net for    *)
(*    which route B itself proves the per-layer semantic equivalences.       *)
(*                                                                           *)
(* What is proved here (the genuinely new, whole-network part):              *)
(*   - the buffer-composition machinery: name-based read/write lemmas        *)
(*     ([in_acc_vwt_bracket], [vrd_after_other_vwt_ary]), freshness          *)
(*     preservation for the loopacc temporary ([SU_tmp_after_assign_vwt]),   *)
(*     and the 13-step forward simulation collapsing [eval lenet5_gen_comm]  *)
(*     to a single [PCG.assign] of the route-A functional net;               *)
(*   - the ReLU-layer bridges in full (route B [ReLU*_equiv_sem] + the       *)
(*     interpretation lemmas [interp_ReLU3d]/[interp_ReLU1d] + route A       *)
(*     [LeNet5_DPIA.A_ReLU*]), including the conversion of the runtime       *)
(*     boolean side condition to a clean [Rle] premise on the functional     *)
(*     layer values.                                                         *)
(*                                                                           *)
(* The 9 non-ReLU per-layer bridges (formerly Section hypotheses) are        *)
(*   PROVED here.  The route-B operator theorems [OSE.*_sem] (and the        *)
(*   [Bridge_ReduceConv] bridges built on them) universally quantify the     *)
(*   output acceptor in their independence side conditions ([forall out,     *)
(*   exp_independent_of_acc input out]), which is unsatisfiable for          *)
(*   buffer-read inputs such as [vrd "p1"] (take [out] to be an acceptor     *)
(*   covering the buffer's own paths).  This file therefore re-proves the    *)
(*   route-B equivalences with single-output side conditions                 *)
(*   ([Linear1d_sem_single], [Softmax1d_sem_single], [Maxpool2d_sem_single], *)
(*   [Maxpool3d_sem_single], [Flatten3d_sem_single], [Conv3d_sem_single])    *)
(*   by replaying the [Operators_Sem_Equiv] proofs with the universally      *)
(*   quantified independence premises replaced by the concrete ones; the     *)
(*   heavy machinery (loopacc elimination, continuation lemmas, sum/max      *)
(*   flattening, padding independence) is reused from [Operators_Sem_Equiv], *)
(*   and the functional interpretation lemmas from [Bridge_ReduceConv].      *)
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

Open Scope string_scope.

(* The buffer name types ([Tc1], [Tkc2], ...) are local [Definition]s; the
   default (unkeyed) subterm matching of [rewrite] refuses to unfold them
   when instantiating the type evars of the read/write lemmas, so the
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
Module LI := Ionia.LeNet5_Imperative.
Module LD := Ionia.LeNet5_DPIA.
Module V := Ionia.vector.
Module BRC := Ionia.Bridge_ReduceConv.
Module FTac := Ionia.FusionTactics.

(* Variable lookup used by [SEM.to_pcg_exp] and [SEM.eval].
   (Local copy of the helper in [Bridge_Pilot], which is not imported.) *)
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
(* Buffer name infrastructure for the whole-network composition               *)
(* -------------------------------------------------------------------------- *)

(* Every leaf path of an ARRAY write target [vwt s] carries at least one
   bracket suffix.  This sharpens [SEM.in_acc_vwt] (which allows the empty
   suffix) and is what makes name-clash reasoning work for pairs like
   ("fc1", "fc1_relu") where one name is a prefix of the other. *)
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

(* Writing buffer [si] does not affect reading buffer [t] whenever [si]'s
   bracketed region cannot collide with [t].  Unlike
   [SEM.vrd_after_other_vwt] (whose side condition quantifies over ALL
   suffixes and therefore fails when [si] is a prefix of [t], e.g.
   "fc1" vs "fc1_relu"), this version only ranges over bracketed paths,
   which is all an array [vwt] ever writes. *)
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

(* Sharper read-path independence for ARRAY read trees: every leaf variable
   read by [CG.vrd (ary f d) t] carries a bracket right after [t], so the
   extension condition only needs to range over bracketed suffixes.  This is
   what makes prefix-named buffer pairs such as ("fc1", "fc1_relu") work:
   ["fc1_relu[" ...] never collides with ["fc1[" ...]. *)
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

(* Type-polymorphic version of [vrd_after_other_vwt_ary]: the read buffer and
   the written buffer may have different data types (e.g. reading the weight
   buffer ["fc1_w"] after writing ["flat"]).  Both sides only range over
   bracketed paths, so prefix-named pairs are still handled. *)
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

(* Assigning an array buffer preserves undefinedness of the loopacc
   temporary ["__tmp"] (its path never has a bracketed buffer prefix). *)
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

(* Sequential composition of AST commands under [eval]. *)
Lemma eval_seq' : forall (c1 c2 : CG.comm) (rho : PCG.env),
  SEM.eval (CG.seq (c1, c2)) rho = SEM.eval c2 (SEM.eval c1 rho).
Proof. intros. reflexivity. Qed.

(* String name-clash solver for the concrete buffer names of the net. *)
Ltac str_neq_tac := intros u v Heq; discriminate.

(* One-sided variant for goals ["__tmp" <> name ++ "[" ++ u]. *)
Ltac str_neq1_tac := intros u Heq; discriminate.
Ltac str_neq2_tac := intros u v Heq; discriminate.

(* Discharge [StructUndefined tmp] at any stage env (a nested stack of
   buffer assigns on top of the initial [rho]). *)
Ltac su_tmp_tac :=
  repeat (apply SU_tmp_after_assign_vwt; [ intros u Heq; discriminate | ]);
  assumption.

(* -------------------------------------------------------------------------- *)
(* Reading an untouched/own variable region in the empty environment          *)
(* (used to evaluate the static [bexp2bool] side of the ReLU side condition)  *)
(* -------------------------------------------------------------------------- *)

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

(* -------------------------------------------------------------------------- *)
(* ReLU3d / ReLU1d: functional interpretation lemmas                          *)
(* (3d is [Bridge_Pilot.interp_ReLU3d]; 1d is the same pattern)               *)
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

Lemma interp_ReLU1d : forall (n : nat)
  (input : DE.exp (ary '{n} num)) (rho : PCG.env),
  (forall (i : fin n),
     DE.eval_bexp (env_val rho) (CD.leExp (DE.idx input i) CD.zero) =
     DE.bexp2bool (CD.leExp (DE.idx input i) CD.zero)) ->
  SEM.to_pcg_exp (COP.ReLU1d input) rho =
  LF.ReLU1d (SEM.to_pcg_exp input rho).
Proof.
  intros n input rho Hb.
  unfold COP.ReLU1d, LF.ReLU1d.
  apply to_pcg_mkvSeq_ext; intro i.
  rewrite <- (Hb i).
  remember (DE.eval_bexp (env_val rho) (CD.leExp (DE.idx input i) CD.zero))
    as b eqn:E.
  rewrite to_pcg_exp_BLe in E.
  rewrite SEM.to_pcg_exp_zero in E.
  rewrite SEM.to_pcg_exp_idx in E.
  unfold PCG.zero.
  destruct b; rewrite <- E.
  - reflexivity.
  - rewrite SEM.to_pcg_exp_idx. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* ReLU layer bridges between named buffers                                   *)
(*                                                                            *)
(* The runtime boolean side condition of [ReLU*_equiv_sem] is packaged in    *)
(* the clean form "every pre-activation value is [<= 0]" on the INTERPRETED  *)
(* buffer content [to_pcg_exp (vrd sin) eta]; the conversion to the native   *)
(* [eval_bexp = bexp2bool] form is done once and for all inside the proofs.  *)
(* -------------------------------------------------------------------------- *)

Lemma bridge_ReLU3d_buf : forall {n1 n2 n3 : nat} (sin sout : string)
  (eta : PCG.env),
  (sin <> "0")%string -> (sin <> "1")%string ->
  (forall u v : string, (sout ++ "[" ++ u <> sin ++ "[" ++ v)%string) ->
  (forall (c : fin n1) (i0 : fin n2) (i1 : fin n3),
     (PCG.idx (PCG.idx (PCG.idx
        (SEM.to_pcg_exp (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin) eta)
        c) i0) i1 <= R0)%R) ->
  SEM.eval
    (@CEB.ReLU3d_comm n1 n2 n3
       (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin)
       (@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} num))) sout)) eta =
  PCG.assign (@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} num))) sout)
    (LF.ReLU3d
      (SEM.to_pcg_exp (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin) eta))
    eta.
Proof.
  intros n1 n2 n3 sin sout eta Hs0 Hs1 Hnames Hle.
  (* Convert the [Rle] premise to the native boolean side condition. *)
  assert (Hb : forall (c : fin n1) (i0 : fin n2) (i1 : fin n3),
    DE.eval_bexp (env_val eta)
      (CD.leExp (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin) c) i0) i1) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin) c) i0) i1) CD.zero)).
  { intros c i0 i1.
    rewrite (to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (DE.idx (DE.idx
        (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin) c) i0) i1) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (DE.idx (DE.idx
          (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin) c) i0) i1)
          PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (env_val PCG.env_empty) by reflexivity.
      apply to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite !PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle c i0 i1).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  (* The buffer read does not clash with the output buffer. *)
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{n1} (ary '{n2} (ary '{n3} num))) sin)
    (@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} num))) sout)).
  { intros p Hp. destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEB.ReLU3d_equiv_sem _ Hindep Hb).
  cbv [CG.A]. rewrite SEM.eval_assign.
  f_equal. apply interp_ReLU3d. exact Hb.
Qed.

Lemma bridge_ReLU1d_buf : forall {n : nat} (sin sout : string)
  (eta : PCG.env),
  (sin <> "0")%string -> (sin <> "1")%string ->
  (forall u v : string, (sout ++ "[" ++ u <> sin ++ "[" ++ v)%string) ->
  (forall (i : fin n),
     (PCG.idx (SEM.to_pcg_exp (@CG.vrd (ary '{n} num) sin) eta) i <= R0)%R) ->
  SEM.eval
    (@CEB.ReLU1d_comm n
       (@CG.vrd (ary '{n} num) sin) (@CG.vwt (ary '{n} num) sout)) eta =
  PCG.assign (@CG.vwt (ary '{n} num) sout)
    (LF.ReLU1d (SEM.to_pcg_exp (@CG.vrd (ary '{n} num) sin) eta)) eta.
Proof.
  intros n sin sout eta Hs0 Hs1 Hnames Hle.
  assert (Hb : forall (i : fin n),
    DE.eval_bexp (env_val eta)
      (CD.leExp (DE.idx (@CG.vrd (ary '{n} num) sin) i) CD.zero) =
    DE.bexp2bool
      (CD.leExp (DE.idx (@CG.vrd (ary '{n} num) sin) i) CD.zero)).
  { intros i.
    rewrite (to_pcg_exp_BLe _ _ _).
    assert (HRHS : DE.bexp2bool
      (CD.leExp (DE.idx (@CG.vrd (ary '{n} num) sin) i) CD.zero) =
      PCG.leExp
        (SEM.to_pcg_exp (DE.idx (@CG.vrd (ary '{n} num) sin) i) PCG.env_empty)
        (SEM.to_pcg_exp CD.zero PCG.env_empty)).
    { unfold DE.bexp2bool.
      replace DE.default_val with (env_val PCG.env_empty) by reflexivity.
      apply to_pcg_exp_BLe. }
    rewrite HRHS.
    rewrite !SEM.to_pcg_exp_idx, !SEM.to_pcg_exp_zero.
    rewrite (to_pcg_exp_vrd_env_empty _ _ Hs0 Hs1).
    rewrite PCG_idx_exp_default. cbn [PCG.exp_default].
    specialize (Hle i).
    cbv [PCG.leExp].
    destruct (Rle_dec _ R0) as [Hl | Hl];
      [| exfalso; apply Hl; exact Hle].
    destruct (Rle_dec R0 R0) as [Hz | Hz];
      [reflexivity | exfalso; apply Hz; apply Rle_refl]. }
  assert (Hindep : SEM.exp_independent_of_acc
    (@CG.vrd (ary '{n} num) sin) (@CG.vwt (ary '{n} num) sout)).
  { intros p Hp. destruct (in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq]. subst p.
    apply exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hnames u w (eq_sym Hw)). }
  rewrite <- (CEB.ReLU1d_equiv_sem _ Hindep Hb).
  cbv [CG.A]. rewrite SEM.eval_assign.
  f_equal. apply interp_ReLU1d. exact Hb.
Qed.

(* -------------------------------------------------------------------------- *)
(* The generic whole-network AST (padding-2 conv1 on the shared 1x28x28       *)
(* input; loopacc-based layer commands; [CNN_Examples_LeNet5] buffer names)   *)
(* -------------------------------------------------------------------------- *)

Definition Tin  : data := ary '{1} (ary '{28} (ary '{28} num)).
Definition Tkc1 : data := ary '{6} (ary '{1} (ary '{5} (ary '{5} num))).
Definition Tbc1 : data := ary '{6} num.
Definition Tc1  : data := ary '{6} (ary '{28} (ary '{28} num)).
Definition Tp1  : data := ary '{6} (ary '{14} (ary '{14} num)).
Definition Tkc2 : data := ary '{16} (ary '{6} (ary '{5} (ary '{5} num))).
Definition Tbc2 : data := ary '{16} num.
Definition Tc2  : data := ary '{16} (ary '{10} (ary '{10} num)).
Definition Tp2  : data := ary '{16} (ary '{5} (ary '{5} num)).
Definition Tflat: data := ary '{(16*5*5)} num.
Definition Tfc1w: data := ary '{120} (ary '{(16*5*5)} num).
Definition Tfc1b: data := ary '{120} num.
Definition Tfc1 : data := ary '{120} num.
Definition Tfc2w: data := ary '{84} (ary '{120} num).
Definition Tfc2b: data := ary '{84} num.
Definition Tfc2 : data := ary '{84} num.
Definition Tfc3w: data := ary '{10} (ary '{84} num).
Definition Tfc3b: data := ary '{10} num.
Definition Tout : data := ary '{10} num.

Definition lenet5_gen_comm : CG.comm :=
  CG.seq ( CEO.Conv3d_comm 2 1
             (@CG.vrd Tbc1 "bc1") (@CG.vrd Tkc1 "kc1")
             (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1"),
  CG.seq ( @CEB.ReLU3d_comm 6 28 28
             (@CG.vrd Tc1 "c1") (@CG.vwt Tc1 "r1"),
  CG.seq ( @CEO.Maxpool3d_comm 6 28 28 2
             (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1"),
  CG.seq ( CEO.Conv3d_comm 0 1
             (@CG.vrd Tbc2 "bc2") (@CG.vrd Tkc2 "kc2")
             (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2"),
  CG.seq ( @CEB.ReLU3d_comm 16 10 10
             (@CG.vrd Tc2 "c2") (@CG.vwt Tc2 "r2"),
  CG.seq ( @CEO.Maxpool3d_comm 16 10 10 2
             (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2"),
  CG.seq ( @CEB.Flatten3d_comm 16 5 5
             (@CG.vrd Tp2 "p2") (@CG.vwt Tflat "flat"),
  CG.seq ( @CEO.Linear1d_comm (16*5*5) 120
             (@CG.vrd Tfc1w "fc1_w") (@CG.vrd Tfc1b "fc1_b")
             (@CG.vrd Tflat "flat") (@CG.vwt Tfc1 "fc1"),
  CG.seq ( @CEB.ReLU1d_comm 120
             (@CG.vrd Tfc1 "fc1") (@CG.vwt Tfc1 "fc1_relu"),
  CG.seq ( @CEO.Linear1d_comm 120 84
             (@CG.vrd Tfc2w "fc2_w") (@CG.vrd Tfc2b "fc2_b")
             (@CG.vrd Tfc1 "fc1_relu") (@CG.vwt Tfc2 "fc2"),
  CG.seq ( @CEB.ReLU1d_comm 84
             (@CG.vrd Tfc2 "fc2") (@CG.vwt Tfc2 "fc2_relu"),
  CG.seq ( @CEO.Linear1d_comm 84 10
             (@CG.vrd Tfc3w "fc3_w") (@CG.vrd Tfc3b "fc3_b")
             (@CG.vrd Tfc2 "fc2_relu") (@CG.vwt Tout "fc3"),
             @CEO.Softmax1d_comm 10
             (@CG.vrd Tout "fc3") (@CG.vwt Tout "output")
  )))))))))))).

(* -------------------------------------------------------------------------- *)
(* Functional layer values (route A), as functions of the initial env         *)
(* -------------------------------------------------------------------------- *)

Definition G1 (rho : PCG.env) : PCG.exp Tc1 :=
  @LF.Conv3d 28 28 1 6 5 2 LF.H5
    (SEM.to_pcg_exp (@CG.vrd Tkc1 "kc1") rho)
    (SEM.to_pcg_exp (@CG.vrd Tbc1 "bc1") rho)
    (SEM.to_pcg_exp (@CG.vrd Tin "input") rho).

Definition G4 (rho : PCG.env) : PCG.exp Tc2 :=
  @LF.Conv3d 14 14 6 16 5 0 LF.H5
    (SEM.to_pcg_exp (@CG.vrd Tkc2 "kc2") rho)
    (SEM.to_pcg_exp (@CG.vrd Tbc2 "bc2") rho)
    (@LF.Maxpool3d 6 28 (LF.ReLU3d (G1 rho))).

Definition G8 (rho : PCG.env) : PCG.exp Tfc1 :=
  @LF.Linear1d (16*5*5) 120
    (SEM.to_pcg_exp (@CG.vrd Tfc1w "fc1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc1b "fc1_b") rho)
    (@LF.Flatten3d 16 5 5 (@LF.Maxpool3d 16 10 (LF.ReLU3d (G4 rho)))).

Definition G10 (rho : PCG.env) : PCG.exp Tfc2 :=
  @LF.Linear1d 120 84
    (SEM.to_pcg_exp (@CG.vrd Tfc2w "fc2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc2b "fc2_b") rho)
    (LF.ReLU1d (G8 rho)).

(* Freshness of the initial environment: the loopacc temporary and the
   route-A intermediate accumulators are all undefined. *)
Definition net_fresh (rho : PCG.env) : Prop :=
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho /\
  PCG.StructUndefined LD.l1_acc rho /\
  PCG.StructUndefined LD.l2_acc rho /\
  PCG.StructUndefined LD.l3_acc rho /\
  PCG.StructUndefined LD.l4_acc rho /\
  PCG.StructUndefined LD.l5_acc rho /\
  PCG.StructUndefined LD.l6_acc rho /\
  PCG.StructUndefined LD.l7_acc rho.

(* A [Var] path can only be in [acc' q] when it is [q] itself; hence the
   route-B output buffer (whose paths are bracketed [Var]s) never aliases
   the route-A accumulators (whose paths are [AryIdx] chains). *)
Lemma in_acc_acc'_Var : forall (d : data) (q : DE.path) (s : string),
  @PCG.in_acc d (DE.Var s) (@PCG.acc' d q) -> q = DE.Var s.
Proof.
  induction d as [| n f d IHd]; intros q s Hin.
  - exact Hin.
  - simpl in Hin. destruct Hin as [i Hi].
    rewrite SEM.PCG_idxAcc_mk_vec in Hi.
    apply IHd in Hi. discriminate.
Qed.

(* ---- name-clash independence helpers ---- *)
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

(* tmp disjointness of a 1d output buffer *)
Lemma tmp_disj_vwt1 : forall (n : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (out : fin n),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p ((@CG.vwt (ary '{n} num) s) |{ out}).
Proof.
  intros n s Hneq p out Hp Hin.
  apply in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.

(* tmp disjointness of a 3d output buffer (maxp3d/conv3d shape) *)
Lemma tmp_disj_vwt3 : forall (n1 n2 n3 : nat) (s : string),
  (forall u : string, ("__tmp" <> s ++ "[" ++ u)%string) ->
  forall (p : DE.path) (fnum : fin n1) (i0 : fin n2) (i1 : fin n3),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p
        ((@CG.vwt (ary '{n1} (ary '{n2} (ary '{n3} num))) s) |{ fnum} |{ i0} |{ i1}).
Proof.
  intros n1 n2 n3 s Hneq p fnum i0 i1 Hp Hin.
  apply in_acc_tmp_scalar in Hp. subst p.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  apply SEM.in_acc_ary_inv in Hin.
  destruct (in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Heq].
  injection Heq as Heq. exact (Hneq u Heq).
Qed.


(* -------------------------------------------------------------------------- *)
(* Linear1d: single-output semantic equivalence                               *)
(* -------------------------------------------------------------------------- *)

Theorem Linear1d_sem_single : forall (m outnum : nat)
  (w : DE.exp (ary '{outnum} (ary '{m} num)))
  (b : DE.exp (ary '{outnum} num))
  (input : DE.exp (ary '{m} num))
  (output : DE.acc (ary '{outnum} num)) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc b OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc b output ->
  OSE.tmp_disjoint_from_output outnum output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Linear w b input)) rho =
  SEM.eval (CEO.Linear1d_comm w b input output) rho.
Proof.
  intros m outnum w b input output rho Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  unfold CG.A, COP.Linear, CEO.Linear1d_comm.
  rewrite SEM.eval_mkvSeq; [ | intros out;
    apply SEM.exp_independent_of_acc_add;
      [ | apply SEM.exp_independent_of_acc_idx; exact Hbo ];
    apply OSE.exp_independent_of_acc_sum; intro i;
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec;
    apply SEM.exp_independent_of_acc_mul;
      [ apply SEM.exp_independent_of_acc_idx; exact Hio
      | apply SEM.exp_independent_of_acc_idx;
        apply SEM.exp_independent_of_acc_idx; exact Hwo ] ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros out eta HPeta. split.
  - set (e := DE.mkvSeq (fun i : fin m => CD.mul (DE.idx input i) (DE.idx (DE.idx w out) i))).
    set (c := fun r : DE.exp num => CG.assign (CG.idxAcc output out, CD.add r (DE.idx b out))).
    assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
        (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
          CG.vwt tmp |:= CD.add (CD.mul (DE.idx input i) (DE.idx (DE.idx w out) i)) (CG.vrd tmp))
        '; CG.assign (CG.idxAcc output out, CD.add (CG.vrd tmp) (DE.idx b out))))
      = (@CG.loopacc num (fun tmp : string =>
        (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
          CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))
        '; c (CG.vrd tmp)))).
    { f_equal. apply functional_extensionality; intro tmp.
      assert (Hfor : CG.seqfor (fun i : fin m =>
                      CG.vwt tmp |:= CD.add (CD.mul (DE.idx input i) (DE.idx (DE.idx w out) i)) (CG.vrd tmp))
                  = CG.seqfor (fun i : fin m =>
                      CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))).
      { apply FTac.seqfor_extensionality; intro i.
        assert (Heq : CD.mul (DE.idx input i) (DE.idx (DE.idx w out) i) = DE.idx e i).
        { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
        rewrite Heq. reflexivity. }
      rewrite Hfor. reflexivity. }
    rewrite Hrhs.
    rewrite SEM.eval_assign.
    rewrite <- (SEM.eval_assign_aux 1 num _ _ eta).
    change (SEM.eval_aux (c (CD.sum e)) 1 eta =
      SEM.eval (@CG.loopacc num (fun tmp : string =>
        (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin m =>
          CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))
        '; c (CG.vrd tmp))) eta).
    unfold P in HPeta.
    assert (Hindep : @SEM.exp_independent_of_acc (ary '{m} num) num e SEM.wtmp_acc).
    { apply SEM.exp_independent_of_acc_mkvSeq. intro i.
      apply SEM.exp_independent_of_acc_mul.
      - apply SEM.exp_independent_of_acc_idx. exact Hi.
      - apply SEM.exp_independent_of_acc_idx. apply SEM.exp_independent_of_acc_idx. exact Hw. }
    assert (Hok : SEM.loopacc_continuation_ok c (CD.sum e)).
    { apply (OSE.Linear1d_cell_continuation_ok Hi Hw Hb out Hdisj). }
    assert (Hinst := @SEM.eval_csum_equiv m e c eta HPeta Hindep Hok).
    rewrite Hinst. reflexivity.
  - rewrite SEM.eval_assign.
    apply OSE.assign_preserves_StructUndefined_tmp.
    + intros p Hp Hout. apply (Hdisj p out Hp). exact Hout.
    + exact HPeta.
Qed.



(* -------------------------------------------------------------------------- *)
(* Softmax1d: single-output semantic equivalence                              *)
(* -------------------------------------------------------------------------- *)

Lemma softmax1d_continuation_ok_single : forall (n : nat)
  (input : DE.exp (ary '{n} num)) (output : DE.acc (ary '{n} num)),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  (forall (p : DE.path) (j : fin n),
     @PCG.in_acc num p OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num p (output |{ j})) ->
  SEM.loopacc_continuation_ok
    (fun r : DE.exp num => CG.seqfor (fun j : fin n =>
       (output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) r))
    (CD.sum (DE.mkvSeq (fun i : fin n => CD.pExp (DE.idx input i)))).
Proof.
  intros n input output Hi Hio Hdisj.
  set (e_final := CD.sum (DE.mkvSeq (fun i : fin n => CD.pExp (DE.idx input i)))).
  set (g := fun (j : fin n) (r : DE.exp num) => CD.div (CD.pExp (DE.idx input j)) r).
  assert (Hdisj_acc : OSE.tmp_disjoint_from_acc output).
  { intros p Hp Hout. unfold PCG.in_acc in Hout. simpl in Hout.
    destruct Hout as [j Hj]. apply (Hdisj p j Hp). exact Hj. }
  apply OSE.seqfor_scalar_assign_continuation_ok.
  - exact Hdisj_acc.
  - unfold e_final. apply OSE.exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hi.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hi.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hi.
  - intros j. unfold g, e_final. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hio.
    + apply OSE.exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hio.
  - intros j. unfold g. apply SEM.exp_independent_of_acc_div.
    + apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hio.
    + apply OSE.exp_independent_of_acc_REvar.
      intro Hc. apply (Hdisj_acc (DE.Var "__tmp") OSE.in_acc_tmp_scalar_acc Hc).
  - intros j rho0 eta v Hv Heta.
    rewrite !OSE.to_pcg_exp_div; f_equal.
    + rewrite !OSE.to_pcg_exp_pExp; f_equal.
      apply SEM.exp_independent_of_acc_eval with (a := OSE.tmp_scalar_acc).
      * apply SEM.exp_independent_of_acc_idx. exact Hi.
      * intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
        apply Heta. intro Hc. apply Hq. simpl. auto.
    + unfold CG.vrd. simpl. rewrite SEM.to_pcg_exp_REvar.
      rewrite PCG.update_eq by reflexivity. symmetry. exact Hv.
Qed.

Theorem Softmax1d_sem_single : forall (n : nat)
  (input : DE.exp (ary '{n} num))
  (output : DE.acc (ary '{n} num)) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  (forall (p : DE.path) (j : fin n),
     @PCG.in_acc num p OSE.tmp_scalar_acc ->
     ~ @PCG.in_acc num p (output |{ j})) ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Softmax1d input)) rho =
  SEM.eval (@CEO.Softmax1d_comm n input output) rho.
Proof.
  intros n input output rho Hi Hio Hdisj Hundef.
  unfold CG.A, COP.Softmax1d, CD.let_binding.
  set (e := DE.mkvSeq (fun i : fin n => CD.pExp (DE.idx input i))).
  assert (Hcell_indep : forall j,
    SEM.exp_independent_of_acc (CD.div (CD.pExp (DE.idx input j)) (CD.sum e)) output).
  { intros j. apply SEM.exp_independent_of_acc_div.
    - apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hio.
    - apply OSE.exp_independent_of_acc_sum. intro i.
      unfold e, DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hio. }
  rewrite SEM.eval_mkvSeq; [ | intros j; apply Hcell_indep ].
  apply eq_trans with (y := SEM.eval_aux (CG.seqfor (fun j : fin n =>
    (output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) (CD.sum e))) 1 rho).
  - rewrite SEM.eval_seqfor.
    assert (Hpoint : forall j,
      SEM.eval ((output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) (CD.sum e)) =
      SEM.eval_aux ((output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) (CD.sum e)) 1).
    { intro j. apply functional_extensionality; intro rho''.
      rewrite SEM.eval_assign. symmetry. apply SEM.eval_assign_aux. }
    replace (PCG.seqfor (fun j : fin n =>
               SEM.eval ((output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) (CD.sum e))) rho)
      with (PCG.seqfor (fun j : fin n =>
               SEM.eval_aux ((output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) (CD.sum e)) 1) rho).
    2: { apply f_equal with (f := fun h => PCG.seqfor h rho).
         apply functional_extensionality; intro j. symmetry. apply Hpoint. }
    rewrite SEM.eval_seqfor_aux. reflexivity.
  - assert (Hrhs : @CEO.Softmax1d_comm n input output =
      @CG.loopacc num (fun tmp : string =>
        (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun i : fin n =>
          CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp)) ';
        CG.seqfor (fun j : fin n =>
          (output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) (CG.vrd tmp)))).
    { unfold CEO.Softmax1d_comm. f_equal. apply functional_extensionality; intro tmp.
      assert (Hfor : CG.seqfor (fun i : fin n =>
                      CG.vwt tmp |:= CD.add (CD.pExp (DE.idx input i)) (CG.vrd tmp))
                  = CG.seqfor (fun i : fin n =>
                      CG.vwt tmp |:= CD.add (DE.idx e i) (CG.vrd tmp))).
      { apply FTac.seqfor_extensionality; intro i.
        assert (Heq_i : CD.pExp (DE.idx input i) = DE.idx e i).
        { unfold e, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
        rewrite Heq_i. reflexivity. }
      rewrite Hfor. reflexivity. }
    rewrite Hrhs.
    apply (@SEM.eval_csum_equiv n e
      (fun s : DE.exp num => CG.seqfor (fun j : fin n =>
        (output |{ j}) |:= CD.div (CD.pExp (DE.idx input j)) s)) rho).
    + exact Hundef.
    + unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro i.
      apply OSE.exp_independent_of_acc_pExp. apply SEM.exp_independent_of_acc_idx. exact Hi.
    + apply softmax1d_continuation_ok_single; assumption.
Qed.


(* -------------------------------------------------------------------------- *)
(* Maxpool2d: single-output semantic equivalence                              *)
(* -------------------------------------------------------------------------- *)

Theorem Maxpool2d_sem_single : forall (m1 m2 k : nat) (Hk : k > 0)
  (input : DE.exp (ary '{m1} (ary '{m2} num)))
  (output : DE.acc (ary '{m1/k} (ary '{m2/k} num))) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  OSE.tmp_disjoint_from_output_maxp2d m1 m2 k output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Maxpool2d m1 m2 k input)) rho =
  SEM.eval (@CEO.Maxpool2d_comm m1 m2 k input output) rho.
Proof.
  intros m1 m2 k Hk input output rho Hi Hio Hdisj Hundef.
  unfold CG.A, COP.Maxpool2d, CEO.Maxpool2d_comm.
  set (row := fun i0 : fin (m1/k) => DE.mkvSeq (fun j0 : fin (m2/k) =>
    (CD.max (DE.mkvSeq (fun i1 : fin k =>
      (CD.max (DE.mkvSeq (fun j1 : fin k =>
        DE.idx (DE.idx input (nat2fin (COP.fin_mul_add_lt_div m1 k i0 i1)))
               (nat2fin (COP.fin_mul_add_lt_div m2 k j0 j1)))))))))).
  assert (Hcell : forall (i0 : fin (m1/k)) (j0 : fin (m2/k)),
    SEM.exp_independent_of_acc
      (CD.max (DE.mkvSeq (fun i1 : fin k =>
        (CD.max (DE.mkvSeq (fun j1 : fin k =>
          DE.idx (DE.idx input (nat2fin (COP.fin_mul_add_lt_div m1 k i0 i1)))
                 (nat2fin (COP.fin_mul_add_lt_div m2 k j0 j1))))))))
      output).
  { intros i0 j0.
    apply OSE.exp_independent_of_acc_max. intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_max. intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    repeat apply SEM.exp_independent_of_acc_idx. exact Hio. }
  assert (Hrow_indep : forall i0, SEM.exp_independent_of_acc (row i0) output).
  { intros i0. unfold row. apply SEM.exp_independent_of_acc_mkvSeq. intros j0.
    apply Hcell. }
  rewrite SEM.eval_mkvSeq; [ | intros i0; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros i0 eta HPeta. split.
  - assert (Hcell_indep_i0 : forall j0,
      SEM.exp_independent_of_acc
        (CD.max (DE.mkvSeq (fun i1 : fin k =>
          CD.max (DE.mkvSeq (fun j1 : fin k =>
            DE.idx (DE.idx input (nat2fin (COP.fin_mul_add_lt_div m1 k i0 i1)))
                   (nat2fin (COP.fin_mul_add_lt_div m2 k j0 j1)))))))
        (output |{ i0})).
    { intros j0. unfold SEM.exp_independent_of_acc. intros p Hp.
      apply (Hcell i0 j0).
      simpl in Hp. destruct Hp as [j0' Hc']. simpl. exists i0. exists j0'. exact Hc'. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_indep_i0 ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros j0 eta' HPeta'. split.
    + set (e := DE.mkvSeq (OSE.MAXP2d_flat_cell m1 m2 k input i0 j0)).
      set (c' := fun r : DE.exp num => ((output |{ i0}) |{ j0}) |:= r).
      assert (Hrhs : (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (k * k) =>
            CG.If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat input
              (fin2nat i0 * k + Nat.div (fin2nat kk) k))
              (fin2nat j0 * k + Nat.modulo (fin2nat kk) k)) (CG.vrd tmp))
            (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat input
              (fin2nat i0 * k + Nat.div (fin2nat kk) k))
              (fin2nat j0 * k + Nat.modulo (fin2nat kk) k),
             CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))
          '; ((output |{ i0}) |{ j0}) |:= (CG.vrd tmp : DE.exp num)))
        = (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (k * k) =>
            CG.If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
            (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))
          '; ((output |{ i0}) |{ j0}) |:= (CG.vrd tmp : DE.exp num)))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : CG.seqfor (fun kk : fin (k * k) =>
                        CG.If (CD.gtExp (CD.safe_idx_nat (CD.safe_idx_nat input
                          (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                          (fin2nat j0 * k + Nat.modulo (fin2nat kk) k)) (CG.vrd tmp))
                        (CG.vwt tmp |:= CD.safe_idx_nat (CD.safe_idx_nat input
                          (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                          (fin2nat j0 * k + Nat.modulo (fin2nat kk) k),
                         CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))
                    = CG.seqfor (fun kk : fin (k * k) =>
                        CG.If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
                        (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))).
        { apply FTac.seqfor_extensionality; intro kk.
          assert (Heq : CD.safe_idx_nat (CD.safe_idx_nat input
                          (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                          (fin2nat j0 * k + Nat.modulo (fin2nat kk) k) = DE.idx e kk).
          { unfold e, OSE.MAXP2d_flat_cell, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity. }
          rewrite Heq. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      rewrite SEM.eval_assign.
      rewrite <- (SEM.eval_assign_aux 1 num _ _ eta').
      change (SEM.eval_aux (c' (CD.max (DE.mkvSeq (fun i1 : fin k =>
        (CD.max (DE.mkvSeq (fun j1 : fin k =>
          DE.idx (DE.idx input (nat2fin (COP.fin_mul_add_lt_div m1 k i0 i1)))
                 (nat2fin (COP.fin_mul_add_lt_div m2 k j0 j1))))))))) 1 eta' =
        SEM.eval (@CG.loopacc num (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (k * k) =>
            CG.If (CD.gtExp (DE.idx e kk) (CG.vrd tmp))
            (CG.vwt tmp |:= DE.idx e kk, CG.vwt tmp |:= (CG.vrd tmp : DE.exp num)))
          '; c' (CG.vrd tmp))) eta').
      assert (Hmax_eq : SEM.to_pcg_exp (CD.max (DE.mkvSeq (fun i1 : fin k =>
        (CD.max (DE.mkvSeq (fun j1 : fin k =>
          DE.idx (DE.idx input (nat2fin (COP.fin_mul_add_lt_div m1 k i0 i1)))
                 (nat2fin (COP.fin_mul_add_lt_div m2 k j0 j1)))))))) eta' =
        SEM.to_pcg_exp (CD.max e) eta').
      { unfold e. apply OSE.MAXP2d_nested_max_flat. exact Hk. }
      assert (Heq_aux : SEM.eval_aux (c' (CD.max (DE.mkvSeq (fun i1 : fin k =>
        (CD.max (DE.mkvSeq (fun j1 : fin k =>
          DE.idx (DE.idx input (nat2fin (COP.fin_mul_add_lt_div m1 k i0 i1)))
                 (nat2fin (COP.fin_mul_add_lt_div m2 k j0 j1))))))))) 1 eta' =
        SEM.eval_aux (c' (CD.max e)) 1 eta').
      { unfold c'. rewrite !SEM.eval_assign_aux. f_equal. exact Hmax_eq. }
      rewrite Heq_aux.
      apply SEM.eval_cmax_equiv.
      * exact HPeta'.
      * unfold e. apply SEM.exp_independent_of_acc_mkvSeq. intro kk.
        unfold OSE.MAXP2d_flat_cell.
        repeat apply OSE.safe_idx_nat_independent.
        exact Hi.
      * apply OSE.Maxpool2d_cell_continuation_ok. exact Hi. exact Hdisj.
    + rewrite SEM.eval_assign.
      apply OSE.assign_preserves_StructUndefined_tmp.
      * intros p Hp Hout. apply (Hdisj p i0 j0 Hp). exact Hout.
      * exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j0 rho'. apply PCG.assign_not_in_acc.
      intros Hc. apply (Hdisj OSE.tmp_path i0 j0 OSE.in_acc_tmp_scalar_acc). exact Hc.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool3d: single-output semantic equivalence                              *)
(* -------------------------------------------------------------------------- *)

Theorem Maxpool3d_sem_single : forall (filernum m1 m2 k : nat)
  (Hf : filernum > 0) (Hk : k > 0)
  (input : DE.exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))) (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  OSE.tmp_disjoint_from_output_maxp3d filernum m1 m2 k output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, @COP.Maxpool3d filernum m1 m2 k input)) rho =
  SEM.eval (@CEO.Maxpool3d_comm filernum m1 m2 k input output) rho.
Proof.
  intros filernum m1 m2 k Hf Hk input output rho Hi Hio Hdisj Hundef.
  unfold CG.A, COP.Maxpool3d, CEO.Maxpool3d_comm.
  assert (Hrow_indep : forall nu,
    SEM.exp_independent_of_acc
      (DE.mkvSeq (fun i0 : fin (m1/k) => DE.mkvSeq (fun i1 : fin (m2/k) =>
        (CD.max (DE.mkvSeq (fun j0 : fin k => (CD.max (DE.mkvSeq (fun j1 : fin k =>
          DE.idx (DE.idx (DE.idx input nu)
            (nat2fin (COP.fin_mul_add_lt_div m1 k i0 j0)))
            (nat2fin (COP.fin_mul_add_lt_div m2 k i1 j1)))))))))))
      output).
  { intro nu. apply SEM.exp_independent_of_acc_mkvSeq. intro i0.
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
  intros nu eta HPeta. split.
  - assert (Hin2d : SEM.exp_independent_of_acc (DE.idx input nu) (output |{ nu})).
    { apply CEO.exp_independent_of_acc_weaken_ary.
      apply SEM.exp_independent_of_acc_idx. exact Hio. }
    assert (Hdisj2d : @OSE.tmp_disjoint_from_output_maxp2d m1 m2 k (output |{ nu})).
    { intros p i0 i1 Hp. exact (Hdisj p nu i0 i1 Hp). }
    change (SEM.eval (CG.A ((output |{ nu}), @COP.Maxpool2d m1 m2 k (DE.idx input nu))) eta =
            SEM.eval (@CEO.Maxpool2d_comm m1 m2 k (DE.idx input nu) (output |{ nu})) eta).
    apply (Maxpool2d_sem_single m1 m2 k Hk (DE.idx input nu) (output |{ nu}) eta).
    + apply SEM.exp_independent_of_acc_idx. exact Hi.
    + exact Hin2d.
    + exact Hdisj2d.
    + exact HPeta.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + apply PCG.assign_not_in_acc.
      intros Hc. simpl in Hc. destruct Hc as [i0 Hc]. simpl in Hc. destruct Hc as [i1 Hc].
      exact (Hdisj OSE.tmp_path nu i0 i1 OSE.in_acc_tmp_scalar_acc Hc).
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.


(* -------------------------------------------------------------------------- *)
(* Flatten3d: single-output semantic equivalence                              *)
(* -------------------------------------------------------------------------- *)

Lemma flatten_batch_sem_single : forall (batch channel m1 m2 : nat)
  (input : DE.exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (Hc : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (output : DE.acc (ary '{channel * m1 * m2} num)) (b : fin batch) (rho : PCG.env),
  SEM.exp_independent_of_acc (DE.idx input b) output ->
  SEM.eval (CG.assign (output, CD.join (CD.join (DE.idx input b)))) rho =
  SEM.eval (CG.seqfor (fun c : fin channel => CG.seqfor (fun i : fin m1 => CG.seqfor (fun j : fin m2 =>
    CG.assign (DE.idxAcc output (CEB.flatten_idx c i j),
      DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))))) rho.
Proof.
  intros batch channel m1 m2 input Hc Hm1 Hm2 output b rho Hin.
  rewrite (OSE.join_mkvSeq (CD.join (DE.idx input b))).
  rewrite (OSE.join_mkvSeq (DE.idx input b)).
  rewrite SEM.eval_mkvSeq.
  - rewrite !SEM.eval_seqfor.
    assert (Heq1 : PCG.seqfor (fun c : fin channel =>
      SEM.eval (CG.seqfor (fun i : fin m1 => CG.seqfor (fun j : fin m2 =>
        (DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j)))) =
      PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
        let '(i, j) := V.idx_1d_to_2d k in
        SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j)))).
    { apply PCG.seqfor_extensionality. intro c.
      rewrite (OSE.seqfor_2d_CG Hm1 Hm2 (fun i j =>
        (DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j)). reflexivity. }
    assert (Heq_m : channel * (m1 * m2) = (channel * m1) * m2) by (apply Nat.mul_assoc).
    assert (Heq2 : PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
      let '(i, j) := V.idx_1d_to_2d k in
      SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))) =
      PCG.seqfor (fun k : fin ((channel * m1) * m2) =>
        (fun k' : fin (channel * (m1 * m2)) =>
          let '(c, k0) := V.idx_1d_to_2d k' in
          let '(i, j) := V.idx_1d_to_2d k0 in
          SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))
        (OSE.fin_cast (eq_sym Heq_m) k))).
    { assert (Heq2' : PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
        let '(i, j) := V.idx_1d_to_2d k in
        SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))) =
        PCG.seqfor (fun k' : fin (channel * (m1 * m2)) =>
          let '(c, k0) := V.idx_1d_to_2d k' in
          let '(i, j) := V.idx_1d_to_2d k0 in
          SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))).
      { apply OSE.seqfor_2d_body; [assumption | apply Nat.mul_pos_pos; assumption ]. }
      rewrite Heq2'. rewrite -> (@OSE.seqfor_body_cast (channel * (m1 * m2)) ((channel * m1) * m2) Heq_m
        (fun k' : fin (channel * (m1 * m2)) =>
          let '(c, k0) := V.idx_1d_to_2d k' in
          let '(i, j) := V.idx_1d_to_2d k0 in
          SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))). reflexivity. }
    rewrite Heq1. rewrite Heq2.
    assert (Heq3 : PCG.seqfor (fun i : fin (channel * m1 * m2) =>
      SEM.eval ((DE.idxAcc output i) |:=
        (let '(i0, j) := V.idx_1d_to_2d i in
          DE.idx (DE.idx (DE.mkvSeq (fun k : fin (channel * m1) =>
            let '(i1, j0) := V.idx_1d_to_2d k in DE.idx (DE.idx (DE.idx input b) i1) j0)) i0) j))) =
      PCG.seqfor (fun k : fin ((channel * m1) * m2) =>
        let '(c, k0) := V.idx_1d_to_2d (OSE.fin_cast (eq_sym Heq_m) k) in
        let '(i, j) := V.idx_1d_to_2d k0 in
        SEM.eval ((DE.idxAcc output (CEB.flatten_idx c i j)) |:= DE.idx (DE.idx (DE.idx (DE.idx input b) c) i) j))).
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
      apply (f_equal (fun e => SEM.eval (CG.assign (DE.idxAcc output (CEB.flatten_idx c i j), e)))).
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
    apply SEM.exp_independent_of_acc_idx.
    apply SEM.exp_independent_of_acc_idx.
    exact Hin.
Qed.

Theorem Flatten3d_sem_single : forall (channel m1 m2 : nat)
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{channel * m1 * m2} num)) (rho : PCG.env),
  channel > 0 -> m1 > 0 -> m2 > 0 ->
  SEM.exp_independent_of_acc input output ->
  SEM.eval (CG.A (output, COP.Flatten3d input)) rho =
  SEM.eval (@CEB.Flatten3d_comm channel m1 m2 input output) rho.
Proof.
  intros channel m1 m2 input output rho Hc Hm1 Hm2 Hin.
  unfold CG.A, COP.Flatten3d, CEB.Flatten3d_comm.
  pose (input4d := DE.mkvSeq (fun _ : fin 1 => input)).
  pose (b0 := @nat2fin 1 0 (Nat.lt_0_succ 0)).
  assert (Hin' : SEM.exp_independent_of_acc (DE.idx input4d b0) output).
  { unfold input4d, DE.idx, DE.mkvSeq. rewrite V.v_idx_mk_vec. exact Hin. }
  assert (Hkey := flatten_batch_sem_single 1 channel m1 m2 input4d Hc Hm1 Hm2 output b0 rho Hin').
  unfold input4d in Hkey.
  unfold DE.idx, DE.mkvSeq in Hkey.
  rewrite V.v_idx_mk_vec in Hkey.
  cbv beta in Hkey.
  exact Hkey.
Qed.


(* -------------------------------------------------------------------------- *)
(* Conv3d: single-output semantic equivalence                                 *)
(* -------------------------------------------------------------------------- *)

Lemma conv3d_cell_indep_single : forall (m1 m2 k channel filernum p : nat)
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{k} (ary '{k} num)))))
  (bias : DE.exp (ary '{filernum} num))
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{filernum}
    (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))))
  (fnum : fin filernum) (i0 : fin ((m1 - k + 2 * p) / 1 + 1))
  (j0 : fin ((m2 - k + 2 * p) / 1 + 1)),
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc bias output ->
  SEM.exp_independent_of_acc
    (CD.add (CD.sum (DE.mkvSeq (fun c : fin channel =>
      (CD.sum (DE.mkvSeq (fun i1 : fin k =>
        (CD.sum (DE.mkvSeq (fun j1 : fin k =>
          OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c i1 j1)))))))))
      (DE.idx bias fnum))
    output.
Proof.
  intros m1 m2 k channel filernum p w bias input output fnum i0 j0 Hio Hwo Hbo.
  apply SEM.exp_independent_of_acc_add.
  - apply OSE.exp_independent_of_acc_sum; intro c.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    apply OSE.exp_independent_of_acc_sum; intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec.
    unfold OSE.Conv3d_idx_cell.
    apply SEM.exp_independent_of_acc_mul.
    + repeat apply OSE.safe_idx_nat_independent.
      apply SEM.exp_independent_of_acc_idx.
      apply OSE.Padding3d_independent.
      exact Hio.
    + repeat apply SEM.exp_independent_of_acc_idx.
      exact Hwo.
  - apply SEM.exp_independent_of_acc_idx.
    exact Hbo.
Qed.

Theorem Conv3d_sem_single : forall (m1 m2 k channel filernum p : nat)
  (Hk : k > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (Hc : channel > 0) (Hf : filernum > 0)
  (w : DE.exp (ary '{filernum} (ary '{channel} (ary '{k} (ary '{k} num)))))
  (bias : DE.exp (ary '{filernum} num))
  (input : DE.exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : DE.acc (ary '{filernum}
    (ary '{(m1 - k + 2 * p) / 1 + 1} (ary '{(m2 - k + 2 * p) / 1 + 1} num))))
  (rho : PCG.env),
  SEM.exp_independent_of_acc input OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc w OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc bias OSE.tmp_scalar_acc ->
  SEM.exp_independent_of_acc input output ->
  SEM.exp_independent_of_acc w output ->
  SEM.exp_independent_of_acc bias output ->
  OSE.tmp_disjoint_from_output_conv3d m1 m2 k k filernum p 1 output ->
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) rho ->
  SEM.eval (CG.A (output, COP.Conv3d p 1 bias w input)) rho =
  SEM.eval (CEO.Conv3d_comm p 1 bias w input output) rho.
Proof.
  intros m1 m2 k channel filernum p Hk Hm1 Hm2 Hc Hf w bias input output rho
    Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  unfold CG.A, COP.Conv3d, CD.let_binding, CEO.Conv3d_comm.
  set (row := fun fnum : fin filernum =>
    DE.mkvSeq (fun i0 : fin ((m1 - k + 2 * p) / 1 + 1) =>
      DE.mkvSeq (fun j0 : fin ((m2 - k + 2 * p) / 1 + 1) =>
        CD.add (CD.sum (DE.mkvSeq (fun c : fin channel =>
          (CD.sum (DE.mkvSeq (fun i1 : fin k =>
            (CD.sum (DE.mkvSeq (fun j1 : fin k =>
              OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c i1 j1)))))))))
          (DE.idx bias fnum)))).
  assert (Hrow_indep : forall fnum, SEM.exp_independent_of_acc (row fnum) output).
  { intros fnum. unfold row. apply SEM.exp_independent_of_acc_mkvSeq; intro i0.
    apply SEM.exp_independent_of_acc_mkvSeq; intro j0.
    apply conv3d_cell_indep_single; assumption. }
  rewrite SEM.eval_mkvSeq; [ | intros fnum; apply Hrow_indep ].
  rewrite !SEM.eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta).
  apply SEM.seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros fnum eta HPeta. split.
  - assert (Hcell_indep_fnum : forall i0 j0,
      SEM.exp_independent_of_acc
        (CD.add (CD.sum (DE.mkvSeq (fun c =>
          (CD.sum (DE.mkvSeq (fun i1 =>
            (CD.sum (DE.mkvSeq (fun j1 =>
              OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c i1 j1)))))))))
          (DE.idx bias fnum))
        (output |{ fnum})).
    { intros i0 j0. intros p0 Hp.
      apply (conv3d_cell_indep_single m1 m2 k channel filernum p
        w bias input output fnum i0 j0 Hio Hwo Hbo).
      apply SEM.in_acc_ary_inv with (i := fnum). exact Hp. }
    unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros i0;
      apply SEM.exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_indep_fnum ].
    rewrite !SEM.eval_seqfor.
    apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros i0 eta' HPeta'. split.
    + assert (Hcell_indep_i0 : forall j0,
        SEM.exp_independent_of_acc
          (CD.add (CD.sum (DE.mkvSeq (fun c =>
            (CD.sum (DE.mkvSeq (fun i1 =>
              (CD.sum (DE.mkvSeq (fun j1 =>
                OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c i1 j1)))))))))
            (DE.idx bias fnum))
          ((output |{ fnum}) |{ i0})).
      { intros j0. intros p0 Hp.
        apply (conv3d_cell_indep_single m1 m2 k channel filernum p
          w bias input output fnum i0 j0 Hio Hwo Hbo).
        apply SEM.in_acc_ary_inv with (i := fnum).
        apply SEM.in_acc_ary_inv with (i := i0).
        exact Hp. }
      unfold row in |- *. rewrite SEM.eval_mkvSeq; [ | intros j0; apply Hcell_indep_i0 ].
      rewrite !SEM.eval_seqfor.
      apply SEM.seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros j0 eta'' HPeta''. split.
      * set (e := DE.mkvSeq (OSE.Conv3d_flat_cell m1 m2 k k channel p 1 w input fnum i0 j0)).
        set (c := fun r : DE.exp num =>
          (((output |{ fnum}) |{ i0}) |{ j0}) |:= CD.add r (DE.idx bias fnum)).
        rewrite (FTac.reduce_loopacc_named_sem _ _ (fun tmp : string =>
          (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * k * k) =>
            CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp)) eta'').
        2: { intros tmp. apply functional_extensionality. intro rho1.
             cbn beta zeta iota. repeat f_equal.
             all: try reflexivity.
             all: try (apply functional_extensionality; intro kk; repeat f_equal;
               assert (Heq : CD.mul (CD.safe_idx_nat (CD.safe_idx_nat
                            ((COP.Padding3d p input)|[nat2fin (CEO.conv3d_flat_c_bound kk)])
                            (fin2nat i0 * 1 + Nat.div (Nat.modulo (fin2nat kk) (k * k)) k))
                            (fin2nat j0 * 1 + Nat.modulo (fin2nat kk) k))
                          (w|[fnum]|[nat2fin (CEO.conv3d_flat_c_bound kk)]|[nat2fin (CEO.conv3d_flat_i1_bound kk)]|[nat2fin (CEO.conv3d_flat_j1_bound kk)]) = DE.idx e kk)
               by (unfold e, DE.idx, DE.mkvSeq; rewrite V.v_idx_mk_vec; reflexivity);
               rewrite Heq; reflexivity). }
        rewrite SEM.eval_assign.
        rewrite <- (SEM.eval_assign_aux 1 num _ _ eta'').
        change (SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun c0 : fin channel =>
          (CD.sum (DE.mkvSeq (fun i1 : fin k =>
            (CD.sum (DE.mkvSeq (fun j1 : fin k =>
              OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c0 i1 j1)))))))))) 1 eta'' =
          SEM.eval (@CG.loopacc num (fun tmp : string =>
            (CG.vwt tmp |:= CD.zero) '; CG.seqfor (fun kk : fin (channel * k * k) =>
              CG.vwt tmp |:= CD.add (DE.idx e kk) (CG.vrd tmp)) '; c (CG.vrd tmp))) eta'').
        assert (Hsum_eq : SEM.to_pcg_exp (CD.sum (DE.mkvSeq (fun c0 : fin channel =>
          (CD.sum (DE.mkvSeq (fun i1 : fin k =>
            (CD.sum (DE.mkvSeq (fun j1 : fin k =>
              OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c0 i1 j1))))))))) eta'' =
          SEM.to_pcg_exp (CD.sum e) eta'').
        { unfold e. apply (OSE.Conv3d_sum_flatten p w input); lia. }
        assert (Heq_aux : SEM.eval_aux (c (CD.sum (DE.mkvSeq (fun c0 : fin channel =>
          (CD.sum (DE.mkvSeq (fun i1 : fin k =>
            (CD.sum (DE.mkvSeq (fun j1 : fin k =>
              OSE.Conv3d_idx_cell m1 m2 p 1 w input fnum i0 j0 c0 i1 j1)))))))))) 1 eta'' =
          SEM.eval_aux (c (CD.sum e)) 1 eta'').
        { unfold c. rewrite !SEM.eval_assign_aux. f_equal.
          rewrite !SEM.to_pcg_exp_add. f_equal.
          { exact Hsum_eq. } }
        rewrite Heq_aux.
        apply SEM.eval_csum_equiv.
        { exact HPeta''. }
        { unfold e. apply SEM.exp_independent_of_acc_mkvSeq; intro kk.
          unfold OSE.Conv3d_flat_cell.
          apply SEM.exp_independent_of_acc_mul.
          { repeat apply OSE.safe_idx_nat_independent.
            apply SEM.exp_independent_of_acc_idx.
            apply OSE.Padding3d_independent.
            exact Hi. }
          { repeat apply SEM.exp_independent_of_acc_idx.
            exact Hw. } }
        { apply (OSE.Conv3d_cell_continuation_ok Hi Hw Hb fnum i0 j0 Hdisj). }
      * rewrite SEM.eval_assign.
        apply OSE.assign_preserves_StructUndefined_tmp.
        -- intros pth Hp Hout. apply (Hdisj pth fnum i0 j0 Hp). exact Hout.
        -- exact HPeta''.
    + rewrite SEM.eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta' OSE.tmp_path).
      * unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros j0 rho'. apply PCG.assign_not_in_acc.
        intros Hin. apply (Hdisj OSE.tmp_path fnum i0 j0 OSE.in_acc_tmp_scalar_acc). exact Hin.
      * apply PCG.StructUndefined_num in HPeta'. exact HPeta'.
  - rewrite SEM.eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta OSE.tmp_path).
    + unfold row in |- *. rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros i0 rho'.
      rewrite SEM.to_pcg_exp_mkvSeq. rewrite SEM.assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j0 rho''. apply PCG.assign_not_in_acc.
      intros Hin. apply (Hdisj OSE.tmp_path fnum i0 j0 OSE.in_acc_tmp_scalar_acc). exact Hin.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.


Lemma HB_c1 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (CEO.Conv3d_comm 2 1
             (@CG.vrd Tbc1 "bc1") (@CG.vrd Tkc1 "kc1")
             (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1")) eta =
  PCG.assign (@CG.vwt Tc1 "c1")
    (@LF.Conv3d 28 28 1 6 5 2 LF.H5
       (SEM.to_pcg_exp (@CG.vrd Tkc1 "kc1") eta)
       (SEM.to_pcg_exp (@CG.vrd Tbc1 "bc1") eta)
       (SEM.to_pcg_exp (@CG.vrd Tin "input") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tin "input") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tkc1 "kc1") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tbc1 "bc1") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tkc1 "kc1") (@CG.vwt Tc1 "c1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tbc1 "bc1") (@CG.vwt Tc1 "c1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output_conv3d 28 28 5 5 6 2 1 (@CG.vwt Tc1 "c1"))
    by (exact (tmp_disj_vwt3 6 28 28 "c1" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv3d_sem_single 28 28 5 1 6 2 LF.H5
    (Nat.lt_0_succ 27) (Nat.lt_0_succ 27) (Nat.lt_0_succ 0) (Nat.lt_0_succ 5)
    (@CG.vrd Tkc1 "kc1") (@CG.vrd Tbc1 "bc1") (@CG.vrd Tin "input") (@CG.vwt Tc1 "c1") eta
    Hi Hw Hb Hio Hwo Hbo Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  assert (Hinterp := BRC.interp_Conv3d 28 28 5 1 6 2 LF.H5
    (Nat.lt_0_succ 27) (Nat.lt_0_succ 27) (Nat.lt_0_succ 0) (Nat.lt_0_succ 5)
    (ltac:(lia) : 5 <= 28)
    (ltac:(lia) : 5 <= 28)
    (@CG.vrd Tkc1 "kc1") (@CG.vrd Tbc1 "bc1") (@CG.vrd Tin "input") eta
    (eq_refl : ary '{6} (ary '{28 + 2 * 2 - 5 + 1} (ary '{28 + 2 * 2 - 5 + 1} num)) =
               ary '{6} (ary '{(28 - 5 + 2 * 2) / 1 + 1} (ary '{(28 - 5 + 2 * 2) / 1 + 1} num)))).
  rewrite <- Hinterp. reflexivity.
Qed.

Lemma HB_p1 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Maxpool3d_comm 6 28 28 2
             (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1")) eta =
  PCG.assign (@CG.vwt Tp1 "p1")
    (@LF.Maxpool3d 6 28 (SEM.to_pcg_exp (@CG.vrd Tc1 "r1") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc1 "r1") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output_maxp3d 6 28 28 2 (@CG.vwt Tp1 "p1"))
    by (exact (tmp_disj_vwt3 6 14 14 "p1" (ltac:(str_neq1_tac)))).
  rewrite <- (Maxpool3d_sem_single 6 28 28 2 (Nat.lt_0_succ 5) (Nat.lt_0_succ 1)
    (@CG.vrd Tc1 "r1") (@CG.vwt Tp1 "p1") eta Hi Hio Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Maxpool3d 6 28 (@CG.vrd Tc1 "r1") eta).
  reflexivity.
Qed.

Lemma HB_c2 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (CEO.Conv3d_comm 0 1
             (@CG.vrd Tbc2 "bc2") (@CG.vrd Tkc2 "kc2")
             (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2")) eta =
  PCG.assign (@CG.vwt Tc2 "c2")
    (@LF.Conv3d 14 14 6 16 5 0 LF.H5
       (SEM.to_pcg_exp (@CG.vrd Tkc2 "kc2") eta)
       (SEM.to_pcg_exp (@CG.vrd Tbc2 "bc2") eta)
       (SEM.to_pcg_exp (@CG.vrd Tp1 "p1") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tp1 "p1") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tkc2 "kc2") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tbc2 "bc2") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tkc2 "kc2") (@CG.vwt Tc2 "c2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tbc2 "bc2") (@CG.vwt Tc2 "c2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output_conv3d 14 14 5 5 16 0 1 (@CG.vwt Tc2 "c2"))
    by (exact (tmp_disj_vwt3 16 10 10 "c2" (ltac:(str_neq1_tac)))).
  rewrite <- (Conv3d_sem_single 14 14 5 6 16 0 LF.H5
    (Nat.lt_0_succ 13) (Nat.lt_0_succ 13) (Nat.lt_0_succ 5) (Nat.lt_0_succ 15)
    (@CG.vrd Tkc2 "kc2") (@CG.vrd Tbc2 "bc2") (@CG.vrd Tp1 "p1") (@CG.vwt Tc2 "c2") eta
    Hi Hw Hb Hio Hwo Hbo Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  assert (Hinterp := BRC.interp_Conv3d 14 14 5 6 16 0 LF.H5
    (Nat.lt_0_succ 13) (Nat.lt_0_succ 13) (Nat.lt_0_succ 5) (Nat.lt_0_succ 15)
    (ltac:(lia) : 5 <= 14)
    (ltac:(lia) : 5 <= 14)
    (@CG.vrd Tkc2 "kc2") (@CG.vrd Tbc2 "bc2") (@CG.vrd Tp1 "p1") eta
    (eq_refl : ary '{16} (ary '{14 + 2 * 0 - 5 + 1} (ary '{14 + 2 * 0 - 5 + 1} num)) =
               ary '{16} (ary '{(14 - 5 + 2 * 0) / 1 + 1} (ary '{(14 - 5 + 2 * 0) / 1 + 1} num)))).
  rewrite <- Hinterp. reflexivity.
Qed.

Lemma HB_p2 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Maxpool3d_comm 16 10 10 2
             (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2")) eta =
  PCG.assign (@CG.vwt Tp2 "p2")
    (@LF.Maxpool3d 16 10 (SEM.to_pcg_exp (@CG.vrd Tc2 "r2") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tc2 "r2") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output_maxp3d 16 10 10 2 (@CG.vwt Tp2 "p2"))
    by (exact (tmp_disj_vwt3 16 5 5 "p2" (ltac:(str_neq1_tac)))).
  rewrite <- (Maxpool3d_sem_single 16 10 10 2 (Nat.lt_0_succ 15) (Nat.lt_0_succ 1)
    (@CG.vrd Tc2 "r2") (@CG.vwt Tp2 "p2") eta Hi Hio Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Maxpool3d 16 10 (@CG.vrd Tc2 "r2") eta).
  reflexivity.
Qed.

Lemma HB_flat : forall (eta : PCG.env),
  SEM.eval (@CEB.Flatten3d_comm 16 5 5
             (@CG.vrd Tp2 "p2") (@CG.vwt Tflat "flat")) eta =
  PCG.assign (@CG.vwt Tflat "flat")
    (@LF.Flatten3d 16 5 5 (SEM.to_pcg_exp (@CG.vrd Tp2 "p2") eta)) eta.
Proof.
  intros eta.
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tp2 "p2") (@CG.vwt Tflat "flat"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  rewrite <- (Flatten3d_sem_single 16 5 5 (@CG.vrd Tp2 "p2") (@CG.vwt Tflat "flat") eta
    (Nat.lt_0_succ 15) (Nat.lt_0_succ 4) (Nat.lt_0_succ 4) Hio).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Flatten3d 16 5 5
    (Nat.lt_0_succ 15) (Nat.lt_0_succ 4) (Nat.lt_0_succ 4) (@CG.vrd Tp2 "p2") eta).
  reflexivity.
Qed.

Lemma HB_fc1 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear1d_comm (16*5*5) 120
             (@CG.vrd Tfc1w "fc1_w") (@CG.vrd Tfc1b "fc1_b")
             (@CG.vrd Tflat "flat") (@CG.vwt Tfc1 "fc1")) eta =
  PCG.assign (@CG.vwt Tfc1 "fc1")
    (@LF.Linear1d (16*5*5) 120
       (SEM.to_pcg_exp (@CG.vrd Tfc1w "fc1_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc1b "fc1_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tflat "flat") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tflat "flat") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tfc1w "fc1_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tfc1b "fc1_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tflat "flat") (@CG.vwt Tfc1 "fc1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tfc1w "fc1_w") (@CG.vwt Tfc1 "fc1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tfc1b "fc1_b") (@CG.vwt Tfc1 "fc1"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output 120 (@CG.vwt Tfc1 "fc1"))
    by (exact (tmp_disj_vwt1 120 "fc1" (ltac:(str_neq1_tac)))).
  rewrite <- (Linear1d_sem_single (16*5*5) 120
    (@CG.vrd Tfc1w "fc1_w") (@CG.vrd Tfc1b "fc1_b") (@CG.vrd Tflat "flat")
    (@CG.vwt Tfc1 "fc1") eta Hi Hw Hb Hio Hwo Hbo Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Linear1d (16*5*5) 120
    (@CG.vrd Tfc1w "fc1_w") (@CG.vrd Tfc1b "fc1_b") (@CG.vrd Tflat "flat") eta).
  reflexivity.
Qed.

Lemma HB_fc2 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear1d_comm 120 84
             (@CG.vrd Tfc2w "fc2_w") (@CG.vrd Tfc2b "fc2_b")
             (@CG.vrd Tfc1 "fc1_relu") (@CG.vwt Tfc2 "fc2")) eta =
  PCG.assign (@CG.vwt Tfc2 "fc2")
    (@LF.Linear1d 120 84
       (SEM.to_pcg_exp (@CG.vrd Tfc2w "fc2_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc2b "fc2_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc1 "fc1_relu") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tfc1 "fc1_relu") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tfc2w "fc2_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tfc2b "fc2_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tfc1 "fc1_relu") (@CG.vwt Tfc2 "fc2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tfc2w "fc2_w") (@CG.vwt Tfc2 "fc2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tfc2b "fc2_b") (@CG.vwt Tfc2 "fc2"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output 84 (@CG.vwt Tfc2 "fc2"))
    by (exact (tmp_disj_vwt1 84 "fc2" (ltac:(str_neq1_tac)))).
  rewrite <- (Linear1d_sem_single 120 84
    (@CG.vrd Tfc2w "fc2_w") (@CG.vrd Tfc2b "fc2_b") (@CG.vrd Tfc1 "fc1_relu")
    (@CG.vwt Tfc2 "fc2") eta Hi Hw Hb Hio Hwo Hbo Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Linear1d 120 84
    (@CG.vrd Tfc2w "fc2_w") (@CG.vrd Tfc2b "fc2_b") (@CG.vrd Tfc1 "fc1_relu") eta).
  reflexivity.
Qed.

Lemma HB_fc3 : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Linear1d_comm 84 10
             (@CG.vrd Tfc3w "fc3_w") (@CG.vrd Tfc3b "fc3_b")
             (@CG.vrd Tfc2 "fc2_relu") (@CG.vwt Tout "fc3")) eta =
  PCG.assign (@CG.vwt Tout "fc3")
    (@LF.Linear1d 84 10
       (SEM.to_pcg_exp (@CG.vrd Tfc3w "fc3_w") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc3b "fc3_b") eta)
       (SEM.to_pcg_exp (@CG.vrd Tfc2 "fc2_relu") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tfc2 "fc2_relu") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hw : SEM.exp_independent_of_acc (@CG.vrd Tfc3w "fc3_w") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hb : SEM.exp_independent_of_acc (@CG.vrd Tfc3b "fc3_b") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tfc2 "fc2_relu") (@CG.vwt Tout "fc3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hwo : SEM.exp_independent_of_acc (@CG.vrd Tfc3w "fc3_w") (@CG.vwt Tout "fc3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hbo : SEM.exp_independent_of_acc (@CG.vrd Tfc3b "fc3_b") (@CG.vwt Tout "fc3"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : OSE.tmp_disjoint_from_output 10 (@CG.vwt Tout "fc3"))
    by (exact (tmp_disj_vwt1 10 "fc3" (ltac:(str_neq1_tac)))).
  rewrite <- (Linear1d_sem_single 84 10
    (@CG.vrd Tfc3w "fc3_w") (@CG.vrd Tfc3b "fc3_b") (@CG.vrd Tfc2 "fc2_relu")
    (@CG.vwt Tout "fc3") eta Hi Hw Hb Hio Hwo Hbo Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Linear1d 84 10
    (@CG.vrd Tfc3w "fc3_w") (@CG.vrd Tfc3b "fc3_b") (@CG.vrd Tfc2 "fc2_relu") eta).
  reflexivity.
Qed.

Lemma HB_sm : forall (eta : PCG.env),
  @PCG.StructUndefined num (PCG.acc' OSE.tmp_path) eta ->
  SEM.eval (@CEO.Softmax1d_comm 10
             (@CG.vrd Tout "fc3") (@CG.vwt Tout "output")) eta =
  PCG.assign (@CG.vwt Tout "output")
    (LF.Softmax1d (SEM.to_pcg_exp (@CG.vrd Tout "fc3") eta)) eta.
Proof.
  intros eta Htmp.
  assert (Hi : SEM.exp_independent_of_acc (@CG.vrd Tout "fc3") OSE.tmp_scalar_acc)
    by (apply vrd_ary_indep_tmp; str_neq1_tac).
  assert (Hio : SEM.exp_independent_of_acc (@CG.vrd Tout "fc3") (@CG.vwt Tout "output"))
    by (apply vrd_ary_indep_vwt_ary; str_neq2_tac).
  assert (Hdisj : forall (p : DE.path) (j : fin 10),
    @PCG.in_acc num p OSE.tmp_scalar_acc ->
    ~ @PCG.in_acc num p ((@CG.vwt Tout "output") |{ j}))
    by (exact (tmp_disj_vwt1 10 "output" (ltac:(str_neq1_tac)))).
  rewrite <- (Softmax1d_sem_single 10 (@CG.vrd Tout "fc3") (@CG.vwt Tout "output") eta
    Hi Hio Hdisj Htmp).
  cbv [CG.A]. rewrite SEM.eval_assign.
  rewrite (BRC.interp_Softmax1d 10 (@CG.vrd Tout "fc3") eta).
  reflexivity.
Qed.


(* -------------------------------------------------------------------------- *)
(* The whole-network bridge                                                   *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_LeNet5 : forall (rho : PCG.env) (p : DE.path),
  @PCG.in_acc Tout p (@CG.vwt Tout "output") ->
  net_fresh rho ->
  (forall (c : fin 6) (i0 i1 : fin 28),
     (PCG.idx (PCG.idx (PCG.idx (G1 rho) c) i0) i1 <= R0)%R) ->
  (forall (c : fin 16) (i0 i1 : fin 10),
     (PCG.idx (PCG.idx (PCG.idx (G4 rho) c) i0) i1 <= R0)%R) ->
  (forall (i : fin 120), (PCG.idx (G8 rho) i <= R0)%R) ->
  (forall (i : fin 84), (PCG.idx (G10 rho) i <= R0)%R) ->
  SEM.eval lenet5_gen_comm rho p =
  LI.lenet5_comm
    (SEM.to_pcg_exp (@CG.vrd Tin "input") rho)
    (SEM.to_pcg_exp (@CG.vrd Tkc1 "kc1") rho)
    (SEM.to_pcg_exp (@CG.vrd Tbc1 "bc1") rho)
    (SEM.to_pcg_exp (@CG.vrd Tkc2 "kc2") rho)
    (SEM.to_pcg_exp (@CG.vrd Tbc2 "bc2") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc1w "fc1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc1b "fc1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc2w "fc2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc2b "fc2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc3w "fc3_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc3b "fc3_b") rho)
    (@CG.vwt Tout "output") rho p.
Proof.
  intros rho p Hinacc Hfresh Hr1 Hr2 Hr3 Hr4.
  destruct Hfresh as [Htmp [Hl1 [Hl2 [Hl3 [Hl4 [Hl5 [Hl6 Hl7]]]]]]].
  (* Route-A side: collapse [lenet5_comm] to the functional assignment. *)
  assert (HfreshA : LD.lenet5_fresh (@CG.vwt Tout "output") rho).
  { unfold LD.lenet5_fresh. repeat split; try assumption;
    intros p0 Hin0 Hin1;
    destruct (in_acc_vwt_bracket _ _ _ _ _ Hin0) as [u Heq]; subst p0;
    apply in_acc_acc'_Var in Hin1; injection Hin1 as Hin1; discriminate. }
  rewrite (LD.A_LeNet5
    (SEM.to_pcg_exp (@CG.vrd Tin "input") rho)
    (SEM.to_pcg_exp (@CG.vrd Tkc1 "kc1") rho)
    (SEM.to_pcg_exp (@CG.vrd Tbc1 "bc1") rho)
    (SEM.to_pcg_exp (@CG.vrd Tkc2 "kc2") rho)
    (SEM.to_pcg_exp (@CG.vrd Tbc2 "bc2") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc1w "fc1_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc1b "fc1_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc2w "fc2_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc2b "fc2_b") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc3w "fc3_w") rho)
    (SEM.to_pcg_exp (@CG.vrd Tfc3b "fc3_b") rho)
    Hinacc HfreshA).
  cbv [DR.A]. cbv beta.
  (* Route-B side: 13-step forward simulation. *)
  unfold lenet5_gen_comm.
  (* c1: conv1 (padding 2) *)
  rewrite eval_seq'.
  rewrite HB_c1; [| exact Htmp].
  (* r1: relu3d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU3d_buf (n1:=6) (n2:=28) (n3:=28) "c1" "r1");
    [| discriminate | discriminate | str_neq_tac |
       intros c i0 i1;
       rewrite SEM.vrd_after_own_vwt by discriminate;
       exact (Hr1 c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* p1: maxpool *)
  rewrite eval_seq'.
  rewrite HB_p1; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* c2: conv2 (padding 0) *)
  rewrite eval_seq'.
  rewrite HB_c2; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* r2: relu3d *)
  rewrite eval_seq'.
  rewrite (bridge_ReLU3d_buf (n1:=16) (n2:=10) (n3:=10) "c2" "r2");
    [| discriminate | discriminate | str_neq_tac |
       intros c i0 i1;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr2 c i0 i1)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* p2: maxpool *)
  rewrite eval_seq'.
  rewrite HB_p2; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* flat: flatten *)
  rewrite eval_seq'.
  rewrite HB_flat.
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* fc1: linear *)
  rewrite eval_seq'.
  rewrite HB_fc1; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* fc1_relu: relu1d *)
  rewrite eval_seq'.
  erewrite (bridge_ReLU1d_buf (n:=120) "fc1" "fc1_relu");
    [| discriminate | discriminate | str_neq_tac |
       intros i;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr3 i)].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  (* fc2: linear *)
  rewrite eval_seq'.
  rewrite HB_fc2; [| su_tmp_tac].
  rewrite SEM.vrd_after_own_vwt by discriminate.
  repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac.
  (* fc2_relu: relu1d *)
  rewrite eval_seq'.
  erewrite (bridge_ReLU1d_buf (n:=84) "fc2" "fc2_relu");
    [| discriminate | discriminate | str_neq_tac |
       intros i;
       repeat rewrite SEM.vrd_after_own_vwt by discriminate;
       repeat rewrite vrd_after_other_vwt_ary_gen by str_neq_tac;
       exact (Hr4 i)].
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

Print Assumptions Bridge_LeNet5.
