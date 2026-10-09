(* ========================================================================= *)
(* MiniTransformer_AST_Faithful.v                                            *)
(*                                                                           *)
(* Milestone T6': the FAITHFUL route-B AST for the mini GPT-style            *)
(* decoder-only network (b = 1, s = 8, h = 2, d = 16, dm = 32, df = 32,      *)
(* v = 8), replacing the hand-optimised AST of MiniTransformer_AST.v as      *)
(* the bridge vehicle.                                                       *)
(*                                                                           *)
(* Method (the "faithful" rebuild): every stage of the AST is a plain        *)
(* [seqfor] nest of scalar [assign]s whose right-hand side is the SYNTACTIC  *)
(* transcription of the corresponding route-A functional leaf expression     *)
(* ([Ops_Transformer.LayerNorm3d], [Attention_DPIA.MHABlock] sub-terms,      *)
(* ...), built with the same combinators ([CNN_Defs.add]/[CNN_Defs.mul]/[CNN_Defs.sum] vs      *)
(* [Proof_CodeGen.add]/[Proof_CodeGen.mul]/[Proof_CodeGen.sum], [DataExp.mkvSeq] vs [Proof_CodeGen.mkvSeq]).  There are   *)
(* no [loopacc] accumulator caches, no staged attention score buffers, and   *)
(* no hand-optimised loop structures: each stage's semantic equivalence      *)
(*                                                                           *)
(*     eval (ast_stage X .. out) rho                                         *)
(*       = Proof_CodeGen.assign out (RouteA_Op (to_pcg_exp X rho) ..) rho              *)
(*                                                                           *)
(* closes by [eval_mkvSeq] (whole-array assign = seqfor of cell assigns)     *)
(* plus the per-combinator [to_pcg_exp] homomorphism lemmas — the bridge is  *)
(* structural, not a simulation over differing computations.                 *)
(*                                                                           *)
(* Remaining honest deltas vs route A (both forced by the extraction/C       *)
(* pipeline, both documented in the T5 report):                              *)
(*   1. The embedding Gather2d is unrolled over the 8 positions with the     *)
(*      token indices baked in ([mt_toks] = 3,1,4,1,5,2,6,0): a host-level   *)
(*      index map [fin 8 -> fin 8] cannot be evaluated on the symbolic loop  *)
(*      indices used by the extraction-based printer.  The bridge            *)
(*      instantiates route A's [toks] with [mt_toks].                        *)
(*   2. The GELU sqrt(2/pi) coefficient is read from the environment cell    *)
(*      "gelu_c" (an [REvar] leaf): [PI]/[R_sqrt.sqrt] are not realisable    *)
(*      in extraction (verified: building [REconst PI] crashes the extracted *)
(*      OCaml with the unrealisable axiom [sig_forall_dec]).  The bridge     *)
(*      carries the premise [rho (Var "gelu_c") = Some gelu_sqrt_2_pi]; the  *)
(*      generated C initialises the global [gelu_c] with the double literal  *)
(*      0.7978845608028654, whose rounding (rel. ~4e-18) is below float32    *)
(*      epsilon and is covered by the NumPy validation like every other      *)
(*      literal constant.                                                    *)
(*                                                                           *)
(* This file modifies nothing else; it is in _CoqProject (main build).       *)
(* No Admitted, no Axiom.                                                    *)
(* ========================================================================= *)

From Stdlib Require Import Reals String Arith Lia Bool ZArith.
From Stdlib Require Import Logic.FunctionalExtensionality Logic.ProofIrrelevance.
From Stdlib Require Import Extraction.
Require Import Ionia.finType Ionia.vector Ionia.DataExp Ionia.CNN_Defs
  Ionia.CNN_CodeGen_Core Ionia.Proof_CodeGen Ionia.DPIA_Rules
  Ionia.CNN_CodeGen_Semantics Ionia.CNN_Examples_Base
  Ionia.CNN_Examples_Base_Ops Ionia.CNN_OP Ionia.Operators_Sem_Equiv
  Ionia.Ops_Elementwise Ionia.Ops_BatchNorm Ionia.Ops_Transformer
  Ionia.Ops_Reduce Ionia.Attention_DPIA Ionia.MiniTransformer_DPIA
  Ionia.Bridge_ReduceConv Ionia.Bridge_ReduceConv2 Ionia.Bridge_Elementwise
  Ionia.Bridge_LeNet5.

Open Scope string_scope.
Set Implicit Arguments.
(* As in [Bridge_LeNet5]: local [Definition]s for buffer-name types defeat
   default subterm matching when instantiating the read/write lemmas, so the
   whole file uses keyed unification. *)
Set Keyed Unification.

(* NOTE: no module aliases in this file — references written through
   [Module X := ...] aliases poison monolithic [Extraction] in Rocq 9.1.1
   ("Extraction of file ... as a module is required"), so all library
   references use the plain library module paths. *)

(* String name-clash solvers (as in [Bridge_LeNet5]/[Bridge_MiniTransformer]). *)
Ltac str_neq_tac := intros u v Heq; discriminate.

(* -------------------------------------------------------------------------- *)
(* Scalar constants (exact real value for [eval], C literal for the printer) *)
(* -------------------------------------------------------------------------- *)

Definition mt_eps : DataExp.exp num := DataExp.REconst (1 / IZR 100000)%R "1e-5".
Definition mt_neginf : DataExp.exp num := DataExp.REconst (- IZR (10 ^ 30)%Z)%R "-1e30".
(* GELU coefficients; [mt_gelu_c] is the environment-read sqrt(2/pi) (see
   the header note): [REconst PI] is not extraction-safe. *)
Definition mt_gelu_c : DataExp.exp num := DataExp.REvar "gelu_c".
Definition mt_half : DataExp.exp num := CNN_Defs.div CNN_Defs.one (CNN_Defs.add CNN_Defs.one CNN_Defs.one).
Definition mt_cubic : DataExp.exp num :=
  CNN_Defs.div (DataExp.REconst (IZR 44715) "44715") (DataExp.REconst (IZR 1000000) "1000000").
(* Attention scale 1/sqrt(16), cf. [Attention_DPIA.attn_scale]. *)
Definition mt_attn_scale : DataExp.exp num :=
  CNN_Defs.div CNN_Defs.one (CNN_Defs.sqrt (DataExp.REconst (IZR 16) "16")).

(* -------------------------------------------------------------------------- *)
(* Constant homomorphism lemmas ([to_pcg_exp] of the constants)              *)
(* -------------------------------------------------------------------------- *)

Lemma to_pcg_exp_one : forall rho,
  CNN_CodeGen_Semantics.to_pcg_exp CNN_Defs.one rho = R1.
Proof. intro rho. cbv [CNN_CodeGen_Semantics.to_pcg_exp CNN_Defs.one DataExp.eval_rexp]. simpl. reflexivity. Qed.

Lemma to_pcg_exp_REconst : forall (r : R) (s : string) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (DataExp.REconst r s : DataExp.exp num) rho = r.
Proof. intros. cbv [CNN_CodeGen_Semantics.to_pcg_exp]. simpl. reflexivity. Qed.

Lemma to_pcg_exp_negate : forall (x : DataExp.exp num) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (CNN_Defs.negate x) rho = Ropp (CNN_CodeGen_Semantics.to_pcg_exp x rho).
Proof. intros. unfold CNN_Defs.negate. cbv [CNN_CodeGen_Semantics.to_pcg_exp]. simpl. reflexivity. Qed.

(* The eps value carried by [mt_eps]. *)
Definition mt_eps_v : R := (1 / IZR 100000)%R.

Lemma to_pcg_mt_eps : forall rho,
  CNN_CodeGen_Semantics.to_pcg_exp mt_eps rho = mt_eps_v.
Proof. intro rho. apply to_pcg_exp_REconst. Qed.

(* [INR (10^30)] and [IZR (10^30)] without ever unfolding the unary nat
   (the [Bridge_MiniTransformer] recipe). *)
Lemma zpow10_30 : Z.of_nat (10 ^ 30)%nat = (10 ^ 30)%Z.
Proof. rewrite Nat2Z.inj_pow. reflexivity. Qed.

Lemma mt_neginf_eq : forall rho,
  CNN_CodeGen_Semantics.to_pcg_exp mt_neginf rho = Ops_Transformer.NEGINF.
Proof.
  intro rho. unfold mt_neginf, Ops_Transformer.NEGINF, Proof_CodeGen.negate.
  (* NOTE: never [f_equal]/[simpl] a goal mentioning [INR (10^30)%nat]
     (unary-nat explosion); rewrite the value-level equalities first. *)
  rewrite to_pcg_exp_REconst. rewrite INR_IZR_INZ, zpow10_30. reflexivity.
Qed.

Lemma mt_attn_scale_eq : forall rho,
  CNN_CodeGen_Semantics.to_pcg_exp mt_attn_scale rho = Attention_DPIA.attn_scale 16.
Proof.
  intro rho. unfold mt_attn_scale, Attention_DPIA.attn_scale.
  rewrite Operators_Sem_Equiv.to_pcg_exp_div, to_pcg_exp_one, Bridge_ReduceConv2.to_pcg_exp_sqrt,
    to_pcg_exp_REconst.
  unfold Proof_CodeGen.div, Proof_CodeGen.one.
  replace (INR 16) with (IZR 16). reflexivity.
  rewrite INR_IZR_INZ. reflexivity.
Qed.

Lemma mt_half_eq : forall rho,
  CNN_CodeGen_Semantics.to_pcg_exp mt_half rho = Ops_Transformer.gelu_half.
Proof.
  intro rho. unfold mt_half, Ops_Transformer.gelu_half.
  rewrite Operators_Sem_Equiv.to_pcg_exp_div, CNN_CodeGen_Semantics.to_pcg_exp_add, !to_pcg_exp_one.
  reflexivity.
Qed.

Lemma mt_cubic_eq : forall rho,
  CNN_CodeGen_Semantics.to_pcg_exp mt_cubic rho = Ops_Transformer.gelu_cubic_coef.
Proof.
  intro rho. unfold mt_cubic, Ops_Transformer.gelu_cubic_coef.
  rewrite Operators_Sem_Equiv.to_pcg_exp_div, !to_pcg_exp_REconst.
  unfold Proof_CodeGen.div.
  replace (INR 44715) with (IZR 44715) by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR 1000000) with (IZR 1000000) by (rewrite INR_IZR_INZ; reflexivity).
  reflexivity.
Qed.

(* The [gelu_c] environment cell carries route A's [gelu_sqrt_2_pi]. *)
Definition gelu_c_ok (rho : Proof_CodeGen.env) : Prop :=
  rho (DataExp.Var "gelu_c") = Some Ops_Transformer.gelu_sqrt_2_pi.

Lemma mt_gelu_c_eq : forall rho,
  gelu_c_ok rho ->
  CNN_CodeGen_Semantics.to_pcg_exp mt_gelu_c rho = Ops_Transformer.gelu_sqrt_2_pi.
Proof.
  intros rho Hgc. unfold mt_gelu_c.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_REvar, Hgc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete instance types (b=1, s=8, h=2, d=16, dm=32, df=32, v=8)          *)
(* -------------------------------------------------------------------------- *)

Definition T1 := ary '{32} num.
Definition T2 := ary '{32} (ary '{32} num).
Definition T3 := ary '{1} (ary '{8} (ary '{32} num)).
Definition T4H := ary '{1} (ary '{2} (ary '{8} (ary '{16} num))).
Definition T4S := ary '{1} (ary '{2} (ary '{8} (ary '{8} num))).
Definition T2H := ary '{32} (ary '{8} num).
Definition T3O := ary '{1} (ary '{8} (ary '{8} num)).

Definition i0_1 : fin 1 := nat2fin (Nat.lt_0_succ 0).

(* Inputs and layer parameters (environment reads). *)
Definition tok_tab : DataExp.exp (ary '{8} (ary '{32} num)) := CNN_CodeGen_Core.vrd "tok_tab".
Definition pos_tab : DataExp.exp (ary '{8} (ary '{32} num)) := CNN_CodeGen_Core.vrd "pos_tab".

Definition l1_ln1_g : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l1_ln1_g".
Definition l1_ln1_b : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l1_ln1_b".
Definition l1_ln2_g : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l1_ln2_g".
Definition l1_ln2_b : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l1_ln2_b".
Definition l1_wq : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l1_wq".
Definition l1_wk : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l1_wk".
Definition l1_wv : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l1_wv".
Definition l1_wo : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l1_wo".
Definition l1_w1 : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l1_w1".
Definition l1_w2 : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l1_w2".

Definition l2_ln1_g : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l2_ln1_g".
Definition l2_ln1_b : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l2_ln1_b".
Definition l2_ln2_g : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l2_ln2_g".
Definition l2_ln2_b : DataExp.exp T1 := CNN_CodeGen_Core.vrd "l2_ln2_b".
Definition l2_wq : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l2_wq".
Definition l2_wk : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l2_wk".
Definition l2_wv : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l2_wv".
Definition l2_wo : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l2_wo".
Definition l2_w1 : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l2_w1".
Definition l2_w2 : DataExp.exp T2 := CNN_CodeGen_Core.vrd "l2_w2".

Definition lnf_g : DataExp.exp T1 := CNN_CodeGen_Core.vrd "lnf_g".
Definition lnf_b : DataExp.exp T1 := CNN_CodeGen_Core.vrd "lnf_b".
Definition whead : DataExp.exp T2H := CNN_CodeGen_Core.vrd "whead".

(* Buffers: write acceptor + read-back expression. *)
Definition l1_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "l1".
Definition l1_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "l1".
Definition l2_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "l2".
Definition l2_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "l2".
Definition l3_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "l3".
Definition l3_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "l3".
Definition l4_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "l4".
Definition l4_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "l4".

Definition bln1_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "bln1".
Definition bln1_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "bln1".
Definition bmha_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "bmha".
Definition bmha_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "bmha".
Definition br1_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "br1".
Definition br1_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "br1".
Definition bln2_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "bln2".
Definition bln2_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "bln2".
Definition btf1_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "btf1".
Definition btf1_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "btf1".
Definition btg_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "btg".
Definition btg_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "btg".
Definition btf2_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "btf2".
Definition btf2_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "btf2".

Definition mtq_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "mtq".
Definition mtq_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "mtq".
Definition mtk_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "mtk".
Definition mtk_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "mtk".
Definition mtv_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "mtv".
Definition mtv_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "mtv".
Definition mtmg_w : DataExp.acc T3 := CNN_CodeGen_Core.vwt "mtmg".
Definition mtmg_r : DataExp.exp T3 := CNN_CodeGen_Core.vrd "mtmg".

Definition mtqs_w : DataExp.acc T4H := CNN_CodeGen_Core.vwt "mtqs".
Definition mtqs_r : DataExp.exp T4H := CNN_CodeGen_Core.vrd "mtqs".
Definition mtks_w : DataExp.acc T4H := CNN_CodeGen_Core.vwt "mtks".
Definition mtks_r : DataExp.exp T4H := CNN_CodeGen_Core.vrd "mtks".
Definition mtvs_w : DataExp.acc T4H := CNN_CodeGen_Core.vwt "mtvs".
Definition mtvs_r : DataExp.exp T4H := CNN_CodeGen_Core.vrd "mtvs".
Definition mtatt_w : DataExp.acc T4H := CNN_CodeGen_Core.vwt "mtatt".
Definition mtatt_r : DataExp.exp T4H := CNN_CodeGen_Core.vrd "mtatt".

Definition mtprob_w : DataExp.acc T4S := CNN_CodeGen_Core.vwt "mtprob".
Definition mtprob_r : DataExp.exp T4S := CNN_CodeGen_Core.vrd "mtprob".

Definition output_w : DataExp.acc T3O := CNN_CodeGen_Core.vwt "output".

(* -------------------------------------------------------------------------- *)
(* Independence infrastructure                                                *)
(* -------------------------------------------------------------------------- *)

(* Independence weakens from an acceptor to any sub-acceptor. *)
Lemma indep_weaken_idx : forall (n : nat) (d d' : data) (e : DataExp.exp d')
  (out : DataExp.acc (ary '{n} d)) (i : fin n),
  CNN_CodeGen_Semantics.exp_independent_of_acc e out ->
  CNN_CodeGen_Semantics.exp_independent_of_acc e (DataExp.idxAcc out i).
Proof.
  intros n d d' e out i H p Hp.
  apply H. apply CNN_CodeGen_Semantics.in_acc_ary_inv in Hp. exact Hp.
Qed.

Lemma indep_REconst : forall (r : R) (s : string) (d : data) (a : DataExp.acc d),
  CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.REconst r s : DataExp.exp num) a.
Proof. intros. intros p Hp. exact I. Qed.

Lemma indep_negate : forall (x : DataExp.exp num) (d : data) (a : DataExp.acc d),
  CNN_CodeGen_Semantics.exp_independent_of_acc x a ->
  CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.negate x) a.
Proof. intros x d a H p Hp. apply H. exact Hp. Qed.

Lemma indep_pExp : forall (x : DataExp.exp num) (d : data) (a : DataExp.acc d),
  CNN_CodeGen_Semantics.exp_independent_of_acc x a ->
  CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.pExp x) a.
Proof. intros x d a H p Hp. apply H. exact Hp. Qed.

Lemma indep_div_n : forall (x : DataExp.exp num) (n : nat) (d : data) (a : DataExp.acc d),
  CNN_CodeGen_Semantics.exp_independent_of_acc x a ->
  CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.div_n x n) a.
Proof. intros x n d a H p Hp. apply H. exact Hp. Qed.

Lemma indep_sum : forall (n : nat) (e : DataExp.exp (ary '{n} num))
  (d : data) (a : DataExp.acc d),
  (forall i, CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.idx e i) a) ->
  CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.sum e) a.
Proof.
  intros n e d a H p Hp.
  apply CNN_CodeGen_Semantics.exp_independent_path_sum. intro i. apply (H i p Hp).
Qed.

Lemma indep_REif : forall (b : DataExp.bexp) (e1 e2 : DataExp.exp num)
  (d : data) (a : DataExp.acc d),
  (forall p, @Proof_CodeGen.in_acc d p a -> CNN_CodeGen_Semantics.bexp_independent_of_path b p) ->
  CNN_CodeGen_Semantics.exp_independent_of_acc e1 a ->
  CNN_CodeGen_Semantics.exp_independent_of_acc e2 a ->
  CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.REif b e1 e2 : DataExp.exp num) a.
Proof.
  intros b e1 e2 d a Hb H1 H2 p Hp. simpl. split; [ apply Hb; exact Hp | ].
  split; [ apply H1; exact Hp | apply H2; exact Hp ].
Qed.

Lemma indep_BLeb : forall (m n : nat) (p : DataExp.path),
  CNN_CodeGen_Semantics.bexp_independent_of_path (DataExp.BLeb m n) p.
Proof. intros. exact I. Qed.

(* The [gelu_c] scalar read is independent of any (differently named) buffer. *)
Lemma indep_gelu_c_vwt : forall (d : data) (s : string),
  (s <> "gelu_c")%string ->
  (forall u : string, (s ++ "[" ++ u <> "gelu_c")%string) ->
  CNN_CodeGen_Semantics.exp_independent_of_acc mt_gelu_c (@CNN_CodeGen_Core.vwt d s).
Proof.
  intros d s Hneq Hbr.
  destruct d as [| n f d']; intros p Hp; unfold mt_gelu_c; simpl; intro Heq.
  - rewrite CNN_CodeGen_Semantics.vwt_num in Hp. simpl in Hp. rewrite <- Hp in Heq.
    injection Heq as Heq. apply Hneq. symmetry. exact Heq.
  - destruct (Bridge_LeNet5.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Hu].
    rewrite Hu in Heq. injection Heq as Heq. apply (Hbr u). symmetry. exact Heq.
Qed.

(* Reading a buffer after writing a DIFFERENT buffer (bracketed names). *)
Lemma vrd_after_other_vwt_br : forall n (f : fle n) d (si t : string),
  (forall u v : string, (si ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  forall (v : Proof_CodeGen.exp (ary f d)) (rho : Proof_CodeGen.env),
    CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd (ary f d) t) (Proof_CodeGen.assign (@CNN_CodeGen_Core.vwt (ary f d) si) v rho) =
    CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd (ary f d) t) rho.
Proof.
  intros n f d si t Hdiv v rho.
  apply (@CNN_CodeGen_Semantics.exp_independent_of_acc_eval (ary f d) (ary f d)
           (@CNN_CodeGen_Core.vrd (ary f d) t) (@CNN_CodeGen_Core.vwt (ary f d) si)).
  - intros p Hp. destruct (Bridge_LeNet5.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq].
    subst p. apply Bridge_LeNet5.exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hdiv u w (eq_sym Hw)).
  - intros q Hq. apply Proof_CodeGen.assign_not_in_acc. exact Hq.
Qed.

(* Type-general version: reading a buffer after writing a DIFFERENT buffer
   whose array type may differ (e.g. a T2/T1 parameter read through a T3/T4H
   stage assign).  Without this, cross-type reads never normalise, so every
   stage value textually embeds the whole prefix assign chain and the goal
   grows exponentially (the 12 GB OOM). *)
Lemma vrd_after_other_vwt_br2 : forall (n1 n2 : nat) (f1 : fle n1) (f2 : fle n2)
  (d1 d2 : data) (si t : string),
  (forall u v : string, (si ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  forall (v : Proof_CodeGen.exp (ary f2 d2)) (rho : Proof_CodeGen.env),
    CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd (ary f1 d1) t)
      (Proof_CodeGen.assign (@CNN_CodeGen_Core.vwt (ary f2 d2) si) v rho) =
    CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd (ary f1 d1) t) rho.
Proof.
  intros n1 n2 f1 f2 d1 d2 si t Hdiv v rho.
  apply (@CNN_CodeGen_Semantics.exp_independent_of_acc_eval (ary f1 d1) (ary f2 d2)
           (@CNN_CodeGen_Core.vrd (ary f1 d1) t) (@CNN_CodeGen_Core.vwt (ary f2 d2) si)).
  - intros p Hp. destruct (Bridge_LeNet5.in_acc_vwt_bracket _ _ _ _ _ Hp) as [u Heq].
    subst p. apply Bridge_LeNet5.exp_indep_vrd_ary_Var. intros w Hw.
    exact (Hdiv u w (eq_sym Hw)).
  - intros q Hq. apply Proof_CodeGen.assign_not_in_acc. exact Hq.
Qed.

(* Buffer writes preserve the [gelu_c] environment cell. *)
Lemma gelu_c_not_in_vwt : forall (d : data) (s : string),
  (s <> "gelu_c")%string ->
  (forall u : string, (s ++ "[" ++ u <> "gelu_c")%string) ->
  ~ @Proof_CodeGen.in_acc d (DataExp.Var "gelu_c") (@CNN_CodeGen_Core.vwt d s).
Proof.
  intros d s Hneq Hbr Hin.
  destruct d as [| n f d'].
  - rewrite CNN_CodeGen_Semantics.vwt_num in Hin. simpl in Hin.
    apply Hneq. injection Hin as H. exact H.
  - destruct (Bridge_LeNet5.in_acc_vwt_bracket _ _ _ _ _ Hin) as [u Hu].
    apply (Hbr u). symmetry. injection Hu as H. exact H.
Qed.

Lemma assign_preserves_gelu_c : forall (d : data) (s : string)
  (v : Proof_CodeGen.exp d) (rho : Proof_CodeGen.env),
  (s <> "gelu_c")%string ->
  (forall u : string, (s ++ "[" ++ u <> "gelu_c")%string) ->
  Proof_CodeGen.assign (@CNN_CodeGen_Core.vwt d s) v rho (DataExp.Var "gelu_c") = rho (DataExp.Var "gelu_c").
Proof.
  intros. apply Proof_CodeGen.assign_not_in_acc. apply gelu_c_not_in_vwt; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic seqfor-nest collapse: a pointwise assignment loop nest equals the *)
(* whole-array assignment of the leaf expressions.  This is the engine of    *)
(* the faithful bridge: every stage collapses by [eval_mkvSeq] alone.        *)
(* -------------------------------------------------------------------------- *)

Definition nest2 (n m : nat) (out : DataExp.acc (ary '{n} (ary '{m} num)))
  (f : fin n -> fin m -> DataExp.exp num) : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seqfor (fun i => CNN_CodeGen_Core.seqfor (fun j =>
    CNN_CodeGen_Core.assign (DataExp.idxAcc (DataExp.idxAcc out i) j, f i j))).

Definition nest3 (n1 n2 n3 : nat)
  (out : DataExp.acc (ary '{n1} (ary '{n2} (ary '{n3} num))))
  (f : fin n1 -> fin n2 -> fin n3 -> DataExp.exp num) : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seqfor (fun i => CNN_CodeGen_Core.seqfor (fun j => CNN_CodeGen_Core.seqfor (fun k =>
    CNN_CodeGen_Core.assign (DataExp.idxAcc (DataExp.idxAcc (DataExp.idxAcc out i) j) k, f i j k)))).

Definition nest4 (n1 n2 n3 n4 : nat)
  (out : DataExp.acc (ary '{n1} (ary '{n2} (ary '{n3} (ary '{n4} num)))))
  (f : fin n1 -> fin n2 -> fin n3 -> fin n4 -> DataExp.exp num) : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seqfor (fun i => CNN_CodeGen_Core.seqfor (fun j => CNN_CodeGen_Core.seqfor (fun k => CNN_CodeGen_Core.seqfor (fun l =>
    CNN_CodeGen_Core.assign (DataExp.idxAcc (DataExp.idxAcc (DataExp.idxAcc (DataExp.idxAcc out i) j) k) l,
               f i j k l))))).

(* Function-level [eval_seqfor] (the library one is pointwise). *)
Lemma eval_seqfor_fun : forall (n : nat) (f : fin n -> CNN_CodeGen_Core.comm),
  CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.seqfor f) = Proof_CodeGen.seqfor (fun i => CNN_CodeGen_Semantics.eval (f i)).
Proof. reflexivity. Qed.

(* Pointwise assign congruence (deterministic replacement for [f_equal],
   whose deep decomposition at concrete types is unpredictable here). *)
Lemma assign_cong_at : forall (d : data) (a : DataExp.acc d)
  (e1 e2 : Proof_CodeGen.exp d) (rho : Proof_CodeGen.env),
  e1 = e2 -> Proof_CodeGen.assign a e1 rho = Proof_CodeGen.assign a e2 rho.
Proof. intros. subst. reflexivity. Qed.

(* Pointwise variant (the whole-network simulation closes at a path). *)
Lemma assign_cong_at_p : forall (d : data) (a : DataExp.acc d)
  (e1 e2 : Proof_CodeGen.exp d) (rho : Proof_CodeGen.env) (p : DataExp.path),
  e1 = e2 -> Proof_CodeGen.assign a e1 rho p = Proof_CodeGen.assign a e2 rho p.
Proof. intros. subst. reflexivity. Qed.

(* One-level collapse: a [seqfor] whose body already assigns the leaf values
   collapses to the whole-array assign (the workhorse; [eval_mkvSeq] fires
   backward here because the [seqfor] IS directly under an [eval]). *)
Lemma collapse_step : forall (n : nat) (d : data) (a : DataExp.acc (ary '{n} d))
  (f : fin n -> DataExp.exp d) (body : fin n -> CNN_CodeGen_Core.comm),
  (forall i, CNN_CodeGen_Semantics.eval (body i) = CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.assign (DataExp.idxAcc a i, f i))) ->
  (forall i, CNN_CodeGen_Semantics.exp_independent_of_acc (f i) a) ->
  CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.seqfor body) = CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.assign (a, DataExp.mkvSeq f)).
Proof.
  intros n d a f body H Hind.
  rewrite eval_seqfor_fun.
  rewrite (@CNN_CodeGen_Semantics.eval_mkvSeq n d f a Hind).
  rewrite eval_seqfor_fun.
  apply Proof_CodeGen.seqfor_extensionality. intro i. exact (H i).
Qed.

Lemma collapse2 : forall (n m : nat)
  (out : DataExp.acc (ary '{n} (ary '{m} num)))
  (f : fin n -> fin m -> DataExp.exp num),
  (forall i j, CNN_CodeGen_Semantics.exp_independent_of_acc (f i j) out) ->
  CNN_CodeGen_Semantics.eval (nest2 out f) =
  CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.assign (out, DataExp.mkvSeq (fun i => DataExp.mkvSeq (fun j => f i j)))).
Proof.
  intros n m out f Hindep. unfold nest2. apply collapse_step.
  - intros i. apply collapse_step.
    + intros j. reflexivity.
    + intros j. apply indep_weaken_idx. apply Hindep.
  - intros i. apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro j. apply Hindep.
Qed.

Lemma collapse3 : forall (n1 n2 n3 : nat)
  (out : DataExp.acc (ary '{n1} (ary '{n2} (ary '{n3} num))))
  (f : fin n1 -> fin n2 -> fin n3 -> DataExp.exp num),
  (forall i j k, CNN_CodeGen_Semantics.exp_independent_of_acc (f i j k) out) ->
  CNN_CodeGen_Semantics.eval (nest3 out f) =
  CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.assign (out, DataExp.mkvSeq (fun i => DataExp.mkvSeq (fun j =>
    DataExp.mkvSeq (fun k => f i j k))))).
Proof.
  intros n1 n2 n3 out f Hindep. unfold nest3. apply collapse_step.
  - intros i. apply collapse_step.
    + intros j. apply collapse_step.
      * intros k. reflexivity.
      * intros k. do 2 apply indep_weaken_idx. apply Hindep.
    + intros j. apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro k.
      apply indep_weaken_idx. apply Hindep.
  - intros i. apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro j.
    apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro k. apply Hindep.
Qed.

Lemma collapse4 : forall (n1 n2 n3 n4 : nat)
  (out : DataExp.acc (ary '{n1} (ary '{n2} (ary '{n3} (ary '{n4} num)))))
  (f : fin n1 -> fin n2 -> fin n3 -> fin n4 -> DataExp.exp num),
  (forall i j k l, CNN_CodeGen_Semantics.exp_independent_of_acc (f i j k l) out) ->
  CNN_CodeGen_Semantics.eval (nest4 out f) =
  CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.assign (out, DataExp.mkvSeq (fun i => DataExp.mkvSeq (fun j =>
    DataExp.mkvSeq (fun k => DataExp.mkvSeq (fun l => f i j k l)))))).
Proof.
  intros n1 n2 n3 n4 out f Hindep. unfold nest4. apply collapse_step.
  - intros i. apply collapse_step.
    + intros j. apply collapse_step.
      * intros k. apply collapse_step.
        -- intros l. reflexivity.
        -- intros l. do 3 apply indep_weaken_idx. apply Hindep.
      * intros k. apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro l.
        do 2 apply indep_weaken_idx. apply Hindep.
    + intros j. apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro k.
      apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro l.
      apply indep_weaken_idx. apply Hindep.
  - intros i. apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro j.
    apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro k.
    apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq. intro l. apply Hindep.
Qed.

(* [CNN_Defs.sum] of an arbitrary syntactic vector reads as [Proof_CodeGen.sum] of its
   interpretation (the [Bridge_MiniTransformer.to_pcg_sum_gen] recipe). *)
Lemma pcg_sum_idx_eta : forall (n : nat) (X : Proof_CodeGen.exp (ary '{n} num)),
  Proof_CodeGen.sum (Proof_CodeGen.mkvSeq (fun i => Proof_CodeGen.idx X i)) = Proof_CodeGen.sum X.
Proof.
  intros n X. unfold Proof_CodeGen.sum, Proof_CodeGen.mkvSeq, Proof_CodeGen.idx, vector.v_idx.
  rewrite (vector.mk_vec_bij_fin n (Proof_CodeGen.exp_default num) X). reflexivity.
Qed.

Lemma to_pcg_sum_gen : forall (n : nat) (x : DataExp.exp (ary '{n} num)) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (CNN_Defs.sum x) rho = Proof_CodeGen.sum (CNN_CodeGen_Semantics.to_pcg_exp x rho).
Proof.
  intros n x rho.
  assert (Heta : x = DataExp.mkvSeq (fun i : fin n => DataExp.idx x i)).
  { unfold DataExp.mkvSeq, DataExp.idx, vector.v_idx. symmetry.
    apply (vector.mk_vec_bij_fin n (DataExp.exp_default num) x). }
  rewrite Heta at 1.
  rewrite Bridge_ReduceConv.to_pcg_sum_mkvSeq.
  assert (Hpoint : Proof_CodeGen.mkvSeq (fun i => CNN_CodeGen_Semantics.to_pcg_exp (DataExp.idx x i) rho) =
                   Proof_CodeGen.mkvSeq (fun i => Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp x rho) i)).
  { apply vector.mk_vec_ext. intro i. apply CNN_CodeGen_Semantics.to_pcg_exp_idx. }
  rewrite Hpoint. apply pcg_sum_idx_eta.
Qed.

(* eval of [CNN_CodeGen_Core.seq] is plain composition. *)
Lemma eval_seq_at : forall (c1 c2 : CNN_CodeGen_Core.comm) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.eval (CNN_CodeGen_Core.seq (c1, c2)) rho = CNN_CodeGen_Semantics.eval c2 (CNN_CodeGen_Semantics.eval c1 rho).
Proof. reflexivity. Qed.


(* -------------------------------------------------------------------------- *)
(* Leaf-level [to_pcg_exp] normalisation tactic                               *)
(* -------------------------------------------------------------------------- *)

Ltac pcg_norm :=
  repeat first
    [ rewrite CNN_CodeGen_Semantics.to_pcg_exp_add | rewrite Operators_Sem_Equiv.to_pcg_exp_mul
    | rewrite Operators_Sem_Equiv.to_pcg_exp_div | rewrite Bridge_ReduceConv2.to_pcg_exp_sub
    | rewrite Bridge_ReduceConv2.to_pcg_exp_sqrt | rewrite Operators_Sem_Equiv.to_pcg_exp_pExp
    | rewrite Operators_Sem_Equiv.to_pcg_exp_div_n | rewrite to_pcg_exp_negate
    | rewrite to_pcg_sum_gen | rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq
    | rewrite CNN_CodeGen_Semantics.to_pcg_exp_idx | rewrite CNN_CodeGen_Semantics.to_pcg_exp_REif ].

(* -------------------------------------------------------------------------- *)
(* Stage: residual add (b,s,dm)  [Ops_Elementwise.Add3d]                                   *)
(* -------------------------------------------------------------------------- *)

Definition add3d_leaf (X Y : DataExp.exp T3) (bb : fin 1) (ss : fin 8) (j : fin 32)
  : DataExp.exp num :=
  CNN_Defs.add (DataExp.idx (DataExp.idx (DataExp.idx X bb) ss) j) (DataExp.idx (DataExp.idx (DataExp.idx Y bb) ss) j).

Definition ast_add3d (X Y : DataExp.exp T3) (out : DataExp.acc T3) : CNN_CodeGen_Core.comm :=
  nest3 out (add3d_leaf X Y).

Lemma ast_add3d_sem : forall (X Y : DataExp.exp T3) (out : DataExp.acc T3) (rho : Proof_CodeGen.env),
  (forall bb ss j, CNN_CodeGen_Semantics.exp_independent_of_acc (add3d_leaf X Y bb ss j) out) ->
  CNN_CodeGen_Semantics.eval (ast_add3d X Y out) rho =
  Proof_CodeGen.assign out (Ops_Elementwise.Add3d (CNN_CodeGen_Semantics.to_pcg_exp X rho) (CNN_CodeGen_Semantics.to_pcg_exp Y rho)) rho.
Proof.
  intros X Y out rho Hindep. unfold ast_add3d.
  rewrite collapse3 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign. f_equal.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: GELU (b,s,dm)  [MiniTransformer_DPIA.GELU3d]                        *)
(* -------------------------------------------------------------------------- *)

Definition ast_tanh (x : DataExp.exp num) : DataExp.exp num :=
  CNN_Defs.div (CNN_Defs.sub (CNN_Defs.pExp x) (CNN_Defs.pExp (CNN_Defs.negate x)))
         (CNN_Defs.add (CNN_Defs.pExp x) (CNN_Defs.pExp (CNN_Defs.negate x))).

Definition ast_gelu (x : DataExp.exp num) : DataExp.exp num :=
  CNN_Defs.mul (CNN_Defs.mul mt_half x)
    (CNN_Defs.add CNN_Defs.one (ast_tanh (CNN_Defs.mul mt_gelu_c
      (CNN_Defs.add x (CNN_Defs.mul mt_cubic (CNN_Defs.mul (CNN_Defs.mul x x) x)))))).

Definition gelu3d_leaf (X : DataExp.exp T3) (bb : fin 1) (ss : fin 8) (j : fin 32)
  : DataExp.exp num := ast_gelu (DataExp.idx (DataExp.idx (DataExp.idx X bb) ss) j).

Definition ast_gelu3d (X : DataExp.exp T3) (out : DataExp.acc T3) : CNN_CodeGen_Core.comm :=
  nest3 out (gelu3d_leaf X).

Lemma gelu_leaf_hom : forall (x : DataExp.exp num) (rho : Proof_CodeGen.env),
  gelu_c_ok rho ->
  CNN_CodeGen_Semantics.to_pcg_exp (ast_gelu x) rho = Ops_Transformer.gelu (CNN_CodeGen_Semantics.to_pcg_exp x rho).
Proof.
  intros x rho Hgc. unfold ast_gelu, ast_tanh, Ops_Transformer.gelu, Ops_Transformer.gelu_tanh. cbn beta.
  pcg_norm.
  rewrite mt_gelu_c_eq by exact Hgc.
  rewrite !to_pcg_exp_one, !to_pcg_exp_REconst.
  unfold Ops_Transformer.gelu_half, Ops_Transformer.gelu_cubic_coef, Proof_CodeGen.div, Proof_CodeGen.one, Proof_CodeGen.mul, Proof_CodeGen.add.
  replace (INR 44715) with (IZR 44715) by (rewrite INR_IZR_INZ; reflexivity).
  replace (INR 1000000) with (IZR 1000000) by (rewrite INR_IZR_INZ; reflexivity).
  reflexivity.
Qed.

Lemma ast_gelu3d_sem : forall (X : DataExp.exp T3) (out : DataExp.acc T3) (rho : Proof_CodeGen.env),
  gelu_c_ok rho ->
  (forall bb ss j, CNN_CodeGen_Semantics.exp_independent_of_acc (gelu3d_leaf X bb ss j) out) ->
  CNN_CodeGen_Semantics.eval (ast_gelu3d X out) rho =
  Proof_CodeGen.assign out (MiniTransformer_DPIA.GELU3d (CNN_CodeGen_Semantics.to_pcg_exp X rho)) rho.
Proof.
  intros X out rho Hgc Hindep. unfold ast_gelu3d.
  rewrite collapse3 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. unfold MiniTransformer_DPIA.GELU3d.
  apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro ss.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro j.
  unfold gelu3d_leaf. rewrite gelu_leaf_hom by exact Hgc.
  do 3 rewrite CNN_CodeGen_Semantics.to_pcg_exp_idx. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: LayerNorm (b,s,dm)  [Ops_Transformer.LayerNorm3d]; mean/variance recomputed per  *)
(* element exactly as in route A (no accumulator caches).                     *)
(* -------------------------------------------------------------------------- *)

Definition ln_mean (row : DataExp.exp (ary '{32} num)) : DataExp.exp num :=
  CNN_Defs.div_n (CNN_Defs.sum row) 32.

Definition ln_varsum (row : DataExp.exp (ary '{32} num)) (mean : DataExp.exp num)
  : DataExp.exp (ary '{32} num) :=
  DataExp.mkvSeq (fun i : fin 32 =>
    CNN_Defs.mul (CNN_Defs.sub (DataExp.idx row i) mean) (CNN_Defs.sub (DataExp.idx row i) mean)).

Definition ln_var (row : DataExp.exp (ary '{32} num)) (mean : DataExp.exp num) : DataExp.exp num :=
  CNN_Defs.div_n (CNN_Defs.sum (ln_varsum row mean)) 32.

Definition ln_leaf (X : DataExp.exp T3) (G B : DataExp.exp T1) (E : DataExp.exp num)
  (bb : fin 1) (ss : fin 8) (j : fin 32) : DataExp.exp num :=
  let row := DataExp.idx (DataExp.idx X bb) ss in
  CNN_Defs.add (CNN_Defs.mul (CNN_Defs.div (CNN_Defs.sub (DataExp.idx row j) (ln_mean row))
                         (CNN_Defs.sqrt (CNN_Defs.add (ln_var row (ln_mean row)) E)))
                 (DataExp.idx G j))
         (DataExp.idx B j).

Definition ast_ln (X : DataExp.exp T3) (G B : DataExp.exp T1) (E : DataExp.exp num) (out : DataExp.acc T3)
  : CNN_CodeGen_Core.comm := nest3 out (ln_leaf X G B E).

(* LN leaf homomorphisms, decomposed so that every [rewrite] runs at top
   level (rewriting under a binder with keyed unification diverges). *)
Lemma ln_mean_hom : forall (row : DataExp.exp (ary '{32} num)) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (ln_mean row) rho = Ops_Transformer.LNmean (CNN_CodeGen_Semantics.to_pcg_exp row rho).
Proof.
  intros row rho. unfold ln_mean, Ops_Transformer.LNmean, Proof_CodeGen.div.
  rewrite Operators_Sem_Equiv.to_pcg_exp_div_n, to_pcg_sum_gen. reflexivity.
Qed.

Lemma ln_varsum_hom : forall (row : DataExp.exp (ary '{32} num)) (mean : DataExp.exp num)
  (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (ln_varsum row mean) rho =
  Ops_Transformer.LNvarSum (CNN_CodeGen_Semantics.to_pcg_exp row rho) (CNN_CodeGen_Semantics.to_pcg_exp mean rho).
Proof.
  intros row mean rho. unfold ln_varsum, Ops_Transformer.LNvarSum.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext. intro i.
  pcg_norm. reflexivity.
Qed.

Lemma ln_var_hom : forall (row : DataExp.exp (ary '{32} num)) (mean : DataExp.exp num)
  (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (ln_var row mean) rho =
  Ops_Transformer.LNvar (CNN_CodeGen_Semantics.to_pcg_exp row rho) (CNN_CodeGen_Semantics.to_pcg_exp mean rho).
Proof.
  intros row mean rho. unfold ln_var, Ops_Transformer.LNvar, Proof_CodeGen.div.
  rewrite Operators_Sem_Equiv.to_pcg_exp_div_n, to_pcg_sum_gen, ln_varsum_hom. reflexivity.
Qed.

Lemma ln_leaf_hom : forall (X : DataExp.exp T3) (G B : DataExp.exp T1) (E : DataExp.exp num)
  (bb : fin 1) (ss : fin 8) (j : fin 32) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (ln_leaf X G B E bb ss j) rho =
  Ops_BatchNorm.BNcell (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp X rho) bb) ss) j)
    (Ops_Transformer.LNmean (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp X rho) bb) ss))
    (Ops_Transformer.LNvar (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp X rho) bb) ss)
              (Ops_Transformer.LNmean (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp X rho) bb) ss)))
    (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp G rho) j) (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp B rho) j)
    (CNN_CodeGen_Semantics.to_pcg_exp E rho).
Proof.
  intros X G B E bb ss j rho.
  unfold ln_leaf. cbv beta zeta.
  unfold Ops_BatchNorm.BNcell.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_add, Operators_Sem_Equiv.to_pcg_exp_mul, Operators_Sem_Equiv.to_pcg_exp_div,
    Bridge_ReduceConv2.to_pcg_exp_sub, Bridge_ReduceConv2.to_pcg_exp_sqrt, CNN_CodeGen_Semantics.to_pcg_exp_add.
  rewrite ln_var_hom, !ln_mean_hom.
  rewrite !CNN_CodeGen_Semantics.to_pcg_exp_idx. reflexivity.
Qed.

Lemma ast_ln_sem : forall (X : DataExp.exp T3) (G B : DataExp.exp T1) (E : DataExp.exp num) (out : DataExp.acc T3)
  (rho : Proof_CodeGen.env),
  (forall bb ss j, CNN_CodeGen_Semantics.exp_independent_of_acc (ln_leaf X G B E bb ss j) out) ->
  CNN_CodeGen_Semantics.eval (ast_ln X G B E out) rho =
  Proof_CodeGen.assign out (Ops_Transformer.LayerNorm3d (CNN_CodeGen_Semantics.to_pcg_exp X rho) (CNN_CodeGen_Semantics.to_pcg_exp G rho)
                                 (CNN_CodeGen_Semantics.to_pcg_exp B rho) (CNN_CodeGen_Semantics.to_pcg_exp E rho)) rho.
Proof.
  intros X G B E out rho Hindep. unfold ast_ln.
  rewrite collapse3 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  unfold Ops_Transformer.LayerNorm3d.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro ss.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro j.
  rewrite ln_leaf_hom. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: batched right-multiplication (1,8,n) @ (n,p)  [Attention_DPIA.BMatMul2d]        *)
(* -------------------------------------------------------------------------- *)

Definition bmm_leaf {n p : nat}
  (X : DataExp.exp (ary '{1} (ary '{8} (ary '{n} num))))
  (W : DataExp.exp (ary '{n} (ary '{p} num)))
  (bb : fin 1) (ss : fin 8) (j : fin p) : DataExp.exp num :=
  CNN_Defs.sum (DataExp.mkvSeq (fun k : fin n =>
    CNN_Defs.mul (DataExp.idx (DataExp.idx (DataExp.idx X bb) ss) k) (DataExp.idx (DataExp.idx W k) j))).

Definition ast_bmm {n p : nat}
  (X : DataExp.exp (ary '{1} (ary '{8} (ary '{n} num))))
  (W : DataExp.exp (ary '{n} (ary '{p} num)))
  (out : DataExp.acc (ary '{1} (ary '{8} (ary '{p} num)))) : CNN_CodeGen_Core.comm :=
  nest3 out (bmm_leaf X W).

Lemma bmm_leaf_hom : forall (n p : nat)
  (X : DataExp.exp (ary '{1} (ary '{8} (ary '{n} num))))
  (W : DataExp.exp (ary '{n} (ary '{p} num)))
  (bb : fin 1) (ss : fin 8) (j : fin p) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (bmm_leaf X W bb ss j) rho =
  Proof_CodeGen.sum (Proof_CodeGen.mkvSeq (fun k : fin n =>
    Proof_CodeGen.mul (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp X rho) bb) ss) k)
            (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp W rho) k) j))).
Proof.
  intros n p X W bb ss j rho. unfold bmm_leaf.
  rewrite to_pcg_sum_gen, CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq.
  f_equal. apply vector.mk_vec_ext. intro k. pcg_norm. reflexivity.
Qed.

Lemma ast_bmm_sem : forall (n p : nat)
  (X : DataExp.exp (ary '{1} (ary '{8} (ary '{n} num))))
  (W : DataExp.exp (ary '{n} (ary '{p} num)))
  (out : DataExp.acc (ary '{1} (ary '{8} (ary '{p} num)))) (rho : Proof_CodeGen.env),
  (forall bb ss j, CNN_CodeGen_Semantics.exp_independent_of_acc (bmm_leaf X W bb ss j) out) ->
  CNN_CodeGen_Semantics.eval (ast_bmm X W out) rho =
  Proof_CodeGen.assign out (Attention_DPIA.BMatMul2d (CNN_CodeGen_Semantics.to_pcg_exp X rho) (CNN_CodeGen_Semantics.to_pcg_exp W rho)) rho.
Proof.
  intros n p X W out rho Hindep. unfold ast_bmm.
  rewrite collapse3 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  unfold Attention_DPIA.BMatMul2d, Ops_Transformer.MatMul2d.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro ss.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro j.
  rewrite bmm_leaf_hom. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: head split (1,8,32) -> (1,2,8,16)  [Ops_Transformer.SplitHeads]                  *)
(* -------------------------------------------------------------------------- *)

Definition split_leaf (X : DataExp.exp T3)
  (bb : fin 1) (hh : fin 2) (ss : fin 8) (dd : fin 16) : DataExp.exp num :=
  DataExp.idx (DataExp.idx (DataExp.idx X bb) ss) (vector.idx_2d_to_1d hh dd).

Definition ast_split (X : DataExp.exp T3) (out : DataExp.acc T4H) : CNN_CodeGen_Core.comm :=
  nest4 out (split_leaf X).

Lemma ast_split_sem : forall (X : DataExp.exp T3) (out : DataExp.acc T4H) (rho : Proof_CodeGen.env),
  (forall bb hh ss dd, CNN_CodeGen_Semantics.exp_independent_of_acc (split_leaf X bb hh ss dd) out) ->
  CNN_CodeGen_Semantics.eval (ast_split X out) rho =
  Proof_CodeGen.assign out (@Ops_Transformer.SplitHeads 1 8 2 16 (CNN_CodeGen_Semantics.to_pcg_exp X rho)) rho.
Proof.
  intros X out rho Hindep. unfold ast_split.
  rewrite collapse4 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  unfold Ops_Transformer.SplitHeads.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro hh.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro ss.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro dd.
  unfold split_leaf. pcg_norm. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: head merge (1,2,8,16) -> (1,8,32)  [Ops_Transformer.MergeHeads]                  *)
(* -------------------------------------------------------------------------- *)

Definition merge_leaf (X : DataExp.exp T4H)
  (bb : fin 1) (ss : fin 8) (xx : fin 32) : DataExp.exp num :=
  DataExp.idx (DataExp.idx (DataExp.idx (DataExp.idx X bb)
    (fst (@vector.idx_1d_to_2d 2 16 xx))) ss) (snd (@vector.idx_1d_to_2d 2 16 xx)).

Definition ast_merge (X : DataExp.exp T4H) (out : DataExp.acc T3) : CNN_CodeGen_Core.comm :=
  nest3 out (merge_leaf X).

Lemma ast_merge_sem : forall (X : DataExp.exp T4H) (out : DataExp.acc T3) (rho : Proof_CodeGen.env),
  (forall bb ss xx, CNN_CodeGen_Semantics.exp_independent_of_acc (merge_leaf X bb ss xx) out) ->
  CNN_CodeGen_Semantics.eval (ast_merge X out) rho =
  Proof_CodeGen.assign out (Ops_Transformer.MergeHeads (CNN_CodeGen_Semantics.to_pcg_exp X rho)) rho.
Proof.
  intros X out rho Hindep. unfold ast_merge.
  rewrite collapse3 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  unfold Ops_Transformer.MergeHeads.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro ss.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro xx.
  unfold merge_leaf. pcg_norm. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: fused attention scores -> probabilities (per head).                 *)
(*   leaf = Softmax2d (CausalMask2d (Mulc2d (attn_scale 16)                   *)
(*            (MatMul2d q (Transpose2d k)))) at (i, j)                        *)
(* The masked-score sub-expression is an [REif] leaf (the printer emits a C   *)
(* ternary), so no score/mask buffers are staged — this is exactly route A's  *)
(* composed [Attention_cell] score sub-expression.                            *)
(* -------------------------------------------------------------------------- *)

Definition attn_score_exp (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i k : fin 8) : DataExp.exp num :=
  CNN_Defs.sum (DataExp.mkvSeq (fun kk : fin 16 =>
    CNN_Defs.mul (DataExp.idx (DataExp.idx (DataExp.idx (DataExp.idx Q bb) hh) i) kk)
           (DataExp.idx (DataExp.idx (DataExp.idx (DataExp.idx K bb) hh) k) kk))).

Definition attn_masked (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i k : fin 8) : DataExp.exp num :=
  DataExp.REif (DataExp.BLeb (fin2nat k) (fin2nat i))
    (CNN_Defs.mul (attn_score_exp Q K bb hh i k) mt_attn_scale)
    mt_neginf.

Definition attnprob_leaf (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i j : fin 8) : DataExp.exp num :=
  CNN_Defs.div (CNN_Defs.pExp (attn_masked Q K bb hh i j))
         (CNN_Defs.sum (DataExp.mkvSeq (fun l : fin 8 =>
           CNN_Defs.pExp (attn_masked Q K bb hh i l)))).

Definition ast_attnprob (Q K : DataExp.exp T4H) (out : DataExp.acc T4S) : CNN_CodeGen_Core.comm :=
  nest4 out (attnprob_leaf Q K).

(* The value form used for the buffer-content tracking. *)
Definition attnprob_value (Qv Kv : Proof_CodeGen.exp T4H) : Proof_CodeGen.exp T4S :=
  Proof_CodeGen.mkvSeq (fun bb => Proof_CodeGen.mkvSeq (fun hh =>
    Ops_Reduce.Softmax2d (Ops_Transformer.CausalMask2d (Ops_Elementwise.Mulc2d (Attention_DPIA.attn_scale 16)
      (Ops_Transformer.MatMul2d (Proof_CodeGen.idx (Proof_CodeGen.idx Qv bb) hh)
                  (Ops_Transformer.Transpose2d (Proof_CodeGen.idx (Proof_CodeGen.idx Kv bb) hh))))))).

Lemma attn_score_hom : forall (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i k : fin 8) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (attn_score_exp Q K bb hh i k) rho =
  Proof_CodeGen.sum (Proof_CodeGen.mkvSeq (fun kk : fin 16 =>
    Proof_CodeGen.mul (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp Q rho) bb) hh) i) kk)
            (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp K rho) bb) hh) k) kk))).
Proof.
  intros Q K bb hh i k rho. unfold attn_score_exp.
  rewrite to_pcg_sum_gen, CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq.
  f_equal. apply vector.mk_vec_ext. intro kk. pcg_norm. reflexivity.
Qed.

(* The if-form of the masked score (route A's [CausalMask2d] leaf, computed
   through the composed score expression). *)
Lemma attn_masked_hom : forall (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i k : fin 8) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (attn_masked Q K bb hh i k) rho =
  (if (fin2nat k <=? fin2nat i)%nat then
     Proof_CodeGen.mul (Proof_CodeGen.sum (Proof_CodeGen.mkvSeq (fun kk : fin 16 =>
       Proof_CodeGen.mul (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp Q rho) bb) hh) i) kk)
               (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (CNN_CodeGen_Semantics.to_pcg_exp K rho) bb) hh) k) kk))))
     (Attention_DPIA.attn_scale 16)
   else Ops_Transformer.NEGINF).
Proof.
  intros Q K bb hh i k rho. unfold attn_masked.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_REif.
  change (DataExp.eval_bexp (fun s : string =>
             match rho (DataExp.Var s) with Some r => r | None => R0 end)
           (DataExp.BLeb (fin2nat k) (fin2nat i)))
    with (fin2nat k <=? fin2nat i)%nat.
  rewrite Operators_Sem_Equiv.to_pcg_exp_mul, mt_attn_scale_eq, mt_neginf_eq, attn_score_hom.
  reflexivity.
Qed.

(* The folded inner value of the attention softmax stage. *)
Definition attn_INN (Qv Kv : Proof_CodeGen.exp T4H) (bb : fin 1) (hh : fin 2)
  : Proof_CodeGen.exp (ary '{8} (ary '{8} num)) :=
  Ops_Transformer.CausalMask2d (Ops_Elementwise.Mulc2d (Attention_DPIA.attn_scale 16)
    (Ops_Transformer.MatMul2d (Proof_CodeGen.idx (Proof_CodeGen.idx Qv bb) hh)
                (Ops_Transformer.Transpose2d (Proof_CodeGen.idx (Proof_CodeGen.idx Kv bb) hh)))).

Lemma attn_INN_idx : forall (Qv Kv : Proof_CodeGen.exp T4H)
  (bb : fin 1) (hh : fin 2) (i k : fin 8),
  Proof_CodeGen.idx (Proof_CodeGen.idx (attn_INN Qv Kv bb hh) i) k =
  (if (fin2nat k <=? fin2nat i)%nat then
     Proof_CodeGen.mul (Proof_CodeGen.sum (Proof_CodeGen.mkvSeq (fun kk : fin 16 =>
       Proof_CodeGen.mul (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx Qv bb) hh) i) kk)
               (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx (Proof_CodeGen.idx Kv bb) hh) k) kk))))
     (Attention_DPIA.attn_scale 16)
   else Ops_Transformer.NEGINF).
Proof.
  intros Qv Kv bb hh i k. unfold attn_INN.
  unfold Ops_Transformer.CausalMask2d, Ops_Elementwise.Mulc2d.
  do 4 (rewrite Proof_CodeGen.idx_mkvSeq by lia; cbn beta).
  destruct (fin2nat k <=? fin2nat i)%nat; [| reflexivity].
  f_equal.
  unfold Ops_Transformer.MatMul2d, Ops_Transformer.Transpose2d.
  do 2 (rewrite Proof_CodeGen.idx_mkvSeq by lia; cbn beta).
  f_equal.
  apply vector.mk_vec_ext. intro kk.
  do 2 (rewrite Proof_CodeGen.idx_mkvSeq by lia; cbn beta). reflexivity.
Qed.

Lemma attn_masked_INN : forall (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i k : fin 8) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (attn_masked Q K bb hh i k) rho =
  Proof_CodeGen.idx (Proof_CodeGen.idx (attn_INN (CNN_CodeGen_Semantics.to_pcg_exp Q rho) (CNN_CodeGen_Semantics.to_pcg_exp K rho) bb hh) i) k.
Proof.
  intros Q K bb hh i k rho. rewrite attn_masked_hom. symmetry.
  apply attn_INN_idx.
Qed.

Lemma attnprob_leaf_hom : forall (Q K : DataExp.exp T4H)
  (bb : fin 1) (hh : fin 2) (i j : fin 8) (rho : Proof_CodeGen.env),
  CNN_CodeGen_Semantics.to_pcg_exp (attnprob_leaf Q K bb hh i j) rho =
  Proof_CodeGen.div (Proof_CodeGen.pExp
    (Proof_CodeGen.idx (Proof_CodeGen.idx (attn_INN (CNN_CodeGen_Semantics.to_pcg_exp Q rho) (CNN_CodeGen_Semantics.to_pcg_exp K rho) bb hh) i) j))
    (Proof_CodeGen.sum (Proof_CodeGen.mkvSeq (fun l : fin 8 =>
      Proof_CodeGen.pExp (Proof_CodeGen.idx (Proof_CodeGen.idx
        (attn_INN (CNN_CodeGen_Semantics.to_pcg_exp Q rho) (CNN_CodeGen_Semantics.to_pcg_exp K rho) bb hh) i) l)))).
Proof.
  intros Q K bb hh i j rho. unfold attnprob_leaf.
  rewrite Operators_Sem_Equiv.to_pcg_exp_div, Operators_Sem_Equiv.to_pcg_exp_pExp, attn_masked_INN.
  rewrite to_pcg_sum_gen, CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq.
  unfold Proof_CodeGen.div, Proof_CodeGen.pExp.
  f_equal.
  f_equal. apply vector.mk_vec_ext. intro l.
  rewrite Operators_Sem_Equiv.to_pcg_exp_pExp, attn_masked_INN. reflexivity.
Qed.

Lemma ast_attnprob_sem : forall (Q K : DataExp.exp T4H) (out : DataExp.acc T4S) (rho : Proof_CodeGen.env),
  (forall bb hh i j, CNN_CodeGen_Semantics.exp_independent_of_acc (attnprob_leaf Q K bb hh i j) out) ->
  CNN_CodeGen_Semantics.eval (ast_attnprob Q K out) rho =
  Proof_CodeGen.assign out (attnprob_value (CNN_CodeGen_Semantics.to_pcg_exp Q rho) (CNN_CodeGen_Semantics.to_pcg_exp K rho)) rho.
Proof.
  intros Q K out rho Hindep. unfold ast_attnprob.
  rewrite collapse4 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  unfold attnprob_value, Ops_Reduce.Softmax2d.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro hh.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro i.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro j.
  rewrite attnprob_leaf_hom. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)

Definition attnproj_leaf (P : DataExp.exp T4S) (Vv : DataExp.exp T4H) (bb : fin 1) (hh : fin 2)
  (i : fin 8) (j : fin 16) : DataExp.exp num :=
  CNN_Defs.sum (DataExp.mkvSeq (fun l : fin 8 =>
    CNN_Defs.mul (DataExp.idx (DataExp.idx (DataExp.idx (DataExp.idx P bb) hh) i) l)
           (DataExp.idx (DataExp.idx (DataExp.idx (DataExp.idx Vv bb) hh) l) j))).

Definition ast_attnproj (P : DataExp.exp T4S) (Vv : DataExp.exp T4H) (out : DataExp.acc T4H)
  : CNN_CodeGen_Core.comm := nest4 out (attnproj_leaf P Vv).

Definition attnproj_value (Pv : Proof_CodeGen.exp T4S) (Vv : Proof_CodeGen.exp T4H) : Proof_CodeGen.exp T4H :=
  Proof_CodeGen.mkvSeq (fun bb => Proof_CodeGen.mkvSeq (fun hh =>
    Ops_Transformer.MatMul2d (Proof_CodeGen.idx (Proof_CodeGen.idx Pv bb) hh) (Proof_CodeGen.idx (Proof_CodeGen.idx Vv bb) hh))).

Lemma ast_attnproj_sem : forall (P : DataExp.exp T4S) (Vv : DataExp.exp T4H)
  (out : DataExp.acc T4H) (rho : Proof_CodeGen.env),
  (forall bb hh i j, CNN_CodeGen_Semantics.exp_independent_of_acc (attnproj_leaf P Vv bb hh i j) out) ->
  CNN_CodeGen_Semantics.eval (ast_attnproj P Vv out) rho =
  Proof_CodeGen.assign out (attnproj_value (CNN_CodeGen_Semantics.to_pcg_exp P rho) (CNN_CodeGen_Semantics.to_pcg_exp Vv rho)) rho.
Proof.
  intros P Vv out rho Hindep. unfold ast_attnproj.
  rewrite collapse4 by exact Hindep. rewrite CNN_CodeGen_Semantics.eval_assign.
  apply assign_cong_at.
  unfold attnproj_value, Ops_Transformer.MatMul2d.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro hh.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro i.
  rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro j.
  unfold attnproj_leaf. pcg_norm. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Stage: embedding (Gather2d + position add), unrolled over the 8 positions  *)
(* with baked token indices [mt_toks] = 3,1,4,1,5,2,6,0 — the one place where *)
(* a host-level index map cannot be printed, cf. the header note.             *)
(* -------------------------------------------------------------------------- *)

Definition F0_8 : fin 8 := @nat2fin 8 0 (ltac:(lia)).
Definition F1_8 : fin 8 := @nat2fin 8 1 (ltac:(lia)).
Definition F2_8 : fin 8 := @nat2fin 8 2 (ltac:(lia)).
Definition F3_8 : fin 8 := @nat2fin 8 3 (ltac:(lia)).
Definition F4_8 : fin 8 := @nat2fin 8 4 (ltac:(lia)).
Definition F5_8 : fin 8 := @nat2fin 8 5 (ltac:(lia)).
Definition F6_8 : fin 8 := @nat2fin 8 6 (ltac:(lia)).
Definition F7_8 : fin 8 := @nat2fin 8 7 (ltac:(lia)).

(* The token sequence as a host-level index map (route A's [toks]). *)
Definition mt_toks (i : fin 8) : fin 8 :=
  match fin2nat i with
  | 0 => F3_8 | 1 => F1_8 | 2 => F4_8 | 3 => F1_8
  | 4 => F5_8 | 5 => F2_8 | 6 => F6_8 | _ => F0_8
  end.

Definition embed_leaf (p tk : fin 8) (j : fin 32) : DataExp.exp num :=
  CNN_Defs.add (DataExp.idx (DataExp.idx tok_tab tk) j) (DataExp.idx (DataExp.idx pos_tab p) j).

Definition ast_embed_pos (p tk : fin 8) : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seqfor (fun j : fin 32 =>
    CNN_CodeGen_Core.assign (DataExp.idxAcc (DataExp.idxAcc (DataExp.idxAcc l1_w i0_1) p) j, embed_leaf p tk j)).

Definition ast_embed : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seq (ast_embed_pos F0_8 F3_8, CNN_CodeGen_Core.seq (ast_embed_pos F1_8 F1_8,
  CNN_CodeGen_Core.seq (ast_embed_pos F2_8 F4_8, CNN_CodeGen_Core.seq (ast_embed_pos F3_8 F1_8,
  CNN_CodeGen_Core.seq (ast_embed_pos F4_8 F5_8, CNN_CodeGen_Core.seq (ast_embed_pos F5_8 F2_8,
  CNN_CodeGen_Core.seq (ast_embed_pos F6_8 F6_8, ast_embed_pos F7_8 F0_8))))))).

(* The value written by the embedding stage: route A's [mt_x0] ingredients. *)
Definition embed_value (rho : Proof_CodeGen.env) : Proof_CodeGen.exp T3 :=
  Ops_Elementwise.Add3d (Proof_CodeGen.mkvSeq (fun bb : fin 1 =>
             Ops_Transformer.Gather2d mt_toks (CNN_CodeGen_Semantics.to_pcg_exp tok_tab rho)))
           (Proof_CodeGen.mkvSeq (fun bb : fin 1 => CNN_CodeGen_Semantics.to_pcg_exp pos_tab rho)).

(* One embedding position row. *)
Lemma embed_pos_sem : forall (p tk : fin 8) (rho : Proof_CodeGen.env),
  (forall j, CNN_CodeGen_Semantics.exp_independent_of_acc (embed_leaf p tk j)
    (DataExp.idxAcc (DataExp.idxAcc l1_w i0_1) p)) ->
  CNN_CodeGen_Semantics.eval (ast_embed_pos p tk) rho =
  Proof_CodeGen.assign (DataExp.idxAcc (DataExp.idxAcc l1_w i0_1) p)
    (Proof_CodeGen.mkvSeq (fun j : fin 32 => CNN_CodeGen_Semantics.to_pcg_exp (embed_leaf p tk j) rho)) rho.
Proof.
  intros p tk rho Hindep. unfold ast_embed_pos.
  rewrite <- CNN_CodeGen_Semantics.eval_mkvSeq.
  2: { intros j. exact (Hindep j). }
  rewrite CNN_CodeGen_Semantics.eval_assign. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Network assembly                                                           *)
(* -------------------------------------------------------------------------- *)

Definition embed_leaf_full (bb : fin 1) (ss : fin 8) (j : fin 32) : DataExp.exp num :=
  CNN_Defs.add (DataExp.idx (DataExp.idx tok_tab (mt_toks ss)) j) (DataExp.idx (DataExp.idx pos_tab ss) j).

Lemma indep_REif_BLeb : forall (m n : nat) (e1 e2 : DataExp.exp num)
  (d : data) (a : DataExp.acc d),
  CNN_CodeGen_Semantics.exp_independent_of_acc e1 a -> CNN_CodeGen_Semantics.exp_independent_of_acc e2 a ->
  CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.REif (DataExp.BLeb m n) e1 e2 : DataExp.exp num) a.
Proof. intros. apply indep_REif; auto. intros. apply indep_BLeb. Qed.

(* Side-condition solver for the stage lemmas' independence premises.  Uses
   [cbv] lists (safe for absent constants — unlike [unfold], whose no-op
   poisons the next rewrite under keyed unification in Rocq 9.1). *)
Ltac mt_indep_tac :=
  cbv [add3d_leaf gelu3d_leaf ln_leaf ln_mean ln_var ln_varsum
       bmm_leaf split_leaf merge_leaf attnprob_leaf attn_masked attn_score_exp
       attnproj_leaf
       embed_leaf embed_leaf_full ast_gelu ast_tanh
       mt_eps mt_neginf mt_attn_scale mt_cubic mt_half
       CNN_Defs.one CNN_Defs.zero
       l1_w l1_r l2_w l2_r l3_w l3_r l4_w l4_r bln1_w bln1_r bmha_w bmha_r
       br1_w br1_r bln2_w bln2_r btf1_w btf1_r btg_w btg_r btf2_w btf2_r
       mtq_w mtq_r mtk_w mtk_r mtv_w mtv_r mtmg_w mtmg_r
       mtqs_w mtqs_r mtks_w mtks_r mtvs_w mtvs_r mtatt_w mtatt_r
       mtprob_w mtprob_r output_w tok_tab pos_tab
       l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2
       l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2
       lnf_g lnf_b whead];
  repeat match goal with
    | |- forall x : fin _, _ => intro
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc _ _ => progress (cbn beta)
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.mkvSeq _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_mkvSeq
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.add _ _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_add
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.mul _ _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_mul
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.sub _ _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_sub
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.div _ _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_div
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.sqrt _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_sqrt
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.pExp _) _ => apply indep_pExp
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.div_n _ _) _ => apply indep_div_n
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.negate _) _ => apply indep_negate
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.REconst _ _) _ => apply indep_REconst
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_Defs.sum _) _ => apply indep_sum
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.REif _ _ _) _ => apply indep_REif_BLeb
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (DataExp.idx _ _) _ =>
        apply CNN_CodeGen_Semantics.exp_independent_of_acc_idx
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc (CNN_CodeGen_Core.vrd _) (CNN_CodeGen_Core.vwt _) =>
        apply Bridge_LeNet5.vrd_ary_indep_vwt_ary; [str_neq_tac]
    | |- CNN_CodeGen_Semantics.exp_independent_of_acc mt_gelu_c (CNN_CodeGen_Core.vwt _) =>
        apply indep_gelu_c_vwt; [discriminate | intros; discriminate]
    end.

(* Read-back normalisation ([mt_readback]) is defined after [block_env]
   below, since its cbv list must include [block_env]. *)

(* [gelu_c] premise discharge through the assign chain. *)
Ltac mt_gelu_c_tac Hgc :=
  unfold gelu_c_ok;
  repeat (rewrite assign_preserves_gelu_c by (first [discriminate | intros; discriminate]));
  exact Hgc.

(* -------------------------------------------------------------------------- *)
(* Embedding stage (unrolled) collapses to the whole-buffer assign            *)
(* -------------------------------------------------------------------------- *)


Lemma seqfor1 : forall (p : fin 1 -> Proof_CodeGen.comm) (rho : Proof_CodeGen.env),
  Proof_CodeGen.seqfor p rho = p i0_1 rho.
Proof.
  intros p rho.
  change (Proof_CodeGen.seqfor p rho) with
    (Proof_CodeGen.seq (Proof_CodeGen.seqfor (fun i : fin 0 => p (fin2finS i))) (p (ltS 0)) rho).
  replace (ltS 0) with i0_1.
  - reflexivity.
  - apply (proj1 (fin_eq _ _)). reflexivity.
Qed.

Lemma seqfor8_peel : forall (p : fin 8 -> Proof_CodeGen.comm) (rho : Proof_CodeGen.env),
  Proof_CodeGen.seqfor p rho =
  p F7_8 (p F6_8 (p F5_8 (p F4_8 (p F3_8 (p F2_8 (p F1_8 (p F0_8 rho))))))).
Proof.
  intros p rho. repeat rewrite CNN_CodeGen_Semantics.seqfor_S.
  replace (ltS 7) with F7_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (ltS 6)) with F6_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (fin2finS (ltS 5))) with F5_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (fin2finS (fin2finS (ltS 4)))) with F4_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (fin2finS (fin2finS (fin2finS (ltS 3))))) with F3_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (fin2finS (fin2finS (fin2finS (fin2finS (ltS 2)))))) with F2_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (fin2finS (fin2finS (fin2finS (fin2finS (fin2finS (ltS 1))))))) with F1_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  replace (fin2finS (fin2finS (fin2finS (fin2finS (fin2finS (fin2finS (fin2finS (ltS 0)))))))) with F0_8 by (apply (proj1 (fin_eq _ _)); reflexivity).
  reflexivity.
Qed.

(* One embedding row, read against an abstract environment [rho_abs]. *)
Lemma embed_pos_sem_abs : forall (p tk : fin 8) (rho rho_abs : Proof_CodeGen.env),
  (forall q, ~ Proof_CodeGen.in_acc q l1_w -> rho q = rho_abs q) ->
  (forall j, CNN_CodeGen_Semantics.exp_independent_of_acc (embed_leaf p tk j) l1_w) ->
  CNN_CodeGen_Semantics.eval (ast_embed_pos p tk) rho =
  Proof_CodeGen.assign (DataExp.idxAcc (DataExp.idxAcc l1_w i0_1) p)
    (Proof_CodeGen.mkvSeq (fun j : fin 32 => CNN_CodeGen_Semantics.to_pcg_exp (embed_leaf p tk j) rho_abs)) rho.
Proof.
  intros p tk rho rho_abs Hagree Hindep.
  rewrite (embed_pos_sem (p := p) (tk := tk) rho).
  2: { intros j. do 2 apply indep_weaken_idx. apply Hindep. }
  apply assign_cong_at. apply vector.mk_vec_ext. intro j.
  apply (CNN_CodeGen_Semantics.exp_independent_of_acc_eval (a := l1_w)); [apply Hindep | exact Hagree].
Qed.

(* A write to an [l1] subcell preserves everything outside [l1]. *)
Lemma assign_subcell_preserve : forall (p : fin 8) (v : Proof_CodeGen.exp (ary '{32} num))
  (rho : Proof_CodeGen.env) (q : DataExp.path),
  ~ Proof_CodeGen.in_acc q l1_w ->
  Proof_CodeGen.assign (DataExp.idxAcc (DataExp.idxAcc l1_w i0_1) p) v rho q = rho q.
Proof.
  intros p v rho q Hq. apply Proof_CodeGen.assign_not_in_acc. intro Hc. apply Hq.
  apply CNN_CodeGen_Semantics.in_acc_ary_inv in Hc. apply CNN_CodeGen_Semantics.in_acc_ary_inv in Hc. exact Hc.
Qed.

Ltac l1_agree_tac :=
  intros q Hq; repeat (rewrite assign_subcell_preserve by exact Hq); reflexivity.

(* The unrolled embedding equals the abstract nest3 form (token-index
   conversion is by computation at each concrete position). *)
Lemma embed_unroll : forall rho,
  CNN_CodeGen_Semantics.eval ast_embed rho = CNN_CodeGen_Semantics.eval (nest3 l1_w embed_leaf_full) rho.
Proof.
  intro rho. unfold nest3.
  (* process the RHS first while [ast_embed] is a folded constant, so the
     [eval_seqfor_fun]/peel rewrites have a unique occurrence *)
  rewrite eval_seqfor_fun. cbn beta.
  rewrite seqfor1. cbn beta.
  rewrite eval_seqfor_fun. cbn beta.
  rewrite seqfor8_peel.
  unfold ast_embed, ast_embed_pos.
  repeat rewrite eval_seq_at.
  unfold embed_leaf, embed_leaf_full. reflexivity.
Qed.

Lemma ast_embed_sem : forall rho,
  CNN_CodeGen_Semantics.eval ast_embed rho = Proof_CodeGen.assign l1_w (embed_value rho) rho.
Proof.
  intro rho.
  rewrite embed_unroll.
  rewrite collapse3 by mt_indep_tac. rewrite CNN_CodeGen_Semantics.eval_assign.
    apply assign_cong_at. unfold embed_value, Ops_Elementwise.Add3d.
    rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro bb.
    rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro ss.
    rewrite CNN_CodeGen_Semantics.to_pcg_exp_mkvSeq. apply vector.mk_vec_ext; intro j.
    repeat (rewrite Proof_CodeGen.idx_mkvSeq by lia; cbn beta).
    unfold Ops_Transformer.Gather2d. repeat (rewrite Proof_CodeGen.idx_mkvSeq by lia; cbn beta).
    unfold embed_leaf_full. pcg_norm. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Block value and its fold to route A's [TransformerBlock]                   *)
(* -------------------------------------------------------------------------- *)

Definition block_value
  (Xv : Proof_CodeGen.exp T3)
  (ln1gv ln1bv ln2gv ln2bv : Proof_CodeGen.exp T1)
  (wqv wkv wvv wov w1v w2v : Proof_CodeGen.exp T2)
  (epsv : Proof_CodeGen.exp num) : Proof_CodeGen.exp T3 :=
  let ln1v := Ops_Transformer.LayerNorm3d Xv ln1gv ln1bv epsv in
  let mqv := Attention_DPIA.BMatMul2d ln1v wqv in
  let mkv := Attention_DPIA.BMatMul2d ln1v wkv in
  let mvv := Attention_DPIA.BMatMul2d ln1v wvv in
  let attv := attnproj_value
                (attnprob_value (@Ops_Transformer.SplitHeads 1 8 2 16 mqv)
                                (@Ops_Transformer.SplitHeads 1 8 2 16 mkv))
                (@Ops_Transformer.SplitHeads 1 8 2 16 mvv) in
  let br1 := Ops_Elementwise.Add3d Xv (Attention_DPIA.BMatMul2d (Ops_Transformer.MergeHeads attv) wov) in
  let ln2v := Ops_Transformer.LayerNorm3d br1 ln2gv ln2bv epsv in
  Ops_Elementwise.Add3d br1 (Attention_DPIA.BMatMul2d (MiniTransformer_DPIA.GELU3d (Attention_DPIA.BMatMul2d ln2v w1v)) w2v).

(* The attention sub-value IS route A's [AttnHeads] of the split inputs. *)
Lemma attn_value_fold : forall (Qv Kv Vv : Proof_CodeGen.exp T4H),
  attnproj_value (attnprob_value Qv Kv) Vv = Attention_DPIA.AttnHeads Qv Kv Vv.
Proof.
  intros Qv Kv Vv.
  unfold attnproj_value, attnprob_value, Attention_DPIA.AttnHeads, Attention_DPIA.Attention_cell.
  apply vector.mk_vec_ext; intro bb. apply vector.mk_vec_ext; intro hh.
  f_equal.
  unfold attn_INN.
  do 2 (rewrite Proof_CodeGen.idx_mkvSeq by lia). reflexivity.
Qed.

Lemma block_value_fold : forall Xv ln1gv ln1bv ln2gv ln2bv
  wqv wkv wvv wov w1v w2v epsv,
  block_value Xv ln1gv ln1bv ln2gv ln2bv wqv wkv wvv wov w1v w2v epsv =
  @MiniTransformer_DPIA.TransformerBlock 1 8 2 16 32 Xv ln1gv ln1bv ln2gv ln2bv wqv wkv wvv wov w1v w2v epsv.
Proof.
  intros. unfold block_value, MiniTransformer_DPIA.TransformerBlock, MiniTransformer_DPIA.FFN, Attention_DPIA.MHABlock.
  cbv zeta. rewrite attn_value_fold. reflexivity.
Qed.

(* The FULL environment effect of [ast_block]: a whole-env equality must
   account for all 17 buffer writes, not just the final [out] — the chain
   below is literally what the 17 stage lemmas produce.  The [out] cell
   carries the folded [block_value] so that downstream reads return exactly
   the route-A block value; the 16 intermediate writes carry the inline
   stage values. *)
Definition block_env
  (out : DataExp.acc T3)
  (Xv : Proof_CodeGen.exp T3)
  (ln1gv ln1bv ln2gv ln2bv : Proof_CodeGen.exp T1)
  (wqv wkv wvv wov w1v w2v : Proof_CodeGen.exp T2)
  (epsv : Proof_CodeGen.exp num) (rho : Proof_CodeGen.env) : Proof_CodeGen.env :=
  let ln1v := Ops_Transformer.LayerNorm3d Xv ln1gv ln1bv epsv in
  let mqv := Attention_DPIA.BMatMul2d ln1v wqv in
  let mkv := Attention_DPIA.BMatMul2d ln1v wkv in
  let mvv := Attention_DPIA.BMatMul2d ln1v wvv in
  let qsv := @Ops_Transformer.SplitHeads 1 8 2 16 mqv in
  let ksv := @Ops_Transformer.SplitHeads 1 8 2 16 mkv in
  let vsv := @Ops_Transformer.SplitHeads 1 8 2 16 mvv in
  let probv := attnprob_value qsv ksv in
  let attv := attnproj_value probv vsv in
  let mgv := Ops_Transformer.MergeHeads attv in
  let mhav := Attention_DPIA.BMatMul2d mgv wov in
  let br1v := Ops_Elementwise.Add3d Xv mhav in
  let ln2v := Ops_Transformer.LayerNorm3d br1v ln2gv ln2bv epsv in
  let tf1v := Attention_DPIA.BMatMul2d ln2v w1v in
  let tgv := MiniTransformer_DPIA.GELU3d tf1v in
  let tf2v := Attention_DPIA.BMatMul2d tgv w2v in
  Proof_CodeGen.assign out
    (block_value Xv ln1gv ln1bv ln2gv ln2bv wqv wkv wvv wov w1v w2v epsv)
  (Proof_CodeGen.assign btf2_w tf2v
  (Proof_CodeGen.assign btg_w tgv
  (Proof_CodeGen.assign btf1_w tf1v
  (Proof_CodeGen.assign bln2_w ln2v
  (Proof_CodeGen.assign br1_w br1v
  (Proof_CodeGen.assign bmha_w mhav
  (Proof_CodeGen.assign mtmg_w mgv
  (Proof_CodeGen.assign mtatt_w attv
  (Proof_CodeGen.assign mtprob_w probv
  (Proof_CodeGen.assign mtvs_w vsv
  (Proof_CodeGen.assign mtv_w mvv
  (Proof_CodeGen.assign mtks_w ksv
  (Proof_CodeGen.assign mtk_w mkv
  (Proof_CodeGen.assign mtqs_w qsv
  (Proof_CodeGen.assign mtq_w mqv
  (Proof_CodeGen.assign bln1_w ln1v rho)))))))))))))))).

(* Block-level read interface (technique C2: the block exposes only these
   two read equations; proofs never unfold [block_env] in a large goal).
   [read_block_env_out]: reading the block's output buffer returns the
   folded [block_value].  [read_block_env_other]: reads of any other array
   pass straight through the 17-write chain. *)
Lemma read_block_env_out : forall (s : string)
  (Xv : Proof_CodeGen.exp T3)
  (ln1gv ln1bv ln2gv ln2bv : Proof_CodeGen.exp T1)
  (wqv wkv wvv wov w1v w2v : Proof_CodeGen.exp T2)
  (epsv : Proof_CodeGen.exp num) (rho : Proof_CodeGen.env),
  (s <> "0")%string -> (s <> "1")%string ->
  CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd T3 s)
    (block_env (@CNN_CodeGen_Core.vwt T3 s) Xv ln1gv ln1bv ln2gv ln2bv
               wqv wkv wvv wov w1v w2v epsv rho) =
  block_value Xv ln1gv ln1bv ln2gv ln2bv wqv wkv wvv wov w1v w2v epsv.
Proof.
  intros s Xv ln1gv ln1bv ln2gv ln2bv wqv wkv wvv wov w1v w2v epsv rho Hs0 Hs1.
  cbv [block_env]. apply CNN_CodeGen_Semantics.vrd_after_own_vwt; assumption.
Qed.

Lemma read_block_env_other : forall (s t : string) (n : nat) (f : fle n) (d : data)
  (Xv : Proof_CodeGen.exp T3)
  (ln1gv ln1bv ln2gv ln2bv : Proof_CodeGen.exp T1)
  (wqv wkv wvv wov w1v w2v : Proof_CodeGen.exp T2)
  (epsv : Proof_CodeGen.exp num) (rho : Proof_CodeGen.env),
  (forall u v : string, (s ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("bln1" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtq" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtqs" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtk" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtks" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtv" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtvs" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtprob" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtatt" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("mtmg" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("bmha" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("br1" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("bln2" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("btf1" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("btg" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  (forall u v : string, ("btf2" ++ "[" ++ u <> t ++ "[" ++ v)%string) ->
  CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd (ary f d) t)
    (block_env (@CNN_CodeGen_Core.vwt T3 s) Xv ln1gv ln1bv ln2gv ln2bv
               wqv wkv wvv wov w1v w2v epsv rho) =
  CNN_CodeGen_Semantics.to_pcg_exp (@CNN_CodeGen_Core.vrd (ary f d) t) rho.
Proof.
  intros s t n f d Xv ln1gv ln1bv ln2gv ln2bv wqv wkv wvv wov w1v w2v epsv rho.
  intros Hs H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
  cbv [block_env].
  repeat (rewrite vrd_after_other_vwt_br2 by
    (first [exact Hs | exact H1 | exact H2 | exact H3 | exact H4 | exact H5
           | exact H6 | exact H7 | exact H8 | exact H9 | exact H10 | exact H11
           | exact H12 | exact H13 | exact H14 | exact H15 | exact H16])).
  reflexivity.
Qed.

(* [block_env] is OPAQUE: the block lemmas close against the folded constant
   (kernel conversion handles the single final unfold), and the read lemmas
   above fail fast (key mismatch) on plain assign-chain environments —
   without opacity, each such failed attempt unfolds [block_value] under
   evars and backtracks through the whole 17-write chain. *)
Opaque block_env.

(* Read-back normalisation: buffer reads after the whole-env assign chain.
   Chain-only version used inside the block simulations: the [block_env] RHS
   stays folded, so goals stay small. *)
Ltac mt_readback :=
  cbv [l1_w l1_r l2_w l2_r l3_w l3_r l4_w l4_r bln1_w bln1_r bmha_w bmha_r
       br1_w br1_r bln2_w bln2_r btf1_w btf1_r btg_w btg_r btf2_w btf2_r
       mtq_w mtq_r mtk_w mtk_r mtv_w mtv_r mtmg_w mtmg_r
       mtqs_w mtqs_r mtks_w mtks_r mtvs_w mtvs_r mtatt_w mtatt_r
       mtprob_w mtprob_r output_w tok_tab pos_tab
       l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2
       l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2
       lnf_g lnf_b whead];
  repeat first
    [ rewrite CNN_CodeGen_Semantics.vrd_after_own_vwt by discriminate
    | rewrite vrd_after_other_vwt_br2 by str_neq_tac
    | rewrite to_pcg_mt_eps ].

(* Whole-network version: additionally reads through folded [block_env]
   environments via the block-level read interface. *)
Ltac mt_readback_net :=
  cbv [l1_w l1_r l2_w l2_r l3_w l3_r l4_w l4_r bln1_w bln1_r bmha_w bmha_r
       br1_w br1_r bln2_w bln2_r btf1_w btf1_r btg_w btg_r btf2_w btf2_r
       mtq_w mtq_r mtk_w mtk_r mtv_w mtv_r mtmg_w mtmg_r
       mtqs_w mtqs_r mtks_w mtks_r mtvs_w mtvs_r mtatt_w mtatt_r
       mtprob_w mtprob_r output_w tok_tab pos_tab
       l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2
       l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2
       lnf_g lnf_b whead];
  repeat first
    [ rewrite CNN_CodeGen_Semantics.vrd_after_own_vwt by discriminate
    | rewrite read_block_env_out by discriminate
    | rewrite read_block_env_other by str_neq_tac
    | rewrite vrd_after_other_vwt_br2 by str_neq_tac
    | rewrite to_pcg_mt_eps ].

(* -------------------------------------------------------------------------- *)
(* The whole-network faithful AST command                                     *)
(* -------------------------------------------------------------------------- *)

Definition ast_block
  (X : DataExp.exp T3) (LN1G LN1B LN2G LN2B : DataExp.exp T1)
  (WQ WK WV WO W1 W2 : DataExp.exp T2) (E : DataExp.exp num) (out : DataExp.acc T3)
  : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seq (ast_ln X LN1G LN1B E bln1_w,
       CNN_CodeGen_Core.seq (ast_bmm bln1_r WQ mtq_w,
       CNN_CodeGen_Core.seq (ast_split mtq_r mtqs_w,
       CNN_CodeGen_Core.seq (ast_bmm bln1_r WK mtk_w,
       CNN_CodeGen_Core.seq (ast_split mtk_r mtks_w,
       CNN_CodeGen_Core.seq (ast_bmm bln1_r WV mtv_w,
       CNN_CodeGen_Core.seq (ast_split mtv_r mtvs_w,
       CNN_CodeGen_Core.seq (ast_attnprob mtqs_r mtks_r mtprob_w,
       CNN_CodeGen_Core.seq (ast_attnproj mtprob_r mtvs_r mtatt_w,
       CNN_CodeGen_Core.seq (ast_merge mtatt_r mtmg_w,
       CNN_CodeGen_Core.seq (ast_bmm mtmg_r WO bmha_w,
       CNN_CodeGen_Core.seq (ast_add3d X bmha_r br1_w,
       CNN_CodeGen_Core.seq (ast_ln br1_r LN2G LN2B E bln2_w,
       CNN_CodeGen_Core.seq (ast_bmm bln2_r W1 btf1_w,
       CNN_CodeGen_Core.seq (ast_gelu3d btf1_r btg_w,
       CNN_CodeGen_Core.seq (ast_bmm btg_r W2 btf2_w,
       ast_add3d br1_r btf2_r out)))))))))))))))).

(* -------------------------------------------------------------------------- *)
(* Per-block simulation lemmas.                                               *)
(*                                                                            *)
(* These MUST be separate lemmas (one per concrete block instance): the two  *)
(* blocks share the MHA buffer names, so inside the whole-network proof the  *)
(* stage calls of block 1 and block 2 (e.g. [ast_attnprob mtqs_r mtks_r      *)
(* mtprob_w]) are textually IDENTICAL and differ only in the environment     *)
(* argument.  A blanket [rewrite ast_attnprob_sem] there picks whichever     *)
(* occurrence the subterm traversal finds first — rewriting the block-2      *)
(* occurrence first leaves [CNN_CodeGen_Semantics.eval (ast_stage ...) ] forms (not            *)
(* [Proof_CodeGen.assign]) inside the read environments of later stages, which neither *)
(* [mt_readback] lemma matches; the stage values then duplicate the whole    *)
(* remaining chain textually and the goal explodes (OOM at the 12 GB cap).   *)
(* With one [ast_block] per lemma, every stage occurrence is unique.         *)
(* -------------------------------------------------------------------------- *)

Lemma ast_block1_sim : forall (rho : Proof_CodeGen.env),
  gelu_c_ok rho ->
  CNN_CodeGen_Semantics.eval (ast_block l1_r l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                      l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 mt_eps l2_w) rho =
  block_env l2_w (CNN_CodeGen_Semantics.to_pcg_exp l1_r rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wk rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wo rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_w2 rho)
    mt_eps_v rho.
Proof.
  intros rho Hgc. unfold ast_block.
  (* The seq chain is peeled ONE stage at a time ([eval_seq_at] exposes the
     next stage applied to the current assign chain, so at every step exactly
     ONE visible [CNN_CodeGen_Semantics.eval] node matches each stage lemma and the blind
     [rewrite] hits it; its environment is always a fully-formed assign
     chain, so [mt_readback] normalises the fresh reads immediately.  Two
     pitfalls shaped this: (i) a blanket [repeat rewrite eval_seq_at] builds
     the 17-node eval nest, where blind rewrites hit the OUTERMOST matching
     stage first and leave reads stuck at unevaluated [CNN_CodeGen_Semantics.eval] chains;
     (ii) explicitly instantiated rewrites (e.g. [(X:=l1_r)]) hang in this
     setting — keyed unification backtracks through the unfolded stage/leaf
     bodies per candidate (Rocq 9.1.1). *)
  rewrite eval_seq_at. rewrite ast_ln_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_split_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_split_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_split_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_attnprob_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_attnproj_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_merge_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_add3d_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_ln_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_gelu3d_sem by (first [mt_gelu_c_tac Hgc | mt_indep_tac]). mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite ast_add3d_sem by mt_indep_tac. mt_readback.
  (* the 17-assign chain IS [block_env] (kernel conversion unfolds the
     folded constant once; the terms are small) *)
  reflexivity.
Qed.

Lemma ast_block2_sim : forall (rho : Proof_CodeGen.env),
  gelu_c_ok rho ->
  CNN_CodeGen_Semantics.eval (ast_block l2_r l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                      l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 mt_eps l3_w) rho =
  block_env l3_w (CNN_CodeGen_Semantics.to_pcg_exp l2_r rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wk rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wo rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_w2 rho)
    mt_eps_v rho.
Proof.
  intros rho Hgc. unfold ast_block.
  (* Same one-stage-at-a-time peeling as [ast_block1_sim]. *)
  rewrite eval_seq_at. rewrite ast_ln_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_split_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_split_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_split_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_attnprob_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_attnproj_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_merge_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_add3d_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_ln_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite eval_seq_at. rewrite ast_gelu3d_sem by (first [mt_gelu_c_tac Hgc | mt_indep_tac]). mt_readback.
  rewrite eval_seq_at. rewrite ast_bmm_sem by mt_indep_tac. mt_readback.
  rewrite ast_add3d_sem by mt_indep_tac. mt_readback.
  reflexivity.
Qed.

Definition minitransformer_faithful_comm : CNN_CodeGen_Core.comm :=
  CNN_CodeGen_Core.seq (ast_embed,
  CNN_CodeGen_Core.seq (ast_block l1_r l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                    l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 mt_eps l2_w,
  CNN_CodeGen_Core.seq (ast_block l2_r l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                    l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 mt_eps l3_w,
  CNN_CodeGen_Core.seq (ast_ln l3_r lnf_g lnf_b mt_eps l4_w,
         ast_bmm l4_r whead output_w)))).

(* -------------------------------------------------------------------------- *)
(* End-to-end simulation: the faithful AST computes [MiniTransformer]         *)
(* -------------------------------------------------------------------------- *)

Lemma faithful_sim : forall (rho : Proof_CodeGen.env),
  gelu_c_ok rho ->
  forall (p : DataExp.path), Proof_CodeGen.in_acc p output_w ->
  CNN_CodeGen_Semantics.eval minitransformer_faithful_comm rho p =
  Proof_CodeGen.assign output_w
    (@MiniTransformer_DPIA.MiniTransformer 1 8 2 16 32 8 mt_eps_v mt_toks
       (CNN_CodeGen_Semantics.to_pcg_exp tok_tab rho) (CNN_CodeGen_Semantics.to_pcg_exp pos_tab rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_b rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_b rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l1_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wk rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l1_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wo rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l1_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_w2 rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_b rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_b rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l2_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wk rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l2_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wo rho)
       (CNN_CodeGen_Semantics.to_pcg_exp l2_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_w2 rho)
       (CNN_CodeGen_Semantics.to_pcg_exp lnf_g rho) (CNN_CodeGen_Semantics.to_pcg_exp lnf_b rho)
       (CNN_CodeGen_Semantics.to_pcg_exp whead rho))
    rho p.
Proof.
  intros rho Hgc p Hin.
  unfold minitransformer_faithful_comm.
  (* Peel the embedding stage FIRST with an explicitly instantiated
     [eval_seq_at]: a blanket [repeat rewrite eval_seq_at] matches through the
     folded [ast_embed] constant (rewrite's subterm search unfolds it) and
     dissolves it into its 8 [ast_embed_pos] pieces, after which
     [ast_embed_sem] can no longer fire. *)
  rewrite (eval_seq_at ast_embed).
  rewrite ast_embed_sem. mt_readback_net.
  (* Blocks are handled by the per-block simulation lemmas (see the note
     there): inside this whole-network goal the two blocks' stage calls are
     textually identical and [rewrite] would hit the wrong occurrence. *)
  rewrite eval_seq_at. rewrite ast_block1_sim by exact Hgc. mt_readback_net.
  rewrite eval_seq_at. rewrite ast_block2_sim by exact Hgc. mt_readback_net.
  rewrite eval_seq_at.
  (* ---- final LN + output head ---- *)
  rewrite ast_ln_sem by mt_indep_tac. mt_readback_net.
  rewrite ast_bmm_sem by mt_indep_tac. mt_readback_net.

  (* fold the computed value to [MiniTransformer] *)
  (* positional instantiation: named-argument application is fragile under
     the implicit-argument setting here ("Wrong argument name" on 9.1.1) *)
  rewrite (CNN_CodeGen_Semantics.assign_in_acc_independent_of_env _ output_w _ _ rho _ Hin).
  apply assign_cong_at_p.
  unfold MiniTransformer_DPIA.MiniTransformer.
  rewrite MiniTransformer_DPIA.mt_x4_body, MiniTransformer_DPIA.mt_x3_body, MiniTransformer_DPIA.mt_x2_body, MiniTransformer_DPIA.mt_x1_body,
    MiniTransformer_DPIA.mt_x0_body.
  unfold MiniTransformer_DPIA.BEmbed, MiniTransformer_DPIA.BPos.
  rewrite <- block_value_fold. rewrite <- block_value_fold.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The bridge theorem                                                         *)
(* -------------------------------------------------------------------------- *)

Theorem Bridge_MiniTransformer_faithful : forall (rho : Proof_CodeGen.env) (p : DataExp.path),
  gelu_c_ok rho ->
  @MiniTransformer_DPIA.minitransformer_fresh 1 8 2 16 8 output_w rho ->
  Proof_CodeGen.in_acc p output_w ->
  CNN_CodeGen_Semantics.eval minitransformer_faithful_comm rho p =
  @MiniTransformer_DPIA.minitransformer_comm 1 8 2 16 32 8 mt_eps_v mt_toks
    (CNN_CodeGen_Semantics.to_pcg_exp tok_tab rho) (CNN_CodeGen_Semantics.to_pcg_exp pos_tab rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wk rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wo rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l1_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_w2 rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wk rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wo rho)
    (CNN_CodeGen_Semantics.to_pcg_exp l2_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_w2 rho)
    (CNN_CodeGen_Semantics.to_pcg_exp lnf_g rho) (CNN_CodeGen_Semantics.to_pcg_exp lnf_b rho)
    (CNN_CodeGen_Semantics.to_pcg_exp whead rho)
    output_w rho p.
Proof.
  intros rho p Hgc Hfresh Hin.
  (* full module path + positional explicit arguments: named arguments for
     the explicit Section-generalised binders are rejected by Rocq 9.1.1
     ("Wrong argument name", only the implicit ones are addressable) *)
  rewrite (MiniTransformer_DPIA.A_MiniTransformer
             (b:=1) (s:=8) (h:=2) (d:=16) (v:=8)
             32 mt_eps_v mt_toks
             (CNN_CodeGen_Semantics.to_pcg_exp tok_tab rho) (CNN_CodeGen_Semantics.to_pcg_exp pos_tab rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln1_b rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_ln2_b rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l1_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wk rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l1_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_wo rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l1_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l1_w2 rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln1_b rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_g rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_ln2_b rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l2_wq rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wk rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l2_wv rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_wo rho)
             (CNN_CodeGen_Semantics.to_pcg_exp l2_w1 rho) (CNN_CodeGen_Semantics.to_pcg_exp l2_w2 rho)
             (CNN_CodeGen_Semantics.to_pcg_exp lnf_g rho) (CNN_CodeGen_Semantics.to_pcg_exp lnf_b rho)
             (CNN_CodeGen_Semantics.to_pcg_exp whead rho)
             Hin Hfresh).
  cbv [DPIA_Rules.A]. cbn beta.
  apply faithful_sim; assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* Extraction for the streaming printers                                      *)
(* -------------------------------------------------------------------------- *)

Extraction "minitransformer_faithful_comm.ml" minitransformer_faithful_comm.
