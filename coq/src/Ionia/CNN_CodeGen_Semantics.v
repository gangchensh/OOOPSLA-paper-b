(* Semantics for the command AST defined in CNN_CodeGen_Core.v.
   We interpret CNN_CodeGen_Core.comm into Proof_CodeGen.comm (env -> env).
   This allows the functional-to-imperative rewrite rules in CNN_CodeGen.v
   to be stated and proved as semantic equalities rather than Leibniz
   equalities on the AST. *)

From Stdlib Require Import Reals String Ascii Nat List Bool Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import ProofIrrelevance.
From Stdlib Require Import Eqdep_dec Classical_Prop.
Import ListNotations.
Set Implicit Arguments.

Require Ionia.finType.
Module FT := Ionia.finType.
Import FT.

Require Ionia.vector.
Module V := Ionia.vector.

Require Ionia.DataExp.
Module DE := Ionia.DataExp.
Import DE.

Require Ionia.Proof_CodeGen.
Module PCG := Ionia.Proof_CodeGen.

Require Ionia.CNN_CodeGen_Core.
Module CG := Ionia.CNN_CodeGen_Core.

Require Ionia.CNN_Defs.
Module CD := Ionia.CNN_Defs.

(* -------------------------------------------------------------------------- *)
(* Auxiliary: decidable equality on [data].                                  *)
(* -------------------------------------------------------------------------- *)

Lemma fle_eq_dec : forall (n:nat) (x y : fle n), {x = y} + {x <> y}.
Proof.
  intros n [x Hx] [y Hy].
  destruct (Nat.eq_dec x y).
  - left. subst. f_equal. apply proof_irrelevance.
  - right. intro H. apply n0. injection H. auto.
Qed.

Definition fle_beq {n} (x y : fle n) : bool :=
  let (i, _) := x in let (j, _) := y in (i =? j)%nat.

Lemma fle_beq_eq : forall n (x y : fle n), fle_beq x y = true <-> x = y.
Proof.
  intros n [i Hi] [j Hj]. unfold fle_beq. simpl.
  split.
  - intro H. apply Nat.eqb_eq in H. subst. f_equal. apply proof_irrelevance.
  - intro H. injection H. intro. apply Nat.eqb_eq. auto.
Qed.

Lemma nat_eq_dec_refl (n : nat) : Nat.eq_dec n n = left (eq_refl n).
Proof. induction n; simpl; auto. rewrite IHn. reflexivity. Qed.

Fixpoint data_beq (d1 d2 : data) : bool :=
  match d1, d2 with
  | num, num => true
  | @ary n1 f1 d1, @ary n2 f2 d2 =>
      match Nat.eq_dec n1 n2 with
      | left Heq =>
          let f2' := eq_rect n2 (fun n => fle n) f2 n1 (eq_sym Heq) in
          (n1 =? n2)%nat && fle_beq f1 f2' && data_beq d1 d2
      | right _ => false
      end
  | _, _ => false
  end.

Lemma data_beq_eq : forall d1 d2, data_beq d1 d2 = true <-> d1 = d2.
Proof.
  intros d1 d2. split.
  - revert d2. induction d1 as [| n1 f1 d1 IHd1]; intros d2; destruct d2 as [| n2 f2 d2'];
    simpl; try discriminate; try reflexivity.
    destruct (Nat.eq_dec n1 n2) as [Heq | Hneq]; [| discriminate].
    subst n2. simpl. intros H. apply andb_true_iff in H. destruct H as [H1 H2].
    apply andb_true_iff in H1. destruct H1 as [Hn Hf].
    apply Nat.eqb_eq in Hn. apply fle_beq_eq in Hf. apply IHd1 in H2.
    subst. reflexivity.
  - revert d1. induction d2 as [| n2 f2 d2 IHd2]; intros d1 H.
    + subst d1. reflexivity.
    + subst d1. simpl.
      rewrite nat_eq_dec_refl. simpl. apply andb_true_iff. split.
      * apply andb_true_iff. split; [apply Nat.eqb_eq; reflexivity | apply fle_beq_eq; reflexivity].
      * apply IHd2. reflexivity.
Qed.

Lemma data_eq_dec : forall d1 d2 : data, {d1 = d2} + {d1 <> d2}.
Proof.
  intros. destruct (data_beq d1 d2) eqn:E.
  - left. apply data_beq_eq. auto.
  - right. intro H. apply data_beq_eq in H. rewrite H in E. discriminate.
Qed.

Lemma data_UIP : forall (d:data) (H:d=d), H = eq_refl d.
Proof. intros. apply UIP_dec. exact data_eq_dec. Qed.

(* Extract the initial assignment from the body of a [new]. *)
Definition init_info : Type := {d : data & acc d * exp d * CG.comm}%type.

Definition extract_init (c:CG.comm) : option init_info :=
  match c with
  | CG.seq (@CG.assign d (w,e), c') => Some (existT _ d (w,e,c'))
  | _ => None
  end.

(* -------------------------------------------------------------------------- *)
(* Main interpretation function.                                             *)
(* -------------------------------------------------------------------------- *)

(* Translation from the code-generation expression AST [DataExp.exp] to the
   semantic expression type [PCG.exp].  Scalar [REvar s] nodes are interpreted
   by looking up [s] in the current environment; this is necessary so that
   loop accumulators (which read the temporary variable ["__tmp"]) receive the
   correct current value at each iteration.  Array variables are accessed
   through paths as before. *)
Fixpoint to_pcg_exp {d:data} (e : DE.exp d) (rho : PCG.env) : PCG.exp d :=
  match d as d0 return DE.exp d0 -> PCG.env -> PCG.exp d0 with
  | num => fun e rho =>
      let val := fun s => match rho (DE.Var s) with Some r => r | None => R0 end in
      DE.eval_rexp val e
  | ary n d' => fun v rho =>
      V.mk_vec (fun i : fin n => to_pcg_exp (V.v_nth (DE.exp_default d') v (fin2nat i)) rho)
  end e rho.
Arguments to_pcg_exp : simpl never.

Lemma to_pcg_exp_mkvSeq : forall n d (f : fin n -> DE.exp d) rho,
  to_pcg_exp (DE.mkvSeq f) rho = PCG.mkvSeq (fun i => to_pcg_exp (f i) rho).
Proof.
  intros n d f rho. unfold DE.mkvSeq, PCG.mkvSeq. apply V.mk_vec_ext. intro i.
  cbv [to_pcg_exp]. rewrite V.v_nth_mk_vec with (H := fin_proof i).
  rewrite nat2fin_fin2nat. reflexivity.
Qed.

Lemma to_pcg_exp_REvar : forall s rho,
  to_pcg_exp (DE.REvar s : exp num) rho = match rho (DE.Var s) with Some r => r | None => R0 end.
Proof.
  intros s rho. cbv [to_pcg_exp]. simpl. reflexivity.
Qed.

Lemma to_pcg_exp_mkvPar : forall n d (f : fin n -> DE.exp d) rho,
  to_pcg_exp (DE.mkvPar f) rho = PCG.mkvPar (fun i => to_pcg_exp (f i) rho).
Proof.
  intros n d f rho. unfold DE.mkvPar, PCG.mkvPar. apply V.mk_vec_ext. intro i.
  cbv [to_pcg_exp]. rewrite V.v_nth_mk_vec with (H := fin_proof i).
  rewrite nat2fin_fin2nat. reflexivity.
Qed.

(* Assigning a vector literal is equivalent to a sequential loop that assigns
   each element.  This relies on the fact that [PCG.mkvSeq] is just a vector
   of element expressions. *)
Lemma assign_mkvSeq :
  forall n d (a : acc (ary '{n} d)) (g : fin n -> PCG.exp d),
    @PCG.assign (ary '{n} d) a (PCG.mkvSeq g) =
    PCG.seqfor (fun i => @PCG.assign d (DE.idxAcc a i) (g i)).
Proof.
  intros n d a g.
  apply PCG.seqfor_extensionality. intro i.
  apply functional_extensionality. intro rho.
  simpl. unfold PCG.idx, PCG.mkvSeq. rewrite V.v_idx_mk_vec. reflexivity.
Qed.

(* Fresh temporary name at nesting depth [depth].  Depth 0 is ["__tmp"],
   depth 1 is ["__tmp_"], depth 2 is ["__tmp__"], etc. *)
Fixpoint tmp_name (depth : nat) : string :=
  match depth with
  | 0 => "__tmp"
  | S n => String.append (tmp_name n) "_"
  end.

(* Interpret a CNN_CodeGen AST command as a semantic command (env -> env).
   The [new] construct is interpreted as allocation + initialisation +
   continuation + deallocation.  Because [new] takes a black-box function
   argument, we inspect the body at a representative temporary and extract
   the initial value from the first assignment.  This works for all the
   well-formed [new] bodies produced by CNN_CodeGen.v (maxl, reducel, suml,
   and the semantic rules [CmkvSeq_sem], [CmkvPar_sem], [Clet_sem]).

   The [depth] parameter supplies distinct temporary names for nested
   [loopacc]/[new] constructs: each binder uses [tmp_name depth] for its
   temporary and evaluates its body at [S depth]. *)
Fixpoint eval_aux (c:CG.comm) (depth:nat) {struct c} : PCG.comm :=
  match c with
  | CG.skip => PCG.skip
  | CG.If b (c1,c2) =>
      fun rho =>
        let val := fun s => match rho (DE.Var s) with Some r => r | None => R0 end in
        PCG.If (DE.eval_bexp val b) (eval_aux c1 depth) (eval_aux c2 depth) rho
  | CG.seq (c1,c2) => PCG.seq (eval_aux c1 depth) (eval_aux c2 depth)
  | @CG.assign d (a,e) => fun rho => @PCG.assign d a (to_pcg_exp e rho) rho
  | @CG.loopacc d p =>
      let name := tmp_name depth in
      let wtmp := CG.vwt name in
      PCG.seq (eval_aux (p name) (S depth)) (@PCG.vrm d wtmp)
  | @CG.new d p =>
      let name := tmp_name depth in
      let wtmp := PCG.acc' (DE.Var name) in
      let v0 := DE.exp_default d in
      match extract_init (p (wtmp, v0)) with
      | Some (existT _ d0 (w', e1, c')) =>
          match data_eq_dec d0 d with
          | left Heq =>
              let e1' := eq_rect d0 (fun d => exp d) e1 d Heq in
              PCG.seq (eval_aux (p (wtmp, e1')) (S depth)) (@PCG.vrm d wtmp)
          | right _ => PCG.skip
          end
      | None => PCG.skip
      end
  | @CG.seqfor n p => @PCG.seqfor n (fun i => eval_aux (p i) depth)
  | @CG.parfor n d a p => @PCG.seqfor n (fun i => eval_aux (p i (DE.idxAcc a i)) depth)
  end.

Definition eval (c:CG.comm) : PCG.comm := eval_aux c 0.

(* Expose how [eval_aux] interprets assignments and [CG.seqfor].
   These are independent of the naming depth. *)
Lemma eval_assign_aux : forall depth d (a : DE.acc d) (e : DE.exp d) (rho : PCG.env),
  eval_aux (CG.assign (a, e)) depth rho = PCG.assign a (to_pcg_exp e rho) rho.
Proof. reflexivity. Qed.

Lemma eval_assign : forall d (a : DE.acc d) (e : DE.exp d) (rho : PCG.env),
  eval (CG.assign (a, e)) rho = PCG.assign a (to_pcg_exp e rho) rho.
Proof. intros. unfold eval. apply eval_assign_aux. Qed.

Lemma eval_seqfor_aux : forall depth n (f : fin n -> CG.comm) (rho : PCG.env),
  eval_aux (CG.seqfor f) depth rho = PCG.seqfor (fun i => eval_aux (f i) depth) rho.
Proof. reflexivity. Qed.

Lemma eval_seqfor : forall n (f : fin n -> CG.comm) (rho : PCG.env),
  eval (CG.seqfor f) rho = PCG.seqfor (fun i => eval (f i)) rho.
Proof. intros. unfold eval. apply eval_seqfor_aux. Qed.

Lemma eval_seq_aux : forall depth (c1 c2 : CG.comm) (rho : PCG.env),
  eval_aux (CG.seq (c1, c2)) depth rho = PCG.seq (eval_aux c1 depth) (eval_aux c2 depth) rho.
Proof. reflexivity. Qed.

Lemma eval_loopacc_aux : forall depth d (p : string -> CG.comm) (rho : PCG.env),
  eval_aux (@CG.loopacc d p) depth rho =
  PCG.seq (eval_aux (p (tmp_name depth)) (S depth))
          (@PCG.vrm d (CG.vwt (tmp_name depth))) rho.
Proof. reflexivity. Qed.

(* One-level unfolding of [PCG.seqfor] for successor lengths. *)
Lemma seqfor_S : forall n' (p : fin (S n') -> PCG.comm),
  PCG.seqfor p =
  PCG.seq (PCG.seqfor (fun i : fin n' => p (fin2finS i))) (p (ltS n')).
Proof. reflexivity. Qed.

(* Invariant-preserving pointwise equality for [PCG.seqfor].  If each
   iteration maps environments satisfying [P] to equal environments that
   still satisfy [P], then the whole loop produces equal results and preserves
   [P].  This is needed because the semantic combinators are only available
   pointwise under side conditions such as [StructUndefined]. *)
Lemma seqfor_pointwise_inv :
  forall n (f g : fin n -> PCG.comm) (rho : PCG.env) (P : PCG.env -> Prop),
    P rho ->
    (forall i eta, P eta -> (f i eta = g i eta) /\ P (f i eta)) ->
    (PCG.seqfor f rho = PCG.seqfor g rho) /\ P (PCG.seqfor f rho).
Proof.
  intros n f g rho P HP Hstep.
  Opaque PCG.seqfor.
  induction n as [| n' IHn].
  - simpl. split; [reflexivity | assumption].
  - assert (IH :
      (PCG.seqfor (fun i : fin n' => f (fin2finS i)) rho =
       PCG.seqfor (fun i : fin n' => g (fin2finS i)) rho) /\
      P (PCG.seqfor (fun i : fin n' => f (fin2finS i)) rho)).
    { apply IHn. intros i eta HPeta. apply Hstep. exact HPeta. }
    destruct IH as [Heq HPeta].
    destruct (Hstep (ltS n') (PCG.seqfor (fun i : fin n' => f (fin2finS i)) rho))
      as [Hbody HPbody].
    { exact HPeta. }
    split.
    + rewrite seqfor_S in |- *. unfold PCG.seq in |- *.
      rewrite Hbody in |- *. rewrite Heq in |- *. reflexivity.
    + rewrite seqfor_S in |- *. unfold PCG.seq in |- *. exact HPbody.
Qed.
Transparent PCG.seqfor.

(* -------------------------------------------------------------------------- *)
(* Semantic versions of the non-new Axioms in CNN_CodeGen.v.                 *)
(* -------------------------------------------------------------------------- *)

(* -------------------------------------------------------------------------- *)
(* Independence of code-generation expressions from a path/region.           *)
(* -------------------------------------------------------------------------- *)

(* Structural predicate: a real expression does not read the path [p]. *)
Fixpoint rexp_independent_of_path (e : DE.rexp) (p : DE.path) : Prop :=
  match e with
  | REvar s => DE.Var s <> p
  | REconst r s => True
  | REopp e' => rexp_independent_of_path e' p
  | REadd e1 e2 => rexp_independent_of_path e1 p /\ rexp_independent_of_path e2 p
  | REsub e1 e2 => rexp_independent_of_path e1 p /\ rexp_independent_of_path e2 p
  | REmul e1 e2 => rexp_independent_of_path e1 p /\ rexp_independent_of_path e2 p
  | REdiv e1 e2 => rexp_independent_of_path e1 p /\ rexp_independent_of_path e2 p
  | REdiv_n e' n => rexp_independent_of_path e' p
  | REscal r e' => rexp_independent_of_path e' p
  | REpow e' n => rexp_independent_of_path e' p
  | REexp e' => rexp_independent_of_path e' p
  | REln e' => rexp_independent_of_path e' p
  | REsqrt e' => rexp_independent_of_path e' p
  | REif b e1 e2 => bexp_independent_of_path b p /\
                      rexp_independent_of_path e1 p /\ rexp_independent_of_path e2 p
  end
with bexp_independent_of_path (b : DE.bexp) (p : DE.path) : Prop :=
  match b with
  | BTrue | BFalse => True
  | BLe e1 e2 | BGt e1 e2 =>
      rexp_independent_of_path e1 p /\ rexp_independent_of_path e2 p
  | BLt _ _ | BEq _ _ | BLeb _ _ => True
  | BAnd b1 b2 => bexp_independent_of_path b1 p /\ bexp_independent_of_path b2 p
  | BNot b' => bexp_independent_of_path b' p
  end.

(* [exp_independent_of_path e p] lifts the structural independence predicate to
   arbitrary [data] by demanding independence of every vector element for arrays. *)
Fixpoint exp_independent_of_path {d} (e : DE.exp d) (p : DE.path) : Prop :=
  match d as d0 return DE.exp d0 -> Prop with
  | num => fun e => rexp_independent_of_path e p
  | ary n d' => fun v =>
      forall i : fin n, exp_independent_of_path (V.v_nth (DE.exp_default d') v (fin2nat i)) p
  end e.

(* [exp_independent_of_acc e a] means [e] does not read any leaf path inside
   the acceptor [a].  This is the side condition needed for array constructors
   and accumulator loops: it guarantees that evaluating [e] at the initial
   environment or at any environment reachable by modifying [a] yields the same
   value. *)
Definition exp_independent_of_acc {d d'} (e : DE.exp d) (a : acc d') : Prop :=
  forall p, @PCG.in_acc d' p a -> @exp_independent_of_path d e p.

Ltac derive_subexp_indep :=
  let p := fresh "p" in
  let Hp := fresh "Hp" in
  intros p Hp;
  match goal with
  | Hind' : exp_independent_of_acc _ _ |- _ =>
      specialize (Hind' p Hp); simpl in Hind'; tauto
  end.

(* A variable read [REvar s] is independent of [p] iff [Var s <> p]. *)
Lemma REvar_independent_neq : forall s p,
  @exp_independent_of_path num (DE.REvar s) p -> DE.Var s <> p.
Proof.
  intros s p Hind. simpl in Hind. exact Hind.
Qed.

(* Scalar [rexp] and boolean expressions are mutually inductive.  We prove the
   scalar evaluation lemma mutually with the boolean one. *)
Lemma rexp_independent_of_acc_eval :
  forall d' (e : DE.rexp) (a : acc d'),
    exp_independent_of_acc (e : exp num) a ->
    forall rho1 rho2,
      (forall q, ~ @PCG.in_acc d' q a -> rho1 q = rho2 q) ->
      to_pcg_exp (e : exp num) rho1 = to_pcg_exp (e : exp num) rho2
with bexp_independent_eval :
  forall d' (b : DE.bexp) (a : acc d'),
    (forall p, @PCG.in_acc d' p a -> bexp_independent_of_path b p) ->
    forall rho1 rho2,
      (forall q, ~ @PCG.in_acc d' q a -> rho1 q = rho2 q) ->
      DE.eval_bexp (fun s => match rho1 (DE.Var s) with Some r => r | None => R0 end) b =
      DE.eval_bexp (fun s => match rho2 (DE.Var s) with Some r => r | None => R0 end) b.
Proof.
  - (* rexp_independent_of_acc_eval *)
    intros d' e a Hind rho1 rho2 Hagree.
    revert Hind.
    induction e as [s | r s | e1 IHe1 | e1 IHe1 | e1 IHe1 e2 IHe2
                   | e1 IHe1 e2 IHe2 | e1 IHe1 e2 IHe2 | e1 IHe1 n'
                   | r e1 IHe1 | e1 IHe1 n' | e1 IHe1 | e1 IHe1 | e1 IHe1
                   | b e1 IHe1 e2 IHe2];
      intro Hind'; unfold to_pcg_exp in *; simpl in *.
    + (* REvar *)
      assert (Hnotin : ~ @PCG.in_acc d' (DE.Var s) a).
      { intro Hin. apply Hind' in Hin. contradiction. }
      specialize (Hagree (DE.Var s) Hnotin).
      rewrite Hagree. reflexivity.
    + (* REconst *) reflexivity.
    + (* REopp *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REadd *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      assert (Hind2 : exp_independent_of_acc (e2 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1), (IHe2 Hind2). reflexivity.
    + (* REsub *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      assert (Hind2 : exp_independent_of_acc (e2 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1), (IHe2 Hind2). reflexivity.
    + (* REmul *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      assert (Hind2 : exp_independent_of_acc (e2 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1), (IHe2 Hind2). reflexivity.
    + (* REdiv *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      assert (Hind2 : exp_independent_of_acc (e2 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1), (IHe2 Hind2). reflexivity.
    + (* REdiv_n *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REscal *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REpow *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REexp *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REln *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REsqrt *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      rewrite (IHe1 Hind1). reflexivity.
    + (* REif *)
      assert (Hind1 : exp_independent_of_acc (e1 : exp num) a) by derive_subexp_indep.
      assert (Hind2 : exp_independent_of_acc (e2 : exp num) a) by derive_subexp_indep.
      assert (Hind_b : forall p, @PCG.in_acc d' p a -> bexp_independent_of_path b p)
        by (intros p Hp; specialize (Hind' p Hp); simpl in Hind'; tauto).
      rewrite (IHe1 Hind1), (IHe2 Hind2).
      erewrite (bexp_independent_eval d' b a Hind_b rho1 rho2 Hagree).
      reflexivity.
  - (* bexp_independent_eval *)
    intros d' b a Hind rho1 rho2 Hagree.
    induction b as [| | e1 e2 | e1 e2 | i n | i n | i n | b1 IHb1 b2 IHb2 | b' IHb'];
      simpl.
    + (* BTrue *) reflexivity.
    + (* BFalse *) reflexivity.
    + (* BLe *)
      assert (He1 : forall p, @PCG.in_acc d' p a -> rexp_independent_of_path e1 p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      assert (He2 : forall p, @PCG.in_acc d' p a -> rexp_independent_of_path e2 p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      assert (Hv1 : to_pcg_exp (e1 : exp num) rho1 = to_pcg_exp (e1 : exp num) rho2)
        by (apply rexp_independent_of_acc_eval with (a := a); [exact He1 | exact Hagree]).
      assert (Hv2 : to_pcg_exp (e2 : exp num) rho1 = to_pcg_exp (e2 : exp num) rho2)
        by (apply rexp_independent_of_acc_eval with (a := a); [exact He2 | exact Hagree]).
      unfold to_pcg_exp in Hv1, Hv2; simpl in Hv1, Hv2. rewrite Hv1, Hv2. reflexivity.
    + (* BGt *)
      assert (He1 : forall p, @PCG.in_acc d' p a -> rexp_independent_of_path e1 p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      assert (He2 : forall p, @PCG.in_acc d' p a -> rexp_independent_of_path e2 p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      assert (Hv1 : to_pcg_exp (e1 : exp num) rho1 = to_pcg_exp (e1 : exp num) rho2)
        by (apply rexp_independent_of_acc_eval with (a := a); [exact He1 | exact Hagree]).
      assert (Hv2 : to_pcg_exp (e2 : exp num) rho1 = to_pcg_exp (e2 : exp num) rho2)
        by (apply rexp_independent_of_acc_eval with (a := a); [exact He2 | exact Hagree]).
      unfold to_pcg_exp in Hv1, Hv2; simpl in Hv1, Hv2. rewrite Hv1, Hv2. reflexivity.
    + (* BLt *) reflexivity.
    + (* BEq *) reflexivity.
    + (* BLeb *) reflexivity.
    + (* BAnd *)
      assert (Hb1 : forall p, @PCG.in_acc d' p a -> bexp_independent_of_path b1 p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      assert (Hb2 : forall p, @PCG.in_acc d' p a -> bexp_independent_of_path b2 p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      rewrite (IHb1 Hb1), (IHb2 Hb2).
      reflexivity.
    + (* BNot *)
      assert (Hb' : forall p, @PCG.in_acc d' p a -> bexp_independent_of_path b' p)
        by (intros p Hp; specialize (Hind p Hp); simpl in Hind; tauto).
      rewrite (IHb' Hb').
      reflexivity.
Qed.

(* Lift the scalar independence lemma to arbitrary [exp d]. *)
Lemma exp_independent_of_acc_eval :
  forall d d' (e : DE.exp d) (a : acc d'),
    exp_independent_of_acc e a ->
    forall rho1 rho2,
      (forall q, ~ @PCG.in_acc d' q a -> rho1 q = rho2 q) ->
      to_pcg_exp e rho1 = to_pcg_exp e rho2.
Proof.
  induction d as [| n d1 IHd]; intros d2 e a Hind rho1 rho2 Hagree.
  - (* scalar *)
    apply rexp_independent_of_acc_eval with (a := a). exact Hind. exact Hagree.
  - (* array: each element is independent of [a] by definition. *)
    apply V.mk_vec_ext. intro i.
    apply (IHIHd d2 (V.v_nth (DE.exp_default IHd) e (fin2nat i)) a).
    + intros p Hp. apply (Hind p Hp i).
    + exact Hagree.
Qed.

(* -------------------------------------------------------------------------- *)
(* Commands that only modify a given acceptor region.                        *)
(* -------------------------------------------------------------------------- *)

Definition command_modifies_only {d} (c : PCG.comm) (a : acc d) : Prop :=
  forall rho q, ~ @PCG.in_acc d q a -> c rho q = rho q.

Lemma in_acc_ary_inv : forall n (m:fle n) d (a : acc (ary m d)) p (i : fin m),
  @PCG.in_acc d p (a |{ i}) -> @PCG.in_acc (ary m d) p a.
Proof.
  intros n m d a p i Hin. simpl. exists i. exact Hin.
Qed.

Lemma modifies_only_weaken_ary :
  forall n (m:fle n) d1 (c : PCG.comm) (a : acc (ary m d1)) (i : fin m),
    command_modifies_only c (a |{ i}) -> command_modifies_only c a.
Proof.
  intros n m d1 c a i Hmod rho q Hq. apply Hmod. intro Hin. apply Hq.
  apply in_acc_ary_inv with (i := i). exact Hin.
Qed.

Lemma seqfor_modifies_only :
  forall n (p : fin n -> PCG.comm) d (a : acc d),
    (forall i, command_modifies_only (p i) a) ->
    command_modifies_only (PCG.seqfor p) a.
Proof.
  induction n as [| n' IHn]; intros p d a Hmod rho q Hq.
  - simpl. reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq.
    assert (Hlast : command_modifies_only (p '[n']) a) by apply Hmod.
    unfold command_modifies_only in Hlast.
    rewrite (Hlast (PCG.seqfor (fun i : fin n' => p FS[i]) rho) q Hq).
    refine (IHn (fun i : fin n' => p FS[i]) d a (fun i => Hmod (FS[i])) rho q Hq).
Qed.

Lemma assign_modifies_only : forall d (a : acc d) (e : PCG.exp d),
  command_modifies_only (PCG.assign a e) a.
Proof.
  induction d as [| m d1 IHd]; intros a e.
  - unfold command_modifies_only. intros rho q Hq. simpl.
    rewrite PCG.update_neq; [reflexivity | ].
    intro Hc. apply Hq. simpl. exact Hc.
  - unfold command_modifies_only. intros rho q Hq. simpl.
    apply (seqfor_modifies_only (fun i => PCG.assign (PCG.idxAcc a i) (PCG.idx e i))
                                (fun i => modifies_only_weaken_ary _ (IHIHd (PCG.idxAcc a i) (PCG.idx e i)))
                                rho q Hq).
Qed.

(* Semantic version of mkvSeq_equiv. *)
Theorem eval_mkvSeq :
  forall n d (f : fin n -> exp d) (a : acc (ary '{n} d)),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (CG.assign (a, DE.mkvSeq f)) =
    eval (CG.seqfor (fun i => CG.assign (DE.idxAcc a i, f i))).
Proof.
  intros n d f a Hindep.
  apply functional_extensionality. intro rho.
  rewrite eval_assign.
  rewrite to_pcg_exp_mkvSeq.
  rewrite assign_mkvSeq.
  simpl.
  apply seqfor_pointwise_inv
    with (P := fun eta => forall q, ~ @PCG.in_acc (ary '{n} d) q a -> eta q = rho q);
    [ | intros i eta HP; split ].
  - intros q Hq. reflexivity.
  - apply functional_extensionality. intro p.
    assert (Heq : to_pcg_exp (f i) eta = to_pcg_exp (f i) rho).
    { apply exp_independent_of_acc_eval with (a := a); [ apply Hindep | exact HP ]. }
    rewrite Heq. reflexivity.
  - intros q Hq.
    assert (Hmod : command_modifies_only (@PCG.assign d (DE.idxAcc a i) (to_pcg_exp (f i) rho)) a).
    { eapply modifies_only_weaken_ary. apply assign_modifies_only. }
    unfold command_modifies_only in Hmod. rewrite (Hmod eta q Hq). apply HP. exact Hq.
Qed.

(* Semantic version of mkvPar_equiv. *)
Theorem eval_mkvPar :
  forall n d (f : fin n -> exp d) (a : acc (ary '{n} d)),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (CG.assign (a, DE.mkvPar f)) =
    eval (CG.parfor a (fun i o => CG.assign (o, f i))).
Proof.
  intros n d f a Hindep.
  apply functional_extensionality. intro rho.
  rewrite eval_assign.
  rewrite to_pcg_exp_mkvPar.
  rewrite assign_mkvSeq.
  simpl.
  apply seqfor_pointwise_inv
    with (P := fun eta => forall q, ~ @PCG.in_acc (ary '{n} d) q a -> eta q = rho q);
    [ | intros i eta HP; split ].
  - intros q Hq. reflexivity.
  - apply functional_extensionality. intro p.
    assert (Heq : to_pcg_exp (f i) eta = to_pcg_exp (f i) rho).
    { apply exp_independent_of_acc_eval with (a := a); [ apply Hindep | exact HP ]. }
    rewrite Heq. reflexivity.
  - intros q Hq.
    assert (Hmod : command_modifies_only (@PCG.assign d (DE.idxAcc a i) (to_pcg_exp (f i) rho)) a).
    { eapply modifies_only_weaken_ary. apply assign_modifies_only. }
    unfold command_modifies_only in Hmod. rewrite (Hmod eta q Hq). apply HP. exact Hq.
Qed.

(* Semantic versions of If-distribution rules, now pointwise over the
   environment.  The side condition says that the runtime truth value of [b]
   in [rho] agrees with the static evaluation [bexp2bool b]; this holds for
   the purely static conditions used for padding/loop bounds. *)
Theorem eval_If :
  forall n d (a : acc (ary '{n} d)) (b:DE.bexp) (e1 e2 : exp d) (i : fin n) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (CG.assign (DE.idxAcc a i, if DE.bexp2bool b then e1 else e2)) rho =
    eval (CG.If b (CG.assign (DE.idxAcc a i, e1), CG.assign (DE.idxAcc a i, e2))) rho.
Proof.
  intros. unfold eval in *. simpl in *. rewrite H. destruct (DE.bexp2bool b); reflexivity.
Qed.

Theorem eval_If1 :
  forall d (a : acc d) (b:DE.bexp) (e1 e2 : exp d) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (CG.assign (a, if DE.bexp2bool b then e1 else e2)) rho =
    eval (CG.If b (CG.assign (a, e1), CG.assign (a, e2))) rho.
Proof.
  intros. unfold eval in *. simpl in *. rewrite H. destruct (DE.bexp2bool b); reflexivity.
Qed.

Theorem eval_cIf :
  forall d (b:DE.bexp) (e1 e2 : exp d) (c : exp d -> CG.comm) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (c (if DE.bexp2bool b then e1 else e2)) rho =
    eval (CG.If b (c e1, c e2)) rho.
Proof.
  intros. unfold eval in *. simpl in *. rewrite H. destruct (DE.bexp2bool b); reflexivity.
Qed.

(* An indexed assignment only modifies the region of the enclosing array. *)
Lemma eval_assign_idx_modifies_only :
  forall n d (a : acc (ary '{n} d)) (i : fin n) (e : exp d),
    command_modifies_only (eval (CG.assign (DE.idxAcc a i, e))) a.
Proof.
  intros n d a i e rho q Hq.
  rewrite eval_assign.
  assert (Hmod : command_modifies_only (PCG.assign (DE.idxAcc a i) (to_pcg_exp e rho)) a).
  { eapply modifies_only_weaken_ary. apply assign_modifies_only. }
  exact (Hmod rho q Hq).
Qed.

(* Pointwise If-lifting under [seqfor]: a loop assigning statically-branched
   expressions evaluates to the loop of imperative conditionals, provided the
   branch conditions do not read the output region and their runtime values in
   [rho] agree with the static evaluations.  This is the semantic workhorse
   behind the ReLU-family equivalence theorems ([ReLU1d_equiv_sem] etc.). *)
Theorem seqfor_If_sem :
  forall n d (a : acc (ary '{n} d)) (b : fin n -> DE.bexp)
         (e1 e2 : fin n -> exp d) (rho : PCG.env),
    (forall i p, @PCG.in_acc (ary '{n} d) p a -> bexp_independent_of_path (b i) p) ->
    (forall i, DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) (b i)
               = DE.bexp2bool (b i)) ->
    eval (CG.seqfor (fun i => CG.assign (DE.idxAcc a i, if DE.bexp2bool (b i) then e1 i else e2 i))) rho =
    eval (CG.seqfor (fun i => CG.If (b i) (CG.assign (DE.idxAcc a i, e1 i),
                                          CG.assign (DE.idxAcc a i, e2 i)))) rho.
Proof.
  intros n d a b e1 e2 rho Hbindep Hbeq.
  rewrite !eval_seqfor.
  apply seqfor_pointwise_inv
    with (P := fun eta => forall q, ~ @PCG.in_acc (ary '{n} d) q a -> eta q = rho q);
    [ | intros i eta HP; split ].
  - intros q Hq. reflexivity.
  - cbn beta. apply eval_If1.
    rewrite <- (Hbeq i).
    apply bexp_independent_eval with (a := a).
    + exact (Hbindep i).
    + exact HP.
  - intros q Hq. cbn beta. transitivity (eta q).
    + apply eval_assign_idx_modifies_only. exact Hq.
    + apply HP. exact Hq.
Qed.

(* -------------------------------------------------------------------------- *)
(* Well-formedness predicate for [new] bodies.                               *)
(* -------------------------------------------------------------------------- *)

Definition new_body {d:data} (p:acc d * exp d -> CG.comm)
                    (w:acc d) (e1:exp d) (c:exp d -> CG.comm) : Prop :=
  forall v, p (w,v) = CG.seq (CG.assign (w,e1), c v).

(* -------------------------------------------------------------------------- *)
(* Semantic expansion of well-formed [new] bodies.                           *)
(* -------------------------------------------------------------------------- *)

(* For a well-formed new body, eval reduces to: assign the initial value to a
   fresh temporary, run the continuation with the initial value bound, and
   finally remove the temporary.  The temporary name is determined by the
   current [depth]; the continuation runs at [S depth] so that any nested
   [loopacc]/[new] inside it receives fresh names. *)
Lemma eval_new_body :
  forall d depth (p : acc d * exp d -> CG.comm) (e1 : exp d) (c : exp d -> CG.comm),
    new_body p (PCG.acc' (DE.Var (tmp_name depth))) e1 c ->
    eval_aux (CG.new p) depth =
    PCG.seq (fun rho => @PCG.assign d (PCG.acc' (DE.Var (tmp_name depth))) (to_pcg_exp e1 rho) rho)
            (PCG.seq (eval_aux (c e1) (S depth)) (@PCG.vrm d (PCG.acc' (DE.Var (tmp_name depth))))).
Proof.
  intros d depth p e1 c Hbody.
  unfold eval_aux. fold eval_aux. fold tmp_name.
  unfold extract_init.
  rewrite Hbody. simpl.
  destruct (data_eq_dec d d) as [Heq | Hneq].
  - rewrite (data_UIP Heq). simpl.
    rewrite Hbody. reflexivity.
  - exfalso. apply Hneq. reflexivity.
Qed.

(* The canonical new body produced by CNN_CodeGen.v combinators satisfies
   the [new_body] predicate. *)
Lemma new_body_canonical :
  forall d (e1 : exp d) (c : exp d -> CG.comm) (w : acc d),
    new_body (fun tmp => let (w,v) := tmp in CG.seq (CG.assign (w,e1), c v)) w e1 c.
Proof.
  intros d e1 c w v.
  reflexivity.
Qed.

(* Specialisation of [eval_new_body] to the canonical new body at depth 0. *)
Lemma eval_new_canonical_body :
  forall d (e1 : exp d) (c : exp d -> CG.comm),
    eval (CG.new (fun tmp => let (w,v) := tmp in CG.seq (CG.assign (w,e1), c v))) =
    PCG.seq (fun rho => @PCG.assign d (PCG.acc' (DE.Var "__tmp")) (to_pcg_exp e1 rho) rho)
            (PCG.seq (eval_aux (c e1) 1) (@PCG.vrm d (PCG.acc' (DE.Var "__tmp")))).
Proof.
  intros. unfold eval. apply eval_new_body. apply new_body_canonical.
Qed.

(* Pointwise version convenient for applying [PCG_dead_store_disjoint]. *)
Lemma eval_new_canonical_body_at :
  forall d (e1 : exp d) (c : exp d -> CG.comm) (rho : PCG.env),
    eval (CG.new (fun tmp => let (w,v) := tmp in CG.seq (CG.assign (w,e1), c v))) rho =
    PCG.seq (PCG.assign (PCG.acc' (DE.Var "__tmp")) (to_pcg_exp e1 rho))
            (PCG.seq (eval_aux (c e1) 1) (@PCG.vrm d (PCG.acc' (DE.Var "__tmp"))))
            rho.
Proof.
  intros. rewrite eval_new_canonical_body. reflexivity.
Qed.


(* Side conditions under which a continuation [c e1] behaves independently of
   the fresh temporary: it must preserve undefinedness of the temporary region
   and its output at every path outside the temporary region must not depend
   on values inside the temporary region.  Both components mirror
   [loopacc_continuation_ok].  The continuation is evaluated at depth 1
   (inside the [new] body). *)
Definition new_continuation_ok {d} (c : exp d -> CG.comm) (e1 : exp d) : Prop :=
  let wtmp := PCG.acc' (DE.Var "__tmp") in
  (forall rho, @PCG.StructUndefined d wtmp rho ->
               @PCG.StructUndefined d wtmp (eval_aux (c e1) 1 rho)) /\
  (forall rho p eta,
     (forall q, ~ @PCG.in_acc d q wtmp -> eta q = rho q) ->
     ~ @PCG.in_acc d p wtmp ->
     eval_aux (c e1) 1 eta p = eval_aux (c e1) 1 rho p).

(* Semantic version of [new_equiv].
   Under the side conditions above, a well-formed [new] behaves exactly like
   running its continuation with the initial value bound (at depth 1). *)
Theorem eval_new_equiv :
  forall d (e1 : exp d) (c : exp d -> CG.comm),
    new_continuation_ok c e1 ->
    forall rho,
      @PCG.StructUndefined d (PCG.acc' (DE.Var "__tmp")) rho ->
      eval (CG.new (fun tmp => let (w,v) := tmp in CG.seq (CG.assign (w,e1), c v))) rho =
      eval_aux (c e1) 1 rho.
Proof.
  intros d e1 c Hok rho Hrho.
  rewrite eval_new_canonical_body.
  unfold PCG.seq. simpl.
  apply functional_extensionality. intro p.
  destruct Hok as [Hnone Hread].
  set (wtmp := PCG.acc' (DE.Var "__tmp")).
  set (eta := @PCG.assign d wtmp (to_pcg_exp e1 rho) rho).
  assert (Heta : forall q, ~ @PCG.in_acc d q wtmp -> eta q = rho q).
  { intros q Hq. apply PCG.assign_not_in_acc. exact Hq. }
  destruct (classic (@PCG.in_acc d p wtmp)) as [Hin | Hout].
  - assert (Hvrm : @PCG.vrm d wtmp (eval_aux (c e1) 1 eta) p = None).
    { apply PCG.vrm_in_acc. exact Hin. }
    rewrite Hvrm.
    symmetry. apply PCG.StructUndefined_implies_None with (a := wtmp).
    + apply Hnone. exact Hrho.
    + exact Hin.
  - assert (Hc : eval_aux (c e1) 1 eta p = eval_aux (c e1) 1 rho p).
    { apply Hread; [exact Heta | exact Hout]. }
    assert (Hvrm : @PCG.vrm d wtmp (eval_aux (c e1) 1 eta) p = eval_aux (c e1) 1 eta p).
    { apply PCG.vrm_not_in_acc. exact Hout. }
    rewrite Hvrm. rewrite Hc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generalised [new] equivalence to arbitrary naming depth.                  *)
(* -------------------------------------------------------------------------- *)

(* Side conditions for a [new] evaluated at an arbitrary [depth].  The
   temporary region is [acc' (tmp_name depth)] and the continuation runs at
   [S depth] so that any nested [new]/[loopacc] inside it gets a fresh name.
   Both components are preservation/restriction statements (an undefined
   temporary region stays undefined; outputs are compared only at paths
   outside the temporary region), mirroring [loopacc_continuation_ok]. *)
Definition new_continuation_ok_at (depth : nat) {d} (c : exp d -> CG.comm) (e1 : exp d) : Prop :=
  let wtmp := PCG.acc' (DE.Var (tmp_name depth)) in
  (forall rho, @PCG.StructUndefined d wtmp rho ->
               @PCG.StructUndefined d wtmp (eval_aux (c e1) (S depth) rho)) /\
  (forall rho p eta,
     (forall q, ~ @PCG.in_acc d q wtmp -> eta q = rho q) ->
     ~ @PCG.in_acc d p wtmp ->
     eval_aux (c e1) (S depth) eta p = eval_aux (c e1) (S depth) rho p).

(* The existing depth-0 predicate is exactly the [depth = 0] instance. *)
Lemma new_continuation_ok_at_0 :
  forall d (c : exp d -> CG.comm) (e1 : exp d),
    new_continuation_ok_at 0 c e1 <-> new_continuation_ok c e1.
Proof.
  intros. unfold new_continuation_ok_at, new_continuation_ok. simpl. reflexivity.
Qed.

(* Generalisation of [eval_new_equiv] to any naming depth.  The proof is the
   same as the depth-0 version, using [eval_new_body] instead of
   [eval_new_canonical_body]. *)
Theorem eval_new_equiv_gen :
  forall d depth (e1 : exp d) (c : exp d -> CG.comm) rho,
    new_continuation_ok_at depth c e1 ->
    @PCG.StructUndefined d (PCG.acc' (DE.Var (tmp_name depth))) rho ->
    eval_aux (CG.new (fun tmp => let (w,v) := tmp in CG.seq (CG.assign (w,e1), c v))) depth rho =
    eval_aux (c e1) (S depth) rho.
Proof.
  intros d depth e1 c rho Hok Hrho.
  rewrite eval_new_body with (e1 := e1) (c := c).
  - unfold PCG.seq. simpl.
    apply functional_extensionality. intro p.
    destruct Hok as [Hnone Hread].
    set (wtmp := PCG.acc' (DE.Var (tmp_name depth))).
    set (eta := @PCG.assign d wtmp (to_pcg_exp e1 rho) rho).
    assert (Heta : forall q, ~ @PCG.in_acc d q wtmp -> eta q = rho q).
    { intros q Hq. apply PCG.assign_not_in_acc. exact Hq. }
    destruct (classic (@PCG.in_acc d p wtmp)) as [Hin | Hout].
    + assert (Hvrm : @PCG.vrm d wtmp (eval_aux (c e1) (S depth) eta) p = None).
      { apply PCG.vrm_in_acc. exact Hin. }
      rewrite Hvrm.
      symmetry. apply PCG.StructUndefined_implies_None with (a := wtmp).
      * apply Hnone. exact Hrho.
      * exact Hin.
    + assert (Hc : eval_aux (c e1) (S depth) eta p = eval_aux (c e1) (S depth) rho p).
      { apply Hread; [exact Heta | exact Hout]. }
      assert (Hvrm : @PCG.vrm d wtmp (eval_aux (c e1) (S depth) eta) p = eval_aux (c e1) (S depth) eta p).
      { apply PCG.vrm_not_in_acc. exact Hout. }
      rewrite Hvrm. rewrite Hc. reflexivity.
  - apply new_body_canonical.
Qed.

(* -------------------------------------------------------------------------- *)
(* Auxiliary lemmas for dead temporary-store elimination.                    *)
(* -------------------------------------------------------------------------- *)

(* If two environments agree outside an acceptor [a1], then a [PCG.seqfor]
   whose bodies preserve that agreement also produces equal results at every
   path outside [a1]. *)
Lemma PCG_seqfor_preserves_agreement_outside :
  forall d1 (a1 : PCG.acc d1) n (f : fin n -> PCG.comm) (rho eta : PCG.env),
    (forall q, ~ @PCG.in_acc d1 q a1 -> eta q = rho q) ->
    (forall i rho' eta' q,
       (forall q, ~ @PCG.in_acc d1 q a1 -> eta' q = rho' q) ->
       ~ @PCG.in_acc d1 q a1 ->
       f i eta' q = f i rho' q) ->
    forall q, ~ @PCG.in_acc d1 q a1 -> PCG.seqfor f eta q = PCG.seqfor f rho q.
Proof.
  induction n as [| n' IHn]; intros f rho eta Heta Hbody q Hq.
  - apply Heta. exact Hq.
  - rewrite seqfor_S. unfold PCG.seq.
    apply Hbody.
    + apply IHn; [exact Heta |].
      intros i rho' eta' q' H Hneq. apply Hbody. exact H. exact Hneq.
    + exact Hq.
Qed.

(* An assignment does not distinguish environments that differ only inside an
   acceptor [a1], provided the observed path is outside [a1]. *)
Lemma PCG_assign_outside_region_independent :
  forall d1 (a1 : PCG.acc d1) d2 (a2 : PCG.acc d2) (e2 : PCG.exp d2)
         (rho eta : PCG.env) (p : DE.path),
    (forall q, ~ @PCG.in_acc d1 q a1 -> eta q = rho q) ->
    ~ @PCG.in_acc d1 p a1 ->
    PCG.assign a2 e2 eta p = PCG.assign a2 e2 rho p.
Proof.
  intros d1 a1 d2 a2 e2 rho eta p H H0.
  revert rho eta p H H0.
  induction d2 as [| n m d2 IHd2]; simpl in *; intros rho eta p H H0.
  - unfold PCG.update. destruct (DE.path_eqb a2 p) eqn:E.
    + reflexivity.
    + apply H. exact H0.
  - apply PCG_seqfor_preserves_agreement_outside with (a1 := a1).
    + exact H.
    + intros i rho' eta' q H1 H2.
      apply (IHd2 (v_idx (PCG.acc_default d2) a2 i) (v_idx (PCG.exp_default d2) e2 i) rho' eta' q H1 H2).
    + exact H0.
Qed.

(* Elimination of a [new] whose continuation is a single assignment to an
   acceptor disjoint from the temporary, when the assigned expression does not
   depend on the temporary region. *)
Lemma eval_new_canonical_assign_independent :
  forall d (e1 : exp d) (d2 : data) (a2 : acc d2) (e2 : exp d2) (rho : PCG.env),
    @PCG.StructUndefined d (@PCG.acc' d (DE.Var "__tmp")) rho ->
    @exp_independent_of_acc d2 d e2 (@PCG.acc' d (DE.Var "__tmp")) ->
    (forall p, @PCG.in_acc d p (@PCG.acc' d (DE.Var "__tmp")) -> ~ @PCG.in_acc d2 p a2) ->
    eval (CG.new (fun tmp => let (w,v) := tmp in CG.seq (CG.assign (w,e1), CG.assign (a2,e2)))) rho =
    @PCG.assign d2 a2 (to_pcg_exp e2 rho) rho.
Proof.
  intros d e1 d2 a2 e2 rho Hundef Hindep Hdisj.
  rewrite eval_new_canonical_body.
  apply functional_extensionality. intro p.
  set (wtmp := @PCG.acc' d (DE.Var "__tmp")) in *.
  assert (Heta_agree : forall q, ~ @PCG.in_acc d q wtmp ->
    PCG.assign wtmp (to_pcg_exp e1 rho) rho q = rho q).
  { intros q Hq. apply PCG.assign_not_in_acc. exact Hq. }
  assert (He2_eq : to_pcg_exp e2 (PCG.assign wtmp (to_pcg_exp e1 rho) rho) = to_pcg_exp e2 rho).
  { apply exp_independent_of_acc_eval with (a := wtmp). exact Hindep. exact Heta_agree. }
  unfold PCG.seq. simpl.
  destruct (classic (@PCG.in_acc d p wtmp)) as [Hin | Hout].
  - (* Paths inside the temporary are removed on the left and untouched by [a2]. *)
    assert (Hlhs : PCG.vrm wtmp
      (PCG.assign a2 (to_pcg_exp e2 (PCG.assign wtmp (to_pcg_exp e1 rho) rho))
        (PCG.assign wtmp (to_pcg_exp e1 rho) rho)) p = None).
    { apply PCG.vrm_in_acc. exact Hin. }
    rewrite Hlhs.
    assert (Hrhs : PCG.assign a2 (to_pcg_exp e2 rho) rho p = rho p).
    { apply PCG.assign_not_in_acc. intro Hc. apply Hdisj in Hin. contradiction. }
    rewrite Hrhs. symmetry. apply (@PCG.StructUndefined_implies_None d wtmp rho p Hundef Hin).
  - (* Paths outside the temporary see the same expression value. *)
    assert (Hlhs : PCG.vrm wtmp
      (PCG.assign a2 (to_pcg_exp e2 (PCG.assign wtmp (to_pcg_exp e1 rho) rho))
        (PCG.assign wtmp (to_pcg_exp e1 rho) rho)) p =
      PCG.assign a2 (to_pcg_exp e2 (PCG.assign wtmp (to_pcg_exp e1 rho) rho))
        (PCG.assign wtmp (to_pcg_exp e1 rho) rho) p).
    { apply PCG.vrm_not_in_acc. exact Hout. }
    rewrite Hlhs. rewrite He2_eq.
    apply PCG_assign_outside_region_independent with (a1 := wtmp).
    + intros q Hq. apply PCG.assign_not_in_acc. exact Hq.
    + exact Hout.
Qed.

(* Dead-store elimination for a temporary that is disjoint from the real output
   of a [new].  If [a1] is initially undefined and [a2] writes nowhere inside
   [a1], then

     a1 := e1 ; a2 := e2 ; vrm a1   =   a2 := e2.

   This is used to show that an intermediate [new] buffer can be eliminated
   when its continuation is just a later assignment that does not read the
   temporary back. *)
Lemma PCG_dead_store_disjoint :
  forall d1 (a1 : PCG.acc d1) (e1 : PCG.exp d1)
         d2 (a2 : PCG.acc d2) (e2 : PCG.exp d2) (rho : PCG.env),
    PCG.StructUndefined a1 rho ->
    (forall p, @PCG.in_acc d1 p a1 -> ~ @PCG.in_acc d2 p a2) ->
    PCG.seq (PCG.assign a1 e1)
      (PCG.seq (PCG.assign a2 e2) (PCG.vrm a1)) rho =
    PCG.assign a2 e2 rho.
Proof.
  intros d1 a1 e1 d2 a2 e2 rho Hundef Hdisj.
  apply functional_extensionality. intro p.
  unfold PCG.seq.
  destruct (classic (PCG.in_acc p a1)) as [Hin | Hout].
  - (* Paths inside the temporary region are removed on the left and never
       touched by the output assignment. *)
    assert (Hvrm : PCG.vrm a1 (PCG.assign a2 e2 (PCG.assign a1 e1 rho)) p = None).
    { apply PCG.vrm_in_acc. exact Hin. }
    rewrite Hvrm.
    assert (Hnotin : ~ PCG.in_acc p a2) by (apply Hdisj; exact Hin).
    rewrite (PCG.assign_not_in_acc _ _ _ _ _ Hnotin).
    symmetry. apply (PCG.StructUndefined_implies_None _ a1); assumption.
  - (* Paths outside the temporary region see only the output assignment. *)
    assert (Hvrm : PCG.vrm a1 (PCG.assign a2 e2 (PCG.assign a1 e1 rho)) p =
                   PCG.assign a2 e2 (PCG.assign a1 e1 rho) p).
    { apply PCG.vrm_not_in_acc. exact Hout. }
    rewrite Hvrm.
    assert (HPres : PCG.assign a2 e2 (PCG.assign a1 e1 rho) p = PCG.assign a2 e2 rho p).
    { apply PCG_assign_outside_region_independent with (a1 := a1).
      - intros q Hq. apply PCG.assign_not_in_acc. exact Hq.
      - exact Hout. }
    rewrite HPres. reflexivity.
Qed.

(* If an acceptor [a2] writes nowhere inside [a1], then assignment to [a2]
   preserves the fact that [a1] is undefined. *)
Lemma PCG_assign_preserves_StructUndefined :
  forall d1 (a1 : PCG.acc d1) d2 (a2 : PCG.acc d2) (e : PCG.exp d2) (rho : PCG.env),
    PCG.StructUndefined a1 rho ->
    (forall p, PCG.in_acc p a1 -> ~ PCG.in_acc p a2) ->
    PCG.StructUndefined a1 (PCG.assign a2 e rho).
Proof.
  intros d1 a1 d2 a2 e rho Hundef Hdisj.
  generalize dependent a1.
  induction d1 as [| n m d1 IHd1]; simpl; intros a1 Hundef Hdisj.
  - rewrite (PCG.assign_not_in_acc _ _ _ _ _ (Hdisj a1 eq_refl)). exact Hundef.
  - intros i. apply IHd1.
    + apply Hundef.
    + intros p Hp. apply Hdisj. exists i. exact Hp.
Qed.

(* On an environment where [a] is undefined, assigning to [a] and then
   removing [a] is the identity. *)
Lemma PCG_assign_vrm_identity :
  forall d (a : PCG.acc d) (e : PCG.exp d) (rho : PCG.env),
    PCG.StructUndefined a rho ->
    PCG.seq (PCG.assign a e) (PCG.vrm a) rho = rho.
Proof.
  intros d a e rho Hundef.
  apply functional_extensionality. intro p.
  unfold PCG.seq.
  destruct (classic (PCG.in_acc p a)) as [Hin | Hout].
  - rewrite (PCG.vrm_in_acc _ _ _ _ Hin).
    symmetry. apply (PCG.StructUndefined_implies_None _ a); assumption.
  - rewrite (PCG.vrm_not_in_acc _ _ _ _ Hout).
    rewrite (PCG.assign_not_in_acc _ _ _ _ _ Hout).
    reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Auxiliary definitions and lemmas for accumulator-loop proofs.             *)
(* -------------------------------------------------------------------------- *)

Definition wtmp_path : DE.path := DE.Var "__tmp".
Definition wtmp_acc : PCG.acc num := PCG.acc' wtmp_path.

Lemma vwt_tmp_path : @CG.vwt num "__tmp" = wtmp_path.
Proof. unfold CG.vwt, wtmp_path. reflexivity. Qed.

Lemma update_vwt_tmp : forall (rho' : PCG.env) (x : PCG.exp num),
  PCG.update rho' (@CG.vwt num "__tmp") x = PCG.update rho' wtmp_path x.
Proof. intros. unfold CG.vwt, wtmp_path. reflexivity. Qed.

Definition value_at (rho : PCG.env) (p : DE.path) : R :=
  match rho p with Some r => r | None => R0 end.

Lemma value_at_update_same : forall rho p x,
  value_at (PCG.update rho p x) p = x.
Proof. intros. unfold value_at. rewrite PCG.update_eq. reflexivity. Qed.

Lemma value_at_env_eq : forall rho1 rho2 p,
  rho1 p = rho2 p -> value_at rho1 p = value_at rho2 p.
Proof. intros. unfold value_at. rewrite H. reflexivity. Qed.

Lemma update_if_distribute : forall rho p (b : bool) x y,
  PCG.update rho p (if b then x else y) =
  if b then PCG.update rho p x else PCG.update rho p y.
Proof. intros rho p b x y. destruct b; reflexivity. Qed.

Lemma remove_eq : forall rho x, PCG.remove rho x x = None.
Proof. intros. unfold PCG.remove. rewrite path_eqb_refl. reflexivity. Qed.

Lemma remove_neq : forall rho x p, x <> p -> PCG.remove rho x p = rho p.
Proof.
  intros. unfold PCG.remove. destruct (path_eqb x p) eqn:E.
  - apply path_eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma to_pcg_exp_zero : forall rho,
  to_pcg_exp CD.zero rho = R0.
Proof.
  intros rho. cbv [to_pcg_exp CD.zero DE.eval_rexp]. simpl. reflexivity.
Qed.

Lemma to_pcg_exp_add : forall x y rho,
  to_pcg_exp (CD.add x y) rho = Rplus (to_pcg_exp x rho) (to_pcg_exp y rho).
Proof.
  intros x y rho. cbv [to_pcg_exp CD.add DE.eval_rexp]. simpl. reflexivity.
Qed.

Lemma to_pcg_exp_idx : forall n d (e : DE.exp (ary '{n} d)) (i : fin n) rho,
  to_pcg_exp (DE.idx e i) rho = PCG.idx (to_pcg_exp e rho) i.
Proof.
  intros n d e i rho. unfold DE.idx, PCG.idx, to_pcg_exp. simpl.
  rewrite V.v_idx_mk_vec. reflexivity.
Qed.

Lemma to_pcg_exp_REvar_tmp : forall rho,
  to_pcg_exp (CG.vrd "__tmp" : exp num) rho = value_at rho wtmp_path.
Proof.
  intros rho. unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
  unfold value_at, wtmp_path. reflexivity.
Qed.

Lemma to_pcg_exp_REvar_tmp' : forall rho,
  to_pcg_exp (CG.vrd "__tmp") rho = (value_at rho wtmp_path : PCG.exp num).
Proof.
  intros rho. unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
  unfold value_at, wtmp_path. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* String and [writeNat] facts needed to reason about the indexed temporary
   names [s ++ "[" ++ writeNat i ++ "]"] produced by the array branches of
   [CG.vrd]/[CG.vwt].                                                        *)
(* -------------------------------------------------------------------------- *)

(* Small string facts that the Rocq 9.0 String library no longer provides. *)
Lemma append_empty_r : forall s : string, (s ++ "" = s)%string.
Proof.
  induction s as [|c s' IH]; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma append_assoc_str : forall s1 s2 s3 : string,
  ((s1 ++ s2) ++ s3 = s1 ++ s2 ++ s3)%string.
Proof.
  induction s1 as [|c s1' IH]; intros s2 s3; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

Lemma append_length_str : forall s1 s2 : string,
  String.length (s1 ++ s2) = (String.length s1 + String.length s2)%nat.
Proof.
  induction s1 as [|c s1' IH]; intro s2; simpl; [reflexivity | rewrite IH; reflexivity].
Qed.

(* Every character produced by [writeNat] is a decimal digit, so ["]"] can
   never occur inside [writeNat n]. *)
Definition is_digit (c : ascii) : bool :=
  (48 <=? Ascii.nat_of_ascii c)%nat && (Ascii.nat_of_ascii c <=? 57)%nat.

Fixpoint all_digits (s : string) : Prop :=
  match s with
  | EmptyString => True
  | String c s' => is_digit c = true /\ all_digits s'
  end.

Lemma natToDigit_is_digit : forall n, is_digit (natToDigit n) = true.
Proof.
  intro n.
  destruct n as [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | m ] ] ] ] ] ] ] ] ] ] ]; reflexivity.
Qed.

Lemma writeNatAux_all_digits : forall time n acc,
  all_digits acc -> all_digits (writeNatAux time n acc).
Proof.
  induction time; intros n acc Hacc; cbn [writeNatAux].
  - split; [apply natToDigit_is_digit | exact Hacc].
  - destruct (n / 10)%nat.
    + split; [apply natToDigit_is_digit | exact Hacc].
    + apply IHtime. split; [apply natToDigit_is_digit | exact Hacc].
Qed.

Lemma writeNat_all_digits : forall n, all_digits (writeNat n).
Proof.
  intro n. unfold writeNat. apply writeNatAux_all_digits. exact I.
Qed.

Lemma digit_not_rbrack : forall c, is_digit c = true -> c <> "]"%char.
Proof.
  intros c Hd Heq. subst c. discriminate Hd.
Qed.

Lemma digits_eq_of_append : forall wa wb u v,
  all_digits wa -> all_digits wb ->
  (wa ++ "]" ++ u = wb ++ "]" ++ v)%string -> wa = wb.
Proof.
  induction wa as [|c wa' IH]; intros wb u v Ha Hb Heq.
  - destruct wb as [|c' wb']; [reflexivity|].
    simpl in Heq. injection Heq as Hc _. destruct Hb as [Hd _].
    exfalso. apply (digit_not_rbrack Hd). symmetry. exact Hc.
  - destruct wb as [|c' wb'].
    + simpl in Heq. injection Heq as Hc _. destruct Ha as [Hd _].
      exfalso. apply (digit_not_rbrack Hd). exact Hc.
    + simpl in Heq. injection Heq as Hc Hrest.
      destruct Ha as [Hd Ha']. destruct Hb as [_ Hb'].
      rewrite (IH wb' u v Ha' Hb' Hrest). rewrite Hc. reflexivity.
Qed.

Lemma append_cancel_l : forall s1 s2 s3 : string,
  (s1 ++ s2 = s1 ++ s3)%string -> s2 = s3.
Proof.
  induction s1 as [|c s1' IH]; intros s2 s3 H.
  - exact H.
  - simpl in H. injection H as H'. apply IH. exact H'.
Qed.

(* The digit property only gives cancellation up to [writeNat]; injectivity
   itself is proved below via a decimal value function on strings. *)
Lemma tmp_idx_neq_pre : forall (s : string) (a b : nat),
  writeNat a <> writeNat b ->
  forall u v : string,
  (s ++ "[" ++ writeNat a ++ "]" ++ u <> s ++ "[" ++ writeNat b ++ "]" ++ v)%string.
Proof.
  intros s a b Hab u v Heq.
  apply Hab.
  apply append_cancel_l in Heq.
  apply append_cancel_l in Heq.
  apply (digits_eq_of_append _ _ _ _ (writeNat_all_digits a) (writeNat_all_digits b) Heq).
Qed.

(* Decimal value of a digit string (most significant digit first). *)
Definition digit_val (c : ascii) : nat := (Ascii.nat_of_ascii c - 48)%nat.

Fixpoint sval (s : string) : nat :=
  match s with
  | EmptyString => 0
  | String c s' => (digit_val c * 10 ^ String.length s' + sval s')%nat
  end.

Lemma natToDigit_val : forall n, (n < 10)%nat -> digit_val (natToDigit n) = n.
Proof.
  intros n Hn.
  destruct n as [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | [ | m ] ] ] ] ] ] ] ] ] ] ]; try reflexivity; lia.
Qed.

Lemma sval_cons : forall c s,
  sval (String c s) = (digit_val c * 10 ^ String.length s + sval s)%nat.
Proof. reflexivity. Qed.

Lemma writeNatAux_sval : forall time n acc,
  (n < 10 ^ time)%nat ->
  sval (writeNatAux time n acc) = (n * 10 ^ String.length acc + sval acc)%nat.
Proof.
  induction time; intros n acc Hn; cbn [writeNatAux].
  - assert (n = 0) by (simpl in Hn; lia). subst n.
    rewrite sval_cons. simpl. reflexivity.
  - destruct (n / 10)%nat eqn:E.
    + assert (Hmod : (n mod 10 < 10)%nat) by (apply Nat.mod_upper_bound; lia).
      pose proof (Nat.div_mod n 10 ltac:(lia)) as Hdm. rewrite E in Hdm.
      rewrite Nat.mul_0_r, Nat.add_0_l in Hdm.
      rewrite sval_cons. rewrite natToDigit_val by exact Hmod. rewrite <- Hdm. reflexivity.
    + assert (Hmod : (n mod 10 < 10)%nat) by (apply Nat.mod_upper_bound; lia).
      pose proof (Nat.div_mod n 10 ltac:(lia)) as Hdm. rewrite E in Hdm.
      assert (Hbound : (S n0 < 10 ^ time)%nat) by (simpl in Hn; lia).
      rewrite (IHtime (S n0) _ Hbound).
      rewrite sval_cons.
      assert (Hlen : String.length (String (natToDigit (n mod 10)) acc)
                     = S (String.length acc)) by reflexivity.
      rewrite Hlen. rewrite Nat.pow_succ_r'.
      rewrite natToDigit_val by exact Hmod.
      nia.
Qed.

Lemma pow10_gt : forall n, (n < 10 ^ n)%nat.
Proof.
  induction n; simpl; lia.
Qed.

Lemma writeNat_sval : forall n, sval (writeNat n) = n.
Proof.
  intro n. unfold writeNat.
  rewrite writeNatAux_sval by apply pow10_gt.
  simpl. lia.
Qed.

(* Injectivity of the standard decimal printing; proved, not axiomatised. *)
Lemma writeNat_inj : forall m n, writeNat m = writeNat n -> m = n.
Proof.
  intros m n H.
  rewrite <- (writeNat_sval m). rewrite <- (writeNat_sval n).
  rewrite H. reflexivity.
Qed.

(* Indexed temporary names at distinct indices never clash, even under
   arbitrary further bracket suffixes. *)
Lemma tmp_idx_neq : forall (s : string) (a b : nat),
  (a <> b)%nat ->
  forall u v : string,
  (s ++ "[" ++ writeNat a ++ "]" ++ u <> s ++ "[" ++ writeNat b ++ "]" ++ v)%string.
Proof.
  intros s a b Hab u v.
  apply tmp_idx_neq_pre.
  intro Hw. apply writeNat_inj in Hw. contradiction.
Qed.

(* Left-associated variant: the bracketed prefix as a whole differs. *)
Lemma tmp_idx_neq2 : forall (s : string) (a b : nat),
  (a <> b)%nat ->
  forall u v : string,
  ((s ++ "[" ++ writeNat a ++ "]") ++ u <> (s ++ "[" ++ writeNat b ++ "]") ++ v)%string.
Proof.
  intros s a b Hab u v Hw.
  apply Hab. apply writeNat_inj.
  rewrite !append_assoc_str in Hw.
  apply append_cancel_l in Hw.
  apply append_cancel_l in Hw.
  exact (digits_eq_of_append _ _ _ _ (writeNat_all_digits a) (writeNat_all_digits b) Hw).
Qed.

(* An indexed name always ends in ["]"], so it has length at least 2 and can
   never equal a one-character constant name such as ["0"] or ["1"]. *)
Lemma indexed_name_neq1 : forall (s : string) (i : nat) (c : string),
  (String.length c = 1)%nat -> (s ++ "[" ++ writeNat i ++ "]" <> c)%string.
Proof.
  intros s i c Hc Heq.
  assert (Hlen : (String.length (s ++ "[" ++ writeNat i ++ "]") = 1)%nat)
    by (rewrite Heq; exact Hc).
  rewrite !append_length_str in Hlen.
  change (String.length "[")%string with 1%nat in Hlen.
  change (String.length "]")%string with 1%nat in Hlen.
  lia.
Qed.

Lemma fin2nat_ltS : forall n, fin2nat (ltS n) = n.
Proof. reflexivity. Qed.

Lemma indexed_name_neq_0 : forall (s : string) (i : nat),
  (s ++ "[" ++ writeNat i ++ "]" <> "0")%string.
Proof. intros. apply (indexed_name_neq1 (c := "0"%string) s i eq_refl). Qed.

Lemma indexed_name_neq_1 : forall (s : string) (i : nat),
  (s ++ "[" ++ writeNat i ++ "]" <> "1")%string.
Proof. intros. apply (indexed_name_neq1 (c := "1"%string) s i eq_refl). Qed.

(* -------------------------------------------------------------------------- *)
(* One-step unfolding lemmas for the simpl-never definitions.                *)
(* -------------------------------------------------------------------------- *)

Lemma vrd_num : forall s,
  @CG.vrd num s =
  (if String.eqb s "0" then DE.REconst R0 "0"
   else if String.eqb s "1" then DE.REconst R1 "1"
   else DE.REvar s)%string.
Proof. reflexivity. Qed.

Lemma vrd_ary : forall n (f : fle n) d s,
  @CG.vrd (ary f d) s =
  V.mk_vec (fun i : fin (fle2nat f) =>
    @CG.vrd d (s ++ "[" ++ writeNat (fin2nat i) ++ "]")%string).
Proof. reflexivity. Qed.

Lemma vwt_num : forall s, @CG.vwt num s = DE.Var s.
Proof. reflexivity. Qed.

Lemma vwt_ary : forall n (f : fle n) d s,
  @CG.vwt (ary f d) s =
  V.mk_vec (fun i : fin (fle2nat f) =>
    @CG.vwt d (s ++ "[" ++ writeNat (fin2nat i) ++ "]")%string).
Proof. reflexivity. Qed.

Lemma PCG_assign_num : forall (a : PCG.acc num) (e : PCG.exp num) rho,
  PCG.assign a e rho = PCG.update rho a e.
Proof. reflexivity. Qed.

Lemma PCG_assign_ary : forall n (f : fle n) d (a : PCG.acc (ary f d))
                            (e : PCG.exp (ary f d)) rho,
  PCG.assign a e rho =
  PCG.seqfor (fun i : fin (fle2nat f) =>
    PCG.assign (PCG.idxAcc a i) (PCG.idx e i)) rho.
Proof. reflexivity. Qed.

Lemma to_pcg_exp_ary : forall n (f : fle n) d (v : DE.exp (ary f d)) rho,
  to_pcg_exp v rho =
  V.mk_vec (fun i : fin (fle2nat f) =>
    to_pcg_exp (V.v_nth (DE.exp_default d) v (fin2nat i)) rho).
Proof. reflexivity. Qed.

Lemma PCG_idxAcc_mk_vec : forall n (f : fle n) d
    (g : fin (fle2nat f) -> DE.acc d) (i : fin (fle2nat f)),
  PCG.idxAcc (V.mk_vec g) i = g i.
Proof.
  intros n f d g i. unfold PCG.idxAcc. apply (V.v_idx_mk_vec i g (PCG.acc_default d)).
Qed.

Lemma PCG_idx_mk_vec : forall n (f : fle n) d
    (g : fin (fle2nat f) -> PCG.exp d) (i : fin (fle2nat f)),
  PCG.idx (V.mk_vec g) i = g i.
Proof.
  intros n f d g i. unfold PCG.idx. apply (V.v_idx_mk_vec i g (PCG.exp_default d)).
Qed.

(* Assigning to a vector of acceptors is the pointwise sequential loop.
   Stated as a single rewrite rule because plain [rewrite] does not match
   under the [seqfor] binder. *)
Lemma PCG_assign_mk_vec : forall n (f : fle n) d
    (g : fin (fle2nat f) -> DE.acc d) (v : PCG.exp (ary f d)) (rho : PCG.env),
  @PCG.assign (ary f d) (V.mk_vec g) v rho =
  PCG.seqfor (fun i : fin (fle2nat f) => @PCG.assign d (g i) (PCG.idx v i)) rho.
Proof.
  intros n f d g v rho.
  rewrite PCG_assign_ary.
  assert (H : PCG.seqfor (fun i : fin (fle2nat f) =>
                @PCG.assign d (@PCG.idxAcc (fle2nat f) d (V.mk_vec g) i) (PCG.idx v i)) =
              PCG.seqfor (fun i : fin (fle2nat f) =>
                @PCG.assign d (g i) (PCG.idx v i))).
  { apply PCG.seqfor_extensionality. intro i.
    rewrite PCG_idxAcc_mk_vec. reflexivity. }
  rewrite H. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Read/write lemmas for the indexed temporary region.                       *)
(* -------------------------------------------------------------------------- *)

(* Every leaf path of [CG.vwt d s] is a plain variable whose name starts
   with [s]. *)
Lemma in_acc_vwt : forall d (p : DE.path) (s : string),
  @PCG.in_acc d p (@CG.vwt d s) ->
  exists u : string, p = DE.Var (s ++ u)%string.
Proof.
  induction d as [| n f d' IHd]; intros p s Hin.
  - rewrite vwt_num in Hin. simpl in Hin.
    exists ""%string. rewrite append_empty_r. symmetry. exact Hin.
  - rewrite vwt_ary in Hin. simpl in Hin.
    destruct Hin as [i Hi].
    rewrite PCG_idxAcc_mk_vec in Hi.
    destruct (IHd _ _ Hi) as [u Heq].
    exists (("[" ++ writeNat (fin2nat i) ++ "]") ++ u)%string.
    rewrite Heq. rewrite append_assoc_str. reflexivity.
Qed.

(* A variable read tree [CG.vrd d t] never reads [Var q] when every extension
   of [t] differs from [q]. *)
Lemma exp_indep_vrd_Var : forall d (t q : string),
  (forall v : string, (t ++ v <> q)%string) ->
  @exp_independent_of_path d (@CG.vrd d t) (DE.Var q).
Proof.
  induction d as [| n f d' IHd]; intros t q Hdiv.
  - rewrite vrd_num. simpl.
    destruct (String.eqb t "0") eqn:E0; [exact I|].
    destruct (String.eqb t "1") eqn:E1; [exact I|].
    intro Heq. injection Heq as Heq.
    apply (Hdiv ""%string). rewrite append_empty_r. exact Heq.
  - rewrite vrd_ary. simpl. intro i.
    rewrite V.v_nth_mk_vec with (H := fin_proof i).
    rewrite nat2fin_fin2nat.
    apply IHd. intros w Hw.
    apply (Hdiv (("[" ++ writeNat (fin2nat i) ++ "]") ++ w)%string).
    rewrite append_assoc_str in Hw. exact Hw.
Qed.

(* Writing one indexed temporary does not affect reading another one whose
   name differs under every bracket suffix. *)
Lemma vrd_after_other_vwt : forall d (si t : string),
  (forall u v : string, (si ++ u <> t ++ v)%string) ->
  forall (v : PCG.exp d) (rho : PCG.env),
    to_pcg_exp (@CG.vrd d t) (PCG.assign (@CG.vwt d si) v rho) =
    to_pcg_exp (@CG.vrd d t) rho.
Proof.
  intros d si t Hdiv v rho.
  apply (@exp_independent_of_acc_eval d d (@CG.vrd d t) (@CG.vwt d si)).
  - intros p Hp. destruct (in_acc_vwt _ _ _ Hp) as [u Heq]. subst p.
    apply exp_indep_vrd_Var. intros w Htw.
    apply (Hdiv u w). symmetry. exact Htw.
  - intros q Hq. apply PCG.assign_not_in_acc. exact Hq.
Qed.

(* Reading [CG.vrd d s] after assigning to [CG.vwt d s] yields the assigned
   value, for any data type [d] and any name [s] that is not a constant
   literal name. *)
Lemma vrd_after_own_vwt : forall d (s : string),
  (s <> "0")%string -> (s <> "1")%string ->
  forall (v : PCG.exp d) (rho : PCG.env),
    to_pcg_exp (@CG.vrd d s) (PCG.assign (@CG.vwt d s) v rho) = v.
Proof.
  induction d as [| n f d' IHd]; intros s Hs0 Hs1 v rho.
  - rewrite vrd_num, vwt_num, PCG_assign_num.
    rewrite (proj2 (String.eqb_neq s "0") Hs0).
    rewrite (proj2 (String.eqb_neq s "1") Hs1).
    rewrite to_pcg_exp_REvar, PCG.update_eq. reflexivity.
  - rewrite vrd_ary, vwt_ary, to_pcg_exp_ary, PCG_assign_mk_vec.
    rewrite <- (V.mk_vec_bij_fin (fle2nat f) (PCG.exp_default d') v) at 1.
    apply V.mk_vec_ext. intro j. cbn beta.
    rewrite V.v_nth_mk_vec with (H := fin_proof j).
    rewrite nat2fin_fin2nat.
    (* Element [j] is written exactly once, by iteration [j] of the seqfor;
       all other iterations write different indexed names. *)
    assert (Hinner : forall n' (j : fin n') (vs : fin n' -> PCG.exp d') (rho' : PCG.env),
      to_pcg_exp (@CG.vrd d' (s ++ "[" ++ writeNat (fin2nat j) ++ "]")%string)
        (PCG.seqfor (fun i : fin n' =>
          @PCG.assign d' (@CG.vwt d' (s ++ "[" ++ writeNat (fin2nat i) ++ "]")%string)
            (vs i)) rho')
      = vs j).
    { induction n' as [| n'' IHn']; intros jj vs rho'.
      - destruct jj as [k Hk]. exfalso. lia.
      - rewrite seqfor_S. unfold PCG.seq. cbn beta.
        destruct (fin_case jj) as [[j' Hj] | Hj]; subst jj.
        + (* j = FS[j']: the last iteration writes a different element *)
          rewrite fin2nat_fin2finS.
          rewrite (vrd_after_other_vwt d'
                    (s ++ "[" ++ writeNat (fin2nat (ltS n'')) ++ "]")%string
                    (s ++ "[" ++ writeNat (fin2nat j') ++ "]")%string).
          * apply (IHn' j' (fun i => vs (fin2finS i)) rho').
          * intros u w. rewrite !append_assoc_str. apply tmp_idx_neq.
            rewrite fin2nat_ltS. pose proof (fin_correct j') as Hlt. lia.
        + (* j = last: the last iteration writes exactly this element *)
          change (nat2fin (Nat.lt_succ_diag_r n'')) with (ltS n'').
          apply (IHd _
                   (indexed_name_neq_0 _ _)
                   (indexed_name_neq_1 _ _)). }
    apply (Hinner (fle2nat f) j (fun i => PCG.idx v i) rho).
Qed.

(* Reading [CG.vrd "__tmp"] after assigning to [CG.vwt "__tmp"] yields the
   assigned value, for any data type [d].  This generalizes the scalar fact
   [value_at_update_same]. *)
Lemma to_pcg_exp_vrd_after_vwt :
  forall d (e : DE.exp d) (rho : PCG.env),
    to_pcg_exp (@CG.vrd d "__tmp")
      (PCG.assign (@CG.vwt d "__tmp") (to_pcg_exp e rho) rho) =
    to_pcg_exp e rho.
Proof.
  intros d e rho. apply vrd_after_own_vwt; discriminate.
Qed.

(* If each iteration of a seqfor produces the same value at [p] in both
   environments whenever it writes [p], and preserves [p] otherwise, then
   the whole runs agree at [p] (provided some iteration writes [p]). *)
Lemma seqfor_agree_at_region :
  forall n (F : fin n -> PCG.comm) (rho1 rho2 : PCG.env) (p : path) (P : fin n -> Prop),
    (exists i, P i) ->
    (forall i r1 r2, P i -> F i r1 p = F i r2 p) ->
    (forall i r, ~ P i -> F i r p = r p) ->
    PCG.seqfor F rho1 p = PCG.seqfor F rho2 p.
Proof.
  induction n as [| n' IHn]; intros F rho1 rho2 p P Hex Hin Hout.
  - destruct Hex as [i _]. destruct i as [k Hk]. exfalso. lia.
  - rewrite seqfor_S. unfold PCG.seq.
    destruct (classic (P (ltS n'))) as [HPlast | HPlast].
    + apply Hin. exact HPlast.
    + rewrite !(Hout (ltS n')) by exact HPlast.
      apply (IHn _ _ _ _ (fun i => P (fin2finS i))).
      * destruct Hex as [i Hi]. destruct (fin_case i) as [[i' ->] | ->].
        -- exists i'. exact Hi.
        -- contradiction.
      * intros i r1 r2 HP. apply Hin. exact HP.
      * intros i r HNP. apply Hout. exact HNP.
Qed.

(* Assigning to an acceptor [a] at a path inside [a] does not depend on the
   rest of the environment: the result at [p] is fully determined by the
   assigned expression. *)
Lemma assign_in_acc_independent_of_env :
  forall d (a : acc d) (e : PCG.exp d) (rho1 rho2 : PCG.env) (p : path),
    @PCG.in_acc d p a ->
    PCG.assign a e rho1 p = PCG.assign a e rho2 p.
Proof.
  induction d as [| n f d' IHd]; simpl; intros a e rho1 rho2 p Hin.
  - subst. rewrite !PCG.update_eq. reflexivity.
  - destruct Hin as [i Hi].
    apply seqfor_agree_at_region with (P := fun i0 => @PCG.in_acc d' p (PCG.idxAcc a i0)).
    + exists i. exact Hi.
    + intros i0 r1 r2 Hin0. apply (IHd (PCG.idxAcc a i0) (PCG.idx e i0) r1 r2 p Hin0).
    + intros i0 r Hout0. apply PCG.assign_not_in_acc. exact Hout0.
Qed.

Lemma to_pcg_exp_REvar_tmp_ : forall rho,
  to_pcg_exp (CG.vrd "__tmp_") rho = (value_at rho (DE.Var "__tmp_") : PCG.exp num).
Proof.
  intros rho. unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
  unfold value_at. reflexivity.
Qed.

Lemma PCG_assign_vwt_tmp : forall (e : DE.exp num) (rho : PCG.env),
  PCG.assign (CG.vwt "__tmp") (to_pcg_exp e rho) rho =
  PCG.update rho wtmp_path (to_pcg_exp e rho).
Proof.
  intros. simpl. unfold CG.vwt, wtmp_path. reflexivity.
Qed.

Lemma idx_fin2finS_eq : forall n d (e : DE.exp (ary '{S n} d)) (i : fin n),
  DE.idx e (FS[i]) = DE.idx (fst e) i.
Proof.
  intros n d e i. unfold DE.idx, V.v_idx.
  assert (He : e = (fst e, snd e)) by apply surjective_pairing.
  rewrite He. apply V.v_nth_fin2finS0.
Qed.

Lemma idx_last_eq : forall n d (e : DE.exp (ary '{S n} d)),
  DE.idx e (ltS n) = snd e.
Proof.
  intros n d e. unfold DE.idx, V.v_idx.
  assert (He : e = (fst e, snd e)) by apply surjective_pairing.
  rewrite He. apply V.v_nth_last.
Qed.

Lemma sum_Sn : forall n (e : DE.exp (ary '{S n} num)),
  CD.sum e = CD.add (DE.idx e (ltS n)) (CD.sum (fst e)).
Proof.
  intros n e. unfold CD.sum.
  assert (He : e = (fst e, snd e)) by apply surjective_pairing.
  rewrite He. simpl. rewrite idx_last_eq. reflexivity.
Qed.

Lemma exp_independent_of_tmp_eval :
  forall d (e : DE.exp d) (rho1 rho2 : PCG.env),
    @exp_independent_of_acc d num e wtmp_acc ->
    (forall q, q <> wtmp_path -> rho1 q = rho2 q) ->
    to_pcg_exp e rho1 = to_pcg_exp e rho2.
Proof.
  intros d e rho1 rho2 Hindep Hagree.
  apply @exp_independent_of_acc_eval with (d' := num) (a := wtmp_acc).
  - exact Hindep.
  - intros q Hq. apply Hagree. intro Hc. apply Hq. simpl. auto.
Qed.

(* If a seqfor body only updates [wtmp_path], then every other path is preserved. *)
Lemma seqfor_preserves_outside_tmp :
  forall n (body : fin n -> PCG.comm) (rho : PCG.env) (p : DE.path),
    p <> wtmp_path ->
    (forall i rho', body i rho' p = rho' p) ->
    PCG.seqfor body rho p = rho p.
Proof.
  intros n body rho p Hp Hbody. apply PCG.seqfor_pointwise. auto.
Qed.

Lemma sum_body_outside :
  forall n (e : DE.exp (ary '{n} num)) (i : fin n) (rho' : PCG.env) (p : DE.path),
    p <> wtmp_path ->
    PCG.update rho' wtmp_path (Rplus (to_pcg_exp (DE.idx e i) rho') (value_at rho' wtmp_path)) p = rho' p.
Proof.
  intros n e i rho' p Hp. apply PCG.update_neq. intro Hc. apply Hp. auto.
Qed.

(* Independence of an array implies independence of every element. *)
Lemma v_nth_fin2finS_eq : forall n (A : Set) (x0 : A) (v : vector A (S n)) (i : fin n),
  V.v_nth x0 v (fin2nat (FS[i])) = V.v_nth x0 (fst v) (fin2nat i).
Proof.
  intros n A x0 v i. assert (He : v = (fst v, snd v)) by apply surjective_pairing.
  rewrite He. apply V.v_nth_fin2finS0.
Qed.

Lemma exp_independent_path_idx :
  forall n d (e : DE.exp (ary '{n} d)) (p : DE.path) (i : fin n),
    exp_independent_of_path e p ->
    exp_independent_of_path (DE.idx e i) p.
Proof.
  intros n d e p i Hindep.
  unfold DE.idx. apply Hindep.
Qed.

(* Independence of an array from [wtmp_acc] implies independence of [fst e]. *)
Lemma exp_independent_fst :
  forall n d (e : DE.exp (ary '{S n} d)),
    @exp_independent_of_acc (ary '{S n} d) num e wtmp_acc ->
    @exp_independent_of_acc (ary '{n} d) num (fst e) wtmp_acc.
Proof.
  intros n d e Hindep p Hp i.
  rewrite <- v_nth_fin2finS_eq.
  apply exp_independent_path_idx with (i := FS[i]).
  apply Hindep. exact Hp.
Qed.

(* Generalized [exp_independent_fst] for an arbitrary acceptor type [d']. *)
Lemma exp_independent_fst_gen :
  forall n d d' (e : DE.exp (ary '{S n} d)) (a : acc d'),
    @exp_independent_of_acc (ary '{S n} d) d' e a ->
    @exp_independent_of_acc (ary '{n} d) d' (fst e) a.
Proof.
  intros n d d' e a Hindep p Hp i.
  rewrite <- v_nth_fin2finS_eq.
  apply exp_independent_path_idx with (i := FS[i]).
  apply Hindep. exact Hp.
Qed.

(* Scalar addition preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_add :
  forall d' (x y : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc y a ->
    exp_independent_of_acc (CD.add x y) a.
Proof.
  intros d' x y a Hx Hy p Hp. simpl. split.
  - apply Hx. exact Hp.
  - apply Hy. exact Hp.
Qed.

(* Scalar multiplication preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_mul :
  forall d' (x y : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc y a ->
    exp_independent_of_acc (CD.mul x y) a.
Proof.
  intros d' x y a Hx Hy p Hp. simpl. split.
  - apply Hx. exact Hp.
  - apply Hy. exact Hp.
Qed.

(* Scalar subtraction preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_sub :
  forall d' (x y : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc y a ->
    exp_independent_of_acc (CD.sub x y) a.
Proof.
  intros d' x y a Hx Hy p Hp. simpl. split.
  - apply Hx. exact Hp.
  - apply Hy. exact Hp.
Qed.

(* Scalar division preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_div :
  forall d' (x y : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc y a ->
    exp_independent_of_acc (CD.div x y) a.
Proof.
  intros d' x y a Hx Hy p Hp. simpl. split.
  - apply Hx. exact Hp.
  - apply Hy. exact Hp.
Qed.

(* Scalar square root preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_sqrt :
  forall d' (x : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc (CD.sqrt x) a.
Proof.
  intros d' x a Hx p Hp. simpl. apply Hx. exact Hp.
Qed.

(* A statically-chosen conditional preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_if :
  forall d' (a : acc d') (b : bexp) (e1 e2 : exp num),
    (bexp2bool b = true -> exp_independent_of_acc e1 a) ->
    (bexp2bool b = false -> exp_independent_of_acc e2 a) ->
    exp_independent_of_acc (if bexp2bool b then e1 else e2) a.
Proof.
  intros. destruct (bexp2bool b); auto.
Qed.

(* The scalar constant [zero] is independent of any acceptor. *)
Lemma exp_independent_of_acc_zero :
  forall d' (a : acc d'), exp_independent_of_acc CD.zero a.
Proof. intros d' a p Hp. exact I. Qed.

(* Path-level scalar addition preserves independence. *)
Lemma exp_independent_path_add :
  forall (x y : exp num) (p : DE.path),
    exp_independent_of_path x p ->
    exp_independent_of_path y p ->
    exp_independent_of_path (CD.add x y) p.
Proof. intros x y p Hx Hy. simpl. split; assumption. Qed.

(* Path-level scalar multiplication preserves independence. *)
Lemma exp_independent_path_mul :
  forall (x y : exp num) (p : DE.path),
    exp_independent_of_path x p ->
    exp_independent_of_path y p ->
    exp_independent_of_path (CD.mul x y) p.
Proof. intros x y p Hx Hy. simpl. split; assumption. Qed.

(* [v_reduce] over a [mk_vec] of length [S n] splits into the last element
   and the prefix. *)
Lemma v_reduce_mk_vec_Sn :
  forall n' (A B : Set) (f : A -> B -> B) (init : B) (g : fin (S n') -> A),
    V.v_reduce f init (V.mk_vec g) =
    f (g (ltS n')) (V.v_reduce f init (V.mk_vec (fun i : fin n' => g (fin2finS i)))).
Proof.
  intros. rewrite (V.mk_vec_Sn _). apply V.v_reduce_Sn.
Qed.

(* [sum] preserves path independence. *)
Lemma exp_independent_path_sum :
  forall n (e : exp (ary '{n} num)) (p : DE.path),
    (forall i, exp_independent_of_path (DE.idx e i) p) ->
    exp_independent_of_path (CD.sum e) p.
Proof.
  intros n e p Hindep.
  unfold CD.sum.
  rewrite <- (V.mk_vec_bij_fin _ (DE.exp_default num) e) at 1.
  change (V.mk_vec (V.v_nth (DE.exp_default num) e)) with (V.mk_vec (DE.idx e)).
  induction n as [| n' IHn].
  - simpl. auto.
  - assert (Hreduce : v_reduce CD.add CD.zero (V.mk_vec (DE.idx e)) =
      CD.add (DE.idx e (ltS n')) (v_reduce CD.add CD.zero (V.mk_vec (fun i : fin n' => DE.idx e (fin2finS i))))).
    { apply v_reduce_mk_vec_Sn. }
    cbn [fle2nat fle_self] in *.
    rewrite Hreduce.
    apply exp_independent_path_add.
    + apply Hindep.
    + remember (V.mk_vec (fun i : fin n' => DE.idx e (fin2finS i))) as e'.
      rewrite <- (V.mk_vec_bij_fin _ (DE.exp_default num) e').
      apply IHn. intros i. subst e'. unfold DE.idx. rewrite V.v_idx_mk_vec. apply Hindep.
Qed.

(* Indexing preserves independence of an acceptor. *)
Lemma exp_independent_of_acc_idx :
  forall n d d' (v : exp (ary '{n} d)) (a : acc d') (i : fin n),
    exp_independent_of_acc v a ->
    exp_independent_of_acc (DE.idx v i) a.
Proof.
  intros n d d' v a i Hindep p Hp.
  apply exp_independent_path_idx with (i := i).
  apply Hindep. exact Hp.
Qed.

(* Scalar indexing of an independent array stays independent of a path. *)
Lemma rexp_idx_independent_of_acc :
  forall n (v : exp (ary '{n} num)) d' (a : acc d') (i : fin n) (p : DE.path),
    exp_independent_of_acc v a -> @PCG.in_acc d' p a ->
    rexp_independent_of_path (DE.idx v i) p.
Proof.
  intros n v d' a i p Hin Hp. unfold DE.idx. apply (Hin p Hp).
Qed.

(* The ReLU branch condition [leExp v|[i] zero] does not read [a] when [v]
   does not. *)
Lemma bexp_leExp_zero_independent_of_acc :
  forall n (v : exp (ary '{n} num)) d' (a : acc d') (i : fin n) (p : DE.path),
    exp_independent_of_acc v a -> @PCG.in_acc d' p a ->
    bexp_independent_of_path (CD.leExp (DE.idx v i) CD.zero) p.
Proof.
  intros n v d' a i p Hin Hp. unfold CD.leExp. split.
  - eapply rexp_idx_independent_of_acc; eassumption.
  - exact I.
Qed.

(* The LeakyReLU branch condition [gtExp v|[i] zero] does not read [a] when
   [v] does not. *)
Lemma bexp_gtExp_zero_independent_of_acc :
  forall n (v : exp (ary '{n} num)) d' (a : acc d') (i : fin n) (p : DE.path),
    exp_independent_of_acc v a -> @PCG.in_acc d' p a ->
    bexp_independent_of_path (CD.gtExp (DE.idx v i) CD.zero) p.
Proof.
  intros n v d' a i p Hin Hp. unfold CD.gtExp. split.
  - eapply rexp_idx_independent_of_acc; eassumption.
  - exact I.
Qed.

(* [mkvSeq] is independent of [a] iff every element is independent of [a]. *)
Lemma exp_independent_of_acc_mkvSeq :
  forall n d d' (f : fin n -> exp d) (a : acc d'),
    (forall i, exp_independent_of_acc (f i) a) ->
    exp_independent_of_acc (DE.mkvSeq f) a.
Proof.
  intros n d d' f a Hindep p Hp i.
  unfold DE.mkvSeq. rewrite V.v_nth_mk_vec with (H := fin_proof i).
  rewrite nat2fin_fin2nat. apply Hindep. exact Hp.
Qed.

(* Main loop invariant for the [sum] accumulator loop. *)
Lemma sum_loop_invariant :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (acc0 : R)
    (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    rho0 = PCG.update rho wtmp_path acc0 ->
    (forall i rho', body i rho' = PCG.update rho' wtmp_path
      (Rplus (to_pcg_exp (DE.idx e i) rho') (value_at rho' wtmp_path))) ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp_acc ->
    value_at (PCG.seqfor body rho0) wtmp_path = Rplus acc0 (to_pcg_exp (CD.sum e) rho).
Proof.
  induction n as [| n' IHn]; intros e rho acc0 rho0 body Hrho0 Hbody Hindep.
  - rewrite Hrho0. simpl. rewrite to_pcg_exp_zero. rewrite Rplus_0_r. reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq.
    remember (PCG.seqfor (fun i : fin n' => body (FS[i])) rho0) as rho1 eqn:Heqrho1.
    assert (Hrho1 : forall q, q <> wtmp_path -> rho1 q = rho0 q).
    { intros q Hq. rewrite Heqrho1. apply PCG.seqfor_pointwise. intros i rho''.
      rewrite Hbody. apply sum_body_outside. auto. }
    assert (Hlast : to_pcg_exp (DE.idx e (ltS n')) rho1 = to_pcg_exp (DE.idx e (ltS n')) rho).
    { apply exp_independent_of_tmp_eval.
      - assert (Hindep_last : @exp_independent_of_acc num num (DE.idx e (ltS n')) wtmp_acc).
        { intros p Hp. apply exp_independent_path_idx with (i := ltS n'). apply Hindep. exact Hp. }
        exact Hindep_last.
      - intros p Hp.
        assert (Hp' : p <> wtmp_path) by (intro Hc; apply Hp; simpl; auto).
        rewrite (Hrho1 p Hp'). rewrite Hrho0. apply PCG.update_neq. auto. }
    set (e' := fst e : exp (ary '{n'} num)) in *.
    assert (Hrest : value_at rho1 wtmp_path = Rplus acc0 (to_pcg_exp (CD.sum e') rho)).
    { assert (Hbody' :
        PCG.seqfor (fun i : fin n' => body (FS[i])) rho0 =
        PCG.seqfor (fun i : fin n' => fun rho'' => PCG.update rho'' wtmp_path
          (Rplus (to_pcg_exp (DE.idx e' i) rho'') (value_at rho'' wtmp_path))) rho0).
      { assert (Hpoint : forall i : fin n',
          (fun i0 : fin n' => body (FS[i0])) i =
          (fun i0 : fin n' => fun rho'' => PCG.update rho'' wtmp_path
            (Rplus (to_pcg_exp (DE.idx e' i0) rho'') (value_at rho'' wtmp_path))) i).
        { intro i. apply functional_extensionality. intro rho''.
          rewrite Hbody. rewrite idx_fin2finS_eq. reflexivity. }
        rewrite (PCG.seqfor_extensionality _ _ Hpoint). reflexivity. }
      rewrite Heqrho1. rewrite Hbody'. apply IHn with (rho0 := rho0).
      + exact Hrho0.
      + intros i rho''. reflexivity.
      + apply exp_independent_fst. exact Hindep. }
    rewrite (Hbody (ltS n') rho1).
    rewrite value_at_update_same.
    rewrite Hlast. rewrite Hrest.
    rewrite sum_Sn. rewrite to_pcg_exp_add.
    unfold e' in *.
    rewrite <- (Rplus_assoc (to_pcg_exp (DE.idx e (ltS n')) rho) acc0 (to_pcg_exp (CD.sum (fst e)) rho)).
    rewrite (Rplus_comm (to_pcg_exp (DE.idx e (ltS n')) rho) acc0).
    rewrite (Rplus_assoc acc0 (to_pcg_exp (DE.idx e (ltS n')) rho) (to_pcg_exp (CD.sum (fst e)) rho)).
    reflexivity.
Qed.

(* The [sum] loop does not touch any path other than [wtmp_path]. *)
Lemma sum_loop_outside :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (acc0 : R) (p : DE.path)
    (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    p <> wtmp_path ->
    rho0 = PCG.update rho wtmp_path acc0 ->
    (forall i rho', body i rho' = PCG.update rho' wtmp_path
      (Rplus (to_pcg_exp (DE.idx e i) rho') (value_at rho' wtmp_path))) ->
    PCG.seqfor body rho0 p = rho0 p.
Proof.
  intros n e rho acc0 p rho0 body Hp Hrho0 Hbody.
  rewrite Hrho0. apply PCG.seqfor_pointwise. intros i rho'.
  rewrite Hbody. apply sum_body_outside. auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Path-parameterised sum-loop lemmas (needed for nested accumulators).      *)
(* -------------------------------------------------------------------------- *)

Lemma sum_body_outside_path :
  forall n (e : DE.exp (ary '{n} num)) (i : fin n) (rho' : PCG.env)
    (p tmp_p : DE.path),
    p <> tmp_p ->
    PCG.update rho' tmp_p
      (Rplus (to_pcg_exp (DE.idx e i) rho')
             (value_at rho' tmp_p)) p = rho' p.
Proof.
  intros n e i rho' p tmp_p Hp. apply PCG.update_neq. intro Hc. apply Hp. auto.
Qed.

Lemma exp_independent_fst_path :
  forall n d (e : DE.exp (ary '{S n} d)) (tmp_p : DE.path),
    @exp_independent_of_acc (ary '{S n} d) num e (@PCG.acc' num tmp_p) ->
    @exp_independent_of_acc (ary '{n} d) num (fst e) (@PCG.acc' num tmp_p).
Proof.
  intros n d e tmp_p Hindep p Hp i.
  rewrite <- v_nth_fin2finS_eq.
  apply exp_independent_path_idx with (i := FS[i]).
  apply Hindep. exact Hp.
Qed.

Lemma sum_loop_invariant_path :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (acc0 : R)
    (tmp_p : DE.path) (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    rho0 = PCG.update rho tmp_p acc0 ->
    (forall i rho', body i rho' = PCG.update rho' tmp_p
      (Rplus (to_pcg_exp (DE.idx e i) rho')
             (value_at rho' tmp_p))) ->
    @exp_independent_of_acc (ary '{n} num) num e (@PCG.acc' num tmp_p) ->
    value_at (PCG.seqfor body rho0) tmp_p =
    Rplus acc0 (to_pcg_exp (CD.sum e) rho).
Proof.
  induction n as [| n' IHn]; intros e rho acc0 tmp_p rho0 body Hrho0 Hbody Hindep.
  - rewrite Hrho0. simpl. unfold PCG.skip. rewrite value_at_update_same.
    rewrite to_pcg_exp_zero. rewrite Rplus_0_r. reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq.
    remember (PCG.seqfor (fun i : fin n' => body (FS[i])) rho0) as rho1 eqn:Heqrho1.
    assert (Hrho1 : forall q, q <> tmp_p -> rho1 q = rho0 q).
    { intros q Hq. rewrite Heqrho1. apply PCG.seqfor_pointwise. intros i rho''.
      rewrite Hbody. apply sum_body_outside_path. auto. }
    assert (Hlast : to_pcg_exp (DE.idx e (ltS n')) rho1 =
                    to_pcg_exp (DE.idx e (ltS n')) rho).
    { apply exp_independent_of_acc_eval with (a := @PCG.acc' num tmp_p).
      - assert (Hindep_last : @exp_independent_of_acc num num (DE.idx e (ltS n')) (@PCG.acc' num tmp_p)).
        { intros p Hp. apply exp_independent_path_idx with (i := ltS n'). apply Hindep. exact Hp. }
        exact Hindep_last.
      - intros p Hp.
        assert (Hp' : p <> tmp_p) by (intro Hc; apply Hp; simpl; auto).
        rewrite (Hrho1 p Hp'). rewrite Hrho0. apply PCG.update_neq. auto. }
    set (e' := fst e : exp (ary '{n'} num)) in *.
    assert (Hrest : value_at rho1 tmp_p =
                    Rplus acc0 (to_pcg_exp (CD.sum e') rho)).
    { rewrite Heqrho1.
      apply IHn with (rho0 := rho0).
      - exact Hrho0.
      - intros i rho'. rewrite Hbody. rewrite idx_fin2finS_eq. reflexivity.
      - apply exp_independent_fst_path. exact Hindep. }
    rewrite (Hbody (ltS n') rho1).
    rewrite value_at_update_same.
    rewrite Hlast. rewrite Hrest.
    rewrite sum_Sn. rewrite to_pcg_exp_add.
    unfold e' in *.
    rewrite <- (Rplus_assoc (to_pcg_exp (DE.idx e (ltS n')) rho) acc0
                            (to_pcg_exp (CD.sum (fst e)) rho)).
    rewrite (Rplus_comm (to_pcg_exp (DE.idx e (ltS n')) rho) acc0).
    rewrite (Rplus_assoc acc0 (to_pcg_exp (DE.idx e (ltS n')) rho)
                         (to_pcg_exp (CD.sum (fst e)) rho)).
    reflexivity.
Qed.

Lemma sum_loop_outside_path :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (acc0 : R)
    (p tmp_p : DE.path) (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    p <> tmp_p ->
    rho0 = PCG.update rho tmp_p acc0 ->
    (forall i rho', body i rho' = PCG.update rho' tmp_p
      (Rplus (to_pcg_exp (DE.idx e i) rho')
             (value_at rho' tmp_p))) ->
    PCG.seqfor body rho0 p = rho0 p.
Proof.
  intros n e rho acc0 p tmp_p rho0 body Hp Hrho0 Hbody.
  rewrite Hrho0. apply PCG.seqfor_pointwise. intros i rho'.
  rewrite Hbody. apply sum_body_outside_path. auto.
Qed.

(* The whole sum loop environment equals the initial environment with only the
   accumulator path updated to the final sum. *)
Lemma seqfor_sum_tmp_path_Some :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (acc0 : R)
    (tmp_p : DE.path) (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    rho0 = PCG.update rho tmp_p acc0 ->
    (forall i rho', body i rho' = PCG.update rho' tmp_p
      (Rplus (to_pcg_exp (DE.idx e i) rho')
             (value_at rho' tmp_p))) ->
    @exp_independent_of_acc (ary '{n} num) num e (@PCG.acc' num tmp_p) ->
    PCG.seqfor body rho0 tmp_p = Some (Rplus acc0 (to_pcg_exp (CD.sum e) rho)).
Proof.
  induction n as [| n' IHn]; intros e rho acc0 tmp_p rho0 body Hrho0 Hbody Hindep.
  - rewrite Hrho0. simpl. unfold PCG.skip. rewrite PCG.update_eq.
    rewrite to_pcg_exp_zero. rewrite Rplus_0_r. reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq. rewrite Hbody.
    unfold value_at. rewrite PCG.update_eq.
    remember (PCG.seqfor (fun i : fin n' => body (FS[i])) rho0) as rho1 eqn:Heqrho1.
    assert (Hrho1 : forall q, q <> tmp_p -> rho1 q = rho0 q).
    { intros q Hq. rewrite Heqrho1. apply PCG.seqfor_pointwise. intros i rho''.
      rewrite Hbody. apply sum_body_outside_path. auto. }
    assert (Hlast : to_pcg_exp (DE.idx e (ltS n')) rho1 =
                    to_pcg_exp (DE.idx e (ltS n')) rho).
    { apply exp_independent_of_acc_eval with (a := @PCG.acc' num tmp_p).
      - assert (Hindep_last : @exp_independent_of_acc num num (DE.idx e (ltS n')) (@PCG.acc' num tmp_p)).
        { intros p Hp. apply exp_independent_path_idx with (i := ltS n'). apply Hindep. exact Hp. }
        exact Hindep_last.
      - intros p Hp.
        assert (Hp' : p <> tmp_p) by (intro Hc; apply Hp; simpl; auto).
        rewrite (Hrho1 p Hp'). rewrite Hrho0. apply PCG.update_neq. auto. }
    set (e' := fst e : DE.exp (ary '{n'} num)) in *.
    assert (Hrest : rho1 tmp_p = Some (Rplus acc0 (to_pcg_exp (CD.sum e') rho))).
    { rewrite Heqrho1. apply IHn with (rho0 := rho0).
      - exact Hrho0.
      - intros i rho''. rewrite Hbody. rewrite idx_fin2finS_eq. reflexivity.
      - apply exp_independent_fst_path. exact Hindep. }
    rewrite Hlast. rewrite Hrest. rewrite sum_Sn. rewrite to_pcg_exp_add.
    unfold e' in *. rewrite <- (Rplus_assoc (to_pcg_exp (DE.idx e (ltS n')) rho) acc0
                            (to_pcg_exp (CD.sum (fst e)) rho)).
    rewrite (Rplus_comm (to_pcg_exp (DE.idx e (ltS n')) rho) acc0).
    rewrite (Rplus_assoc acc0 (to_pcg_exp (DE.idx e (ltS n')) rho)
                         (to_pcg_exp (CD.sum (fst e)) rho)).
    reflexivity.
Qed.

Lemma sum_loop_env_path :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (acc0 : R)
    (tmp_p : DE.path) (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    rho0 = PCG.update rho tmp_p acc0 ->
    (forall i rho', body i rho' = PCG.update rho' tmp_p
      (Rplus (to_pcg_exp (DE.idx e i) rho')
             (value_at rho' tmp_p))) ->
    @exp_independent_of_acc (ary '{n} num) num e (@PCG.acc' num tmp_p) ->
    PCG.seqfor body rho0 = PCG.update rho tmp_p (Rplus acc0 (to_pcg_exp (CD.sum e) rho)).
Proof.
  intros n e rho acc0 tmp_p rho0 body Hrho0 Hbody Hindep.
  apply functional_extensionality. intro q.
  destruct (classic (q = tmp_p)) as [Heq | Hne].
  - subst q. rewrite (seqfor_sum_tmp_path_Some body Hrho0 Hbody Hindep).
    unfold PCG.update. rewrite DE.path_eqb_refl. reflexivity.
  - rewrite (sum_loop_outside_path e body Hne Hrho0 Hbody).
    rewrite Hrho0. unfold PCG.update.
    destruct (DE.path_eqb tmp_p q) eqn:E.
    + apply DE.path_eqb_eq in E. exfalso. apply Hne. symmetry. exact E.
    + reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Helpers for the [max] accumulator loop.                                   *)
(* -------------------------------------------------------------------------- *)

Lemma to_pcg_exp_REif : forall b e1 e2 rho,
  to_pcg_exp (REif b e1 e2 : exp num) rho =
  if DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b
  then to_pcg_exp (e1 : exp num) rho else to_pcg_exp (e2 : exp num) rho.
Proof.
  intros b e1 e2 rho. cbv [to_pcg_exp]. simpl. reflexivity.
Qed.

Lemma to_pcg_exp_BGt : forall x y rho,
  DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) (CD.gtExp x y) =
  match Rgt_dec (to_pcg_exp x rho) (to_pcg_exp y rho) with
  | left _ => true | right _ => false
  end.
Proof.
  intros x y rho. cbv [to_pcg_exp CD.gtExp]. simpl. reflexivity.
Qed.

Lemma max_Sn : forall n (e : DE.exp (ary '{S n} num)),
  CD.max e = REif (CD.gtExp (DE.idx e (ltS n)) (CD.max (fst e)))
                  (DE.idx e (ltS n))
                  (CD.max (fst e)).
Proof.
  intros n e. unfold CD.max.
  assert (He : e = (fst e, snd e)) by apply surjective_pairing.
  rewrite He. simpl. rewrite idx_last_eq. reflexivity.
Qed.

Lemma max_body_outside :
  forall n (e : DE.exp (ary '{n} num)) (i : fin n) (rho' : PCG.env) (p : DE.path),
    p <> wtmp_path ->
    PCG.update rho' wtmp_path
      (if DE.eval_bexp (fun s => match rho' (DE.Var s) with Some r => r | None => R0 end)
          (CD.gtExp (DE.idx e i) (CG.vrd "__tmp"))
       then to_pcg_exp (DE.idx e i) rho'
       else value_at rho' wtmp_path) p = rho' p.
Proof.
  intros n e i rho' p Hp. apply PCG.update_neq. intro Hc. apply Hp. auto.
Qed.

(* Main loop invariant for the [max] accumulator loop. *)
Lemma max_loop_invariant :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env)
    (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    rho0 = PCG.update rho wtmp_path R0 ->
    (forall i rho', body i rho' = PCG.update rho' wtmp_path
      (if DE.eval_bexp (fun s => match rho' (DE.Var s) with Some r => r | None => R0 end)
          (CD.gtExp (DE.idx e i) (CG.vrd "__tmp"))
       then to_pcg_exp (DE.idx e i) rho'
       else value_at rho' wtmp_path)) ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp_acc ->
    value_at (PCG.seqfor body rho0) wtmp_path = to_pcg_exp (CD.max e) rho.
Proof.
  induction n as [| n' IHn]; intros e rho rho0 body Hrho0 Hbody Hindep.
  - rewrite Hrho0. simpl. unfold CD.max. simpl. rewrite to_pcg_exp_zero. reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq.
    remember (PCG.seqfor (fun i : fin n' => body (FS[i])) rho0) as rho1 eqn:Heqrho1.
    assert (Hrho1 : forall q, q <> wtmp_path -> rho1 q = rho0 q).
    { intros q Hq. rewrite Heqrho1. apply PCG.seqfor_pointwise. intros i rho''.
      rewrite Hbody. apply max_body_outside. auto. }
    assert (Hlast : to_pcg_exp (DE.idx e (ltS n')) rho1 = to_pcg_exp (DE.idx e (ltS n')) rho).
    { apply exp_independent_of_tmp_eval.
      - assert (Hindep_last : @exp_independent_of_acc num num (DE.idx e (ltS n')) wtmp_acc).
        { intros p Hp. apply exp_independent_path_idx with (i := ltS n'). apply Hindep. exact Hp. }
        exact Hindep_last.
      - intros p Hp.
        assert (Hp' : p <> wtmp_path) by (intro Hc; apply Hp; simpl; auto).
        rewrite (Hrho1 p Hp'). rewrite Hrho0. apply PCG.update_neq. auto. }
    set (e' := fst e : exp (ary '{n'} num)) in *.
    assert (Hrest : value_at rho1 wtmp_path = to_pcg_exp (CD.max e') rho).
    { assert (Hbody' :
        PCG.seqfor (fun i : fin n' => body (FS[i])) rho0 =
        PCG.seqfor (fun i : fin n' => fun rho'' => PCG.update rho'' wtmp_path
          (if DE.eval_bexp (fun s => match rho'' (DE.Var s) with Some r => r | None => R0 end)
             (CD.gtExp (DE.idx e' i) (CG.vrd "__tmp"))
           then to_pcg_exp (DE.idx e' i) rho''
           else value_at rho'' wtmp_path)) rho0).
      { assert (Hpoint : forall i : fin n',
          (fun i0 : fin n' => body (FS[i0])) i =
          (fun i0 : fin n' => fun rho'' => PCG.update rho'' wtmp_path
            (if DE.eval_bexp (fun s => match rho'' (DE.Var s) with Some r => r | None => R0 end)
               (CD.gtExp (DE.idx e' i0) (CG.vrd "__tmp"))
             then to_pcg_exp (DE.idx e' i0) rho''
             else value_at rho'' wtmp_path)) i).
        { intro i. apply functional_extensionality. intro rho''.
          rewrite Hbody. rewrite idx_fin2finS_eq. reflexivity. }
        rewrite (PCG.seqfor_extensionality _ _ Hpoint). reflexivity. }
      rewrite Heqrho1. rewrite Hbody'. apply IHn with (rho0 := rho0).
      + exact Hrho0.
      + intros i rho''. reflexivity.
      + apply exp_independent_fst. exact Hindep. }
    rewrite (Hbody (ltS n') rho1).
    rewrite value_at_update_same.
    rewrite Hlast. rewrite Hrest.
    rewrite max_Sn. rewrite to_pcg_exp_REif.
    assert (Hcond : DE.eval_bexp (fun s => match rho1 (DE.Var s) with Some r => r | None => R0 end)
                     (CD.gtExp (DE.idx e (ltS n')) (CG.vrd "__tmp")) =
                   DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end)
                     (CD.gtExp (DE.idx e (ltS n')) (CD.max e'))).
    { do 2 rewrite to_pcg_exp_BGt.
      rewrite to_pcg_exp_REvar_tmp' in *.
      rewrite Hlast. rewrite Hrest.
      reflexivity. }
    rewrite Hcond. reflexivity.
Qed.

(* The [max] loop does not touch any path other than [wtmp_path]. *)
Arguments max_loop_invariant {n} e rho rho0 body.

Lemma max_loop_outside :
  forall n (e : DE.exp (ary '{n} num)) (rho : PCG.env) (p : DE.path)
    (rho0 : PCG.env) (body : fin n -> PCG.env -> PCG.env),
    p <> wtmp_path ->
    rho0 = PCG.update rho wtmp_path R0 ->
    (forall i rho', body i rho' = PCG.update rho' wtmp_path
      (if DE.eval_bexp (fun s => match rho' (DE.Var s) with Some r => r | None => R0 end)
          (CD.gtExp (DE.idx e i) (CG.vrd "__tmp"))
       then to_pcg_exp (DE.idx e i) rho'
       else value_at rho' wtmp_path)) ->
    PCG.seqfor body rho0 p = rho0 p.
Proof.
  intros n e rho p rho0 body Hp Hrho0 Hbody.
  rewrite Hrho0. apply PCG.seqfor_pointwise. intros i rho'.
  rewrite Hbody. apply max_body_outside. auto.
Qed.

Arguments max_loop_outside {n} e rho p rho0 body.

(* -------------------------------------------------------------------------- *)
(* Semantic versions of the [new]-based Axioms in CNN_CodeGen.v.             *)
(*                                                                            *)
(* The rules below involve imperative accumulator loops whose bodies read the *)
(* temporary variable.  Because [vrd]/[vwt] are Parameters in CNN_CodeGen.v   *)
(* and [exp num] is not an inductive type, the variable-read construct cannot *)
(* be interpreted as an environment lookup inside the current semantic model. *)
(* They were therefore kept as semantic Axioms.                               *)
(*                                                                            *)
(* [eval_sum_equiv] and [eval_max_equiv] have now been proved as theorems;    *)
(* they require that the input array [e] be independent of the temporary        *)
(* accumulator and that the output acceptor [a] is distinct from the            *)
(* temporary.                                                                 *)
(*                                                                            *)
(* [eval_reduce_equiv] is now also a theorem for the scalar accumulator case    *)
(* [d2 = num]; the generalized theorem [eval_reduce_equiv_gen] covers arbitrary *)
(* accumulator types [d2].                                                      *)
(*                                                                            *)
(* The continuation variants ([eval_creduce_equiv], [eval_cmax_equiv], and      *)
(* [eval_csum_equiv]) are now also theorems.  They require the same            *)
(* input-array independence as above, plus [loopacc_continuation_ok c e_final], *)
(* which states that the continuation [c] preserves undefinedness of the        *)
(* temporary and cannot distinguish the functional result from a read of the    *)
(* temporary after it has been assigned that result.                            *)
(* -------------------------------------------------------------------------- *)

(* A reduction combinator [f] is usable in the accumulator-loop proof when it
   is a semantic function: the value of [f x y] depends only on the semantic
   values of [x] and [y].  This holds for all DataExp combinators used in
   practice (e.g. addition, multiplication, and vector append). *)
Definition reduce_op_proper {d1 d2 : data} (f : exp d1 -> exp d2 -> exp d2) : Prop :=
  forall (x1 x2 : exp d1) (y1 y2 : exp d2) (rho1 rho2 : PCG.env),
    to_pcg_exp x1 rho1 = to_pcg_exp x2 rho2 ->
    to_pcg_exp y1 rho1 = to_pcg_exp y2 rho2 ->
    to_pcg_exp (f x1 y1) rho1 = to_pcg_exp (f x2 y2) rho2.

(* -------------------------------------------------------------------------- *)
(* Helpers for the [reduce] accumulator loop (scalar accumulator).           *)
(* -------------------------------------------------------------------------- *)

Lemma reduce_Sn : forall n d1 d2 (f : exp d1 -> exp d2 -> exp d2) (i : exp d2)
  (e : DE.exp (ary '{S n} d1)),
  CD.reduce f i e = f (DE.idx e (ltS n)) (CD.reduce f i (fst e)).
Proof.
  intros n d1 d2 f i e. unfold CD.reduce.
  assert (He : e = (fst e, snd e)) by apply surjective_pairing.
  rewrite He. simpl. rewrite idx_last_eq. reflexivity.
Qed.

Lemma reduce_body_outside :
  forall n d1 (f : exp d1 -> exp num -> exp num) (e : DE.exp (ary '{n} d1))
         (i0 : fin n) (rho' : PCG.env) (p : DE.path),
    p <> wtmp_path ->
    PCG.update rho' wtmp_path
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho') p = rho' p.
Proof.
  intros n d1 f e i0 rho' p Hp. apply PCG.update_neq. intro Hc. apply Hp. auto.
Qed.

(* Main loop invariant for the [reduce] accumulator loop.
   The accumulator starts as the semantic value of the initial expression [i]
   and each iteration stores [f (e|[i0]) (vrd "__tmp")]. *)
Lemma reduce_loop_invariant :
  forall n d1 (f : exp d1 -> exp num -> exp num) (i : exp num)
         (e : DE.exp (ary '{n} d1)) (rho rho0 : PCG.env)
         (body : fin n -> PCG.env -> PCG.env),
    reduce_op_proper f ->
    rho0 = PCG.update rho wtmp_path (to_pcg_exp i rho) ->
    (forall i0 rho', body i0 rho' = PCG.update rho' wtmp_path
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho')) ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp_acc ->
    value_at (PCG.seqfor body rho0) wtmp_path = to_pcg_exp (CD.reduce f i e) rho.
Proof.
  induction n as [| n' IHn]; intros d1 f i e rho rho0 body Hf Hrho0 Hbody Hindep.
  - rewrite Hrho0. simpl. reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq.
    remember (PCG.seqfor (fun i : fin n' => body (FS[i])) rho0) as rho1 eqn:Heqrho1.
    assert (Hrho1 : forall q, q <> wtmp_path -> rho1 q = rho0 q).
    { intros q Hq. rewrite Heqrho1. apply PCG.seqfor_pointwise. intros j rho''.
      rewrite Hbody. apply reduce_body_outside. auto. }
    assert (Hlast : to_pcg_exp (DE.idx e (ltS n')) rho1 = to_pcg_exp (DE.idx e (ltS n')) rho).
    { apply exp_independent_of_tmp_eval.
      - assert (Hindep_last : @exp_independent_of_acc d1 num (DE.idx e (ltS n')) wtmp_acc).
        { intros p Hp. apply exp_independent_path_idx with (i := ltS n'). apply Hindep. exact Hp. }
        exact Hindep_last.
      - intros p Hp.
        assert (Hp' : p <> wtmp_path) by (intro Hc; apply Hp; simpl; auto).
        rewrite (Hrho1 p Hp'). rewrite Hrho0. apply PCG.update_neq. auto. }
    set (e' := fst e : exp (ary '{n'} d1)) in *.
    assert (Hrest : value_at rho1 wtmp_path = to_pcg_exp (CD.reduce f i e') rho).
    { assert (Hbody' :
        PCG.seqfor (fun i : fin n' => body (FS[i])) rho0 =
        PCG.seqfor (fun i : fin n' => fun rho'' => PCG.update rho'' wtmp_path
          (to_pcg_exp (f (DE.idx e' i) (CG.vrd "__tmp")) rho'')) rho0).
      { assert (Hpoint : forall i : fin n',
          (fun i0 : fin n' => body (FS[i0])) i =
          (fun i0 : fin n' => fun rho'' => PCG.update rho'' wtmp_path
            (to_pcg_exp (f (DE.idx e' i0) (CG.vrd "__tmp")) rho'')) i).
        { intro i0. apply functional_extensionality. intro rho''.
          rewrite Hbody. rewrite idx_fin2finS_eq. reflexivity. }
        rewrite (PCG.seqfor_extensionality _ _ Hpoint). reflexivity. }
      rewrite Heqrho1. rewrite Hbody'. apply IHn with (rho0 := rho0).
      + exact Hf.
      + exact Hrho0.
      + intros i0 rho''. reflexivity.
      + apply exp_independent_fst. exact Hindep. }
    rewrite (Hbody (ltS n') rho1).
    rewrite value_at_update_same.
    rewrite reduce_Sn.
    apply Hf.
    + exact Hlast.
    + rewrite to_pcg_exp_REvar_tmp'. unfold value_at. exact Hrest.
Qed.

(* The [reduce] loop does not touch any path other than [wtmp_path]. *)
Lemma reduce_loop_outside :
  forall n d1 (f : exp d1 -> exp num -> exp num) (i : exp num)
         (e : DE.exp (ary '{n} d1)) (rho rho0 : PCG.env) (p : DE.path)
         (body : fin n -> PCG.env -> PCG.env),
    p <> wtmp_path ->
    rho0 = PCG.update rho wtmp_path (to_pcg_exp i rho) ->
    (forall i0 rho', body i0 rho' = PCG.update rho' wtmp_path
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho')) ->
    PCG.seqfor body rho0 p = rho0 p.
Proof.
  intros n d1 f i e rho rho0 p body Hp Hrho0 Hbody.
  rewrite Hrho0. apply PCG.seqfor_pointwise. intros i0 rho'.
  rewrite Hbody. apply reduce_body_outside. auto.
Qed.

Arguments reduce_loop_invariant {n d1} f i e rho rho0 body.
Arguments reduce_loop_outside {n d1} f i e rho rho0 p body.

(* -------------------------------------------------------------------------- *)
(* Helpers for the [reduce] accumulator loop (arbitrary accumulator type).     *)
(* -------------------------------------------------------------------------- *)

(* Generalized [reduce] body update only touches paths inside the temporary
   acceptor [wtmp_acc] for the accumulator type [d2]. *)
Lemma reduce_body_outside_gen :
  forall n d1 d2 (f : exp d1 -> exp d2 -> exp d2) (e : DE.exp (ary '{n} d1))
         (i0 : fin n) (rho' : PCG.env) (p : DE.path),
    ~ @PCG.in_acc d2 p (@CG.vwt d2 "__tmp") ->
    PCG.assign (@CG.vwt d2 "__tmp")
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho') rho' p = rho' p.
Proof.
  intros n d1 d2 f e i0 rho' p Hp.
  apply PCG.assign_not_in_acc.
  exact Hp.
Qed.

(* Generalized loop invariant: after the loop, reading the temporary variable
   yields exactly the semantic value of [CD.reduce f i e].  The scalar-only
   lemma [reduce_loop_invariant] is the special case [d2 = num] expressed via
   [value_at]. *)
Lemma reduce_loop_invariant_gen :
  forall n d1 d2 (f : exp d1 -> exp d2 -> exp d2) (i : exp d2)
         (e : DE.exp (ary '{n} d1)) (rho rho0 : PCG.env)
         (body : fin n -> PCG.env -> PCG.env),
    reduce_op_proper f ->
    rho0 = PCG.assign (@CG.vwt d2 "__tmp") (to_pcg_exp i rho) rho ->
    (forall i0 rho', body i0 rho' = PCG.assign (@CG.vwt d2 "__tmp")
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho') rho') ->
    @exp_independent_of_acc (ary '{n} d1) d2 e (@CG.vwt d2 "__tmp") ->
    to_pcg_exp (@CG.vrd d2 "__tmp") (PCG.seqfor body rho0) =
    to_pcg_exp (CD.reduce f i e) rho.
Proof.
  induction n as [| n' IHn]; intros d1 d2 f i e rho rho0 body Hf Hrho0 Hbody Hindep.
  - rewrite Hrho0. simpl. unfold PCG.skip. cbn beta.
    erewrite vrd_after_own_vwt; [| discriminate | discriminate ].
    reflexivity.
  - rewrite PCG.seqfor_Sn. unfold PCG.seq.
    remember (PCG.seqfor (fun i : fin n' => body (FS[i])) rho0) as rho1 eqn:Heqrho1.
    set (wtmp := @CG.vwt d2 "__tmp") in *.
    assert (Hrho1_out : forall q, ~ @PCG.in_acc d2 q wtmp -> rho1 q = rho0 q).
    { intros q Hq. rewrite Heqrho1. apply PCG.seqfor_pointwise. intros j rho''.
      rewrite Hbody. apply reduce_body_outside_gen. exact Hq. }
    assert (Hlast : to_pcg_exp (DE.idx e (ltS n')) rho1 =
                    to_pcg_exp (DE.idx e (ltS n')) rho).
    { apply exp_independent_of_acc_eval with (a := wtmp).
      - apply exp_independent_of_acc_idx with (i := ltS n'). exact Hindep.
      - intros q Hq.
        assert (Hq' : ~ @PCG.in_acc d2 q wtmp) by exact Hq.
        rewrite (Hrho1_out q Hq').
        rewrite Hrho0. apply PCG.assign_not_in_acc. exact Hq. }
    set (e' := fst e : exp (ary '{n'} d1)) in *.
    assert (Hrest : to_pcg_exp (@CG.vrd d2 "__tmp") rho1 =
                    to_pcg_exp (CD.reduce f i e') rho).
    { assert (Hbody' :
        PCG.seqfor (fun i : fin n' => body (FS[i])) rho0 =
        PCG.seqfor (fun i : fin n' => fun rho'' => PCG.assign (@CG.vwt d2 "__tmp")
          (to_pcg_exp (f (DE.idx e' i) (CG.vrd "__tmp")) rho'') rho'') rho0).
      { assert (Hpoint : forall i : fin n',
          (fun i0 : fin n' => body (FS[i0])) i =
          (fun i0 : fin n' => fun rho'' => PCG.assign (@CG.vwt d2 "__tmp")
            (to_pcg_exp (f (DE.idx e' i0) (CG.vrd "__tmp")) rho'') rho'') i).
        { intro i0. apply functional_extensionality. intro rho''.
          rewrite Hbody. rewrite idx_fin2finS_eq. reflexivity. }
        rewrite (PCG.seqfor_extensionality _ _ Hpoint). reflexivity. }
      rewrite Heqrho1. rewrite Hbody'. apply IHn with (rho0 := rho0).
      + exact Hf.
      + exact Hrho0.
      + intros i0 rho''. reflexivity.
      + apply exp_independent_fst_gen. exact Hindep. }
    assert (Hbody_last : body (ltS n') rho1 =
      PCG.assign (@CG.vwt d2 "__tmp")
        (to_pcg_exp (f (DE.idx e (ltS n')) (CG.vrd "__tmp")) rho1) rho1).
    { apply Hbody. }
    rewrite Hbody_last.
    assert (Hread_tmp : to_pcg_exp (@CG.vrd d2 "__tmp")
      (PCG.assign (@CG.vwt d2 "__tmp")
        (to_pcg_exp (f (DE.idx e (ltS n')) (CG.vrd "__tmp")) rho1) rho1) =
      to_pcg_exp (f (DE.idx e (ltS n')) (CG.vrd "__tmp")) rho1).
    { apply to_pcg_exp_vrd_after_vwt. }
    rewrite Hread_tmp. rewrite reduce_Sn.
    apply Hf.
    + exact Hlast.
    + exact Hrest.
Qed.

(* The generalized [reduce] loop does not touch any path outside the temporary
   acceptor [wtmp_acc] for the accumulator type [d2]. *)
Lemma reduce_loop_outside_gen :
  forall n d1 d2 (f : exp d1 -> exp d2 -> exp d2) (i : exp d2)
         (e : DE.exp (ary '{n} d1)) (rho rho0 : PCG.env) (p : DE.path)
         (body : fin n -> PCG.env -> PCG.env),
    ~ @PCG.in_acc d2 p (@CG.vwt d2 "__tmp") ->
    rho0 = PCG.assign (@CG.vwt d2 "__tmp") (to_pcg_exp i rho) rho ->
    (forall i0 rho', body i0 rho' = PCG.assign (@CG.vwt d2 "__tmp")
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho') rho') ->
    PCG.seqfor body rho0 p = rho0 p.
Proof.
  intros n d1 d2 f i e rho rho0 p body Hp Hrho0 Hbody.
  rewrite Hrho0. apply PCG.seqfor_pointwise. intros i0 rho'.
  rewrite Hbody. apply reduce_body_outside_gen. exact Hp.
Qed.

Arguments reduce_loop_invariant_gen {n d1 d2} f i e rho rho0 body.
Arguments reduce_loop_outside_gen {n d1 d2} f i e rho rho0 p body.

Theorem eval_reduce_equiv :
  forall n d1 (f : exp d1 -> exp num -> exp num) (i : exp num)
         (e : exp (ary '{n} d1)) (a : acc num) (rho : PCG.env),
    reduce_op_proper f ->
    @PCG.StructUndefined num wtmp_acc rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp_acc ->
    a <> wtmp_acc ->
    eval (CG.assign (a, CD.reduce f i e)) rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, i),
        CG.seq (CG.seqfor (fun i0 => CG.assign (w, f (DE.idx e i0) v)),
          CG.assign (a, v))))) rho.
Proof.
  intros n d1 f i e a rho Hf Hundef Hindep Hneq.
  apply PCG.StructUndefined_num in Hundef.
  assert (Ha : a <> wtmp_path) by (intro Hc; apply Hneq; simpl; rewrite Hc; reflexivity).
  apply functional_extensionality. intro p.
  rewrite eval_assign.
  unfold eval at 1.
  change (CG.vwt "__tmp") with wtmp_path.
  simpl.
  set (rho_init := PCG.update rho wtmp_path (to_pcg_exp i rho)).
  set (body := fun (i0 : fin n) (rho' : PCG.env) =>
    PCG.update rho' wtmp_path
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho')).
  assert (Hval : value_at (PCG.seqfor body rho_init) wtmp_path = to_pcg_exp (CD.reduce f i e) rho).
  { apply (@reduce_loop_invariant _ _ f i e rho rho_init body); auto; try reflexivity; intros; reflexivity. }
  assert (Houtside : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. apply (@reduce_loop_outside _ _ f i e rho rho_init q body); auto; try reflexivity; intros; reflexivity. }
  simpl. unfold PCG.seq. fold rho_init. fold body.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  fold body. fold rho_init.
  assert (Hread : to_pcg_exp (CG.vrd "__tmp") (PCG.seqfor body rho_init) = (value_at (PCG.seqfor body rho_init) wtmp_path : PCG.exp num)).
  { apply to_pcg_exp_REvar_tmp'. }
  rewrite Hread. rewrite Hval.
  destruct (path_eqb wtmp_path p) eqn:Etmp.
  - apply path_eqb_eq in Etmp. subst p.
    rewrite PCG.update_neq by exact Ha.
    rewrite Hundef. rewrite remove_eq. reflexivity.
  - assert (Hp : p <> wtmp_path) by (intro Hc; rewrite Hc in Etmp; discriminate).
    destruct (path_eqb a p) eqn:Ea.
    + apply path_eqb_eq in Ea. subst p.
      rewrite remove_neq by (intro Hc; apply Ha; symmetry; exact Hc).
      rewrite (PCG.update_eq rho a (to_pcg_exp (CD.reduce f i e) rho)).
      rewrite (PCG.update_eq (PCG.seqfor body rho_init) a (to_pcg_exp (CD.reduce f i e) rho)). reflexivity.
    + assert (Hp2 : (a : path) <> p).
      { intro Hc. apply path_eqb_eq in Hc. rewrite Hc in Ea. discriminate. }
      rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
      assert (Hupd1 : PCG.update rho a (to_pcg_exp (CD.reduce f i e) rho) p = rho p)
        by (apply PCG.update_neq; exact Hp2).
      assert (Hupd2 : PCG.update (PCG.seqfor body rho_init) a (to_pcg_exp (CD.reduce f i e) rho) p = (PCG.seqfor body rho_init) p)
        by (apply PCG.update_neq; exact Hp2).
      rewrite Hupd1. rewrite Hupd2.
      rewrite Houtside by exact Hp.
      unfold rho_init. rewrite PCG.update_neq by (intro Hc; apply Hp; symmetry; exact Hc).
      reflexivity.
Qed.

(* Generalized semantic correctness of the [reduce] combinator for an
   arbitrary accumulator type [d2].  The output acceptor [a] must be disjoint
   from the temporary region used by [loopacc]; for scalar accumulators this
   reduces to [a <> wtmp_acc]. *)
Theorem eval_reduce_equiv_gen :
  forall n d1 d2 (f : exp d1 -> exp d2 -> exp d2) (i : exp d2)
         (e : exp (ary '{n} d1)) (a : acc d2) (rho : PCG.env),
    reduce_op_proper f ->
    @PCG.StructUndefined d2 (@CG.vwt d2 "__tmp") rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e (@CG.vwt d2 "__tmp") ->
    (forall p, @PCG.in_acc d2 p (@CG.vwt d2 "__tmp") -> ~ @PCG.in_acc d2 p a) ->
    eval (CG.assign (a, CD.reduce f i e)) rho =
    eval (@CG.loopacc d2 (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, i),
        CG.seq (CG.seqfor (fun i0 => CG.assign (w, f (DE.idx e i0) v)),
          CG.assign (a, v))))) rho.
Proof.
  intros n d1 d2 f i e a rho Hf Hundef Hindep Hdisj.
  set (wtmp := @CG.vwt d2 "__tmp") in *.
  apply functional_extensionality. intro p.
  rewrite eval_assign.
  unfold eval at 1. simpl.
  set (rho_init := PCG.assign (@CG.vwt d2 "__tmp") (to_pcg_exp i rho) rho).
  set (body := fun (i0 : fin n) (rho' : PCG.env) =>
    PCG.assign (@CG.vwt d2 "__tmp")
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho') rho').
  assert (Hval : to_pcg_exp (@CG.vrd d2 "__tmp") (PCG.seqfor body rho_init) =
                 to_pcg_exp (CD.reduce f i e) rho).
  { apply (@reduce_loop_invariant_gen _ _ _ f i e rho rho_init body); auto;
      try reflexivity; intros; reflexivity. }
  assert (Houtside : forall q, ~ @PCG.in_acc d2 q wtmp ->
    PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. apply (@reduce_loop_outside_gen _ _ _ f i e rho rho_init q body); auto;
      try reflexivity; intros; reflexivity. }
  unfold PCG.seq. fold rho_init. fold body.
  (* Rewrite the final read of the temporary using the loop invariant. *)
  rewrite Hval.
  destruct (classic (@PCG.in_acc d2 p wtmp)) as [Hin | Hout].
  - (* Path [p] is inside the temporary region.  The left-hand side leaves
       [p] unchanged because [a] is disjoint from [wtmp]; the right-hand side
       removes [p].  Equality follows from [StructUndefined]. *)
    assert (Hlhs : PCG.assign a (to_pcg_exp (CD.reduce f i e) rho) rho p = rho p).
    { apply PCG.assign_not_in_acc. intro Hc. apply Hdisj in Hin. contradiction. }
    assert (Hrhs : PCG.vrm wtmp
      (PCG.assign a (to_pcg_exp (CD.reduce f i e) rho)
        (PCG.seqfor body rho_init)) p = None).
    { apply PCG.vrm_in_acc. exact Hin. }
    rewrite Hlhs. unfold wtmp in Hrhs. rewrite Hrhs.
    apply PCG.StructUndefined_implies_None with (a := wtmp); assumption.
  - (* Path [p] is outside the temporary region; [vrm] is the identity there. *)
    assert (Hvrm : PCG.vrm wtmp
      (PCG.assign a (to_pcg_exp (CD.reduce f i e) rho)
        (PCG.seqfor body rho_init)) p =
      PCG.assign a (to_pcg_exp (CD.reduce f i e) rho)
        (PCG.seqfor body rho_init) p).
    { apply PCG.vrm_not_in_acc. exact Hout. }
    unfold wtmp in Hvrm. rewrite Hvrm.
    destruct (classic (@PCG.in_acc d2 p a)) as [Hina | Houta].
    + (* Path [p] is in the output acceptor; both sides assign the same value. *)
      rewrite (assign_in_acc_independent_of_env d2 a (to_pcg_exp (CD.reduce f i e) rho)
        (PCG.seqfor body rho_init) rho p Hina).
      reflexivity.
    + (* Path [p] is outside both regions; both sides preserve the original env. *)
      rewrite (PCG.assign_not_in_acc _ _ _ _ _ Houta).
      rewrite (PCG.assign_not_in_acc _ _ _ _ _ Houta).
      rewrite (Houtside p Hout).
      unfold rho_init. symmetry. apply PCG.assign_not_in_acc. exact Hout.
Qed.

(* Side condition for continuation variants of accumulator loops:
   the continuation [c] must preserve undefinedness of the temporary
   and behave the same when applied to the final expression or to a
   read of the temporary that has been assigned the final value.
   The continuation is evaluated at depth 1 (inside the [loopacc] body). *)
Definition loopacc_continuation_ok {d} (c : exp d -> CG.comm) (e_final : exp d) : Prop :=
  let wtmp := CG.vwt "__tmp" in
  (forall rho, @PCG.StructUndefined d wtmp rho -> @PCG.StructUndefined d wtmp (eval_aux (c e_final) 1 rho)) /\
  (forall rho eta (v : PCG.exp d),
     to_pcg_exp e_final rho = v ->
     (forall q, ~ @PCG.in_acc d q wtmp -> eta q = rho q) ->
     forall p, ~ @PCG.in_acc d p wtmp ->
       eval_aux (c (CG.vrd "__tmp")) 1 (PCG.assign wtmp v eta) p = eval_aux (c e_final) 1 rho p).

(* TODO: generalize [eval_creduce_equiv] to arbitrary accumulator types [d2]
   using the same strategy as [eval_reduce_equiv_gen] and the already-generic
   [loopacc_continuation_ok]. *)
Theorem eval_creduce_equiv :
  forall n d1 (f : exp d1 -> exp num -> exp num) (i : exp num)
         (e : exp (ary '{n} d1)) (c : exp num -> CG.comm) (rho : PCG.env),
    reduce_op_proper f ->
    @PCG.StructUndefined num wtmp_acc rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp_acc ->
    loopacc_continuation_ok c (CD.reduce f i e) ->
    eval_aux (c (CD.reduce f i e)) 1 rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, i),
        CG.seq (CG.seqfor (fun i0 => CG.assign (w, f (DE.idx e i0) v)),
          c v)))) rho.
Proof.
  intros n d1 f i e c rho Hf Hundef Hindep Hok.
  apply PCG.StructUndefined_num in Hundef.
  destruct Hok as [Hstruct Hcont].
  apply functional_extensionality. intro p.
  unfold eval at 1.
  change (CG.vwt "__tmp") with wtmp_path.
  simpl.
  set (rho_init := PCG.update rho wtmp_path (to_pcg_exp i rho)).
  set (body := fun (i0 : fin n) (rho' : PCG.env) =>
    PCG.update rho' wtmp_path
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho')).
  assert (Hval : value_at (PCG.seqfor body rho_init) wtmp_path = to_pcg_exp (CD.reduce f i e) rho).
  { apply (@reduce_loop_invariant _ _ f i e rho rho_init body); auto; try reflexivity; intros; reflexivity. }
  assert (Houtside : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. apply (@reduce_loop_outside _ _ f i e rho rho_init q body); auto; try reflexivity; intros; reflexivity. }
  set (vreduce := to_pcg_exp (CD.reduce f i e) rho).
  assert (Hval_loop : value_at (PCG.seqfor body rho_init) wtmp_path = vreduce).
  { unfold vreduce. exact Hval. }
  assert (Houtside_loop : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { apply Houtside. }
  assert (Hloop_some : PCG.seqfor body rho_init wtmp_path = Some (value_at (PCG.seqfor body rho_init) wtmp_path)).
  { induction n as [| n' IHn].
    - simpl. unfold rho_init. unfold PCG.update, value_at. reflexivity.
    - rewrite seqfor_S. unfold PCG.seq. simpl. unfold PCG.update, value_at. reflexivity. }
  assert (Hassign_idem : PCG.assign wtmp_acc vreduce (PCG.seqfor body rho_init) = PCG.seqfor body rho_init).
  { apply functional_extensionality. intro q.
    destruct (classic (q = wtmp_path)) as [Heq | Hne].
    - subst q. simpl. rewrite PCG.update_eq. rewrite Hloop_some. f_equal. symmetry. exact Hval_loop.
    - simpl. rewrite PCG.update_neq by (intro Hc; apply Hne; symmetry; exact Hc). reflexivity. }
  Opaque PCG.seqfor PCG.assign.
  simpl. unfold PCG.seq. simpl. fold rho_init. fold body.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  fold body. fold rho_init.
  Transparent PCG.seqfor PCG.assign.
  assert (Hrho_loop_agree : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho q).
  { intros q Hq. rewrite Houtside_loop by exact Hq. unfold rho_init. apply PCG.update_neq. intro Hc. apply Hq. auto. }
  unfold PCG.vrm.
  destruct (classic (p = wtmp_path)) as [Hp | Hp].
  - subst p. rewrite remove_eq.
    apply PCG.StructUndefined_implies_None with (a := wtmp_acc).
    + apply Hstruct. exact Hundef.
    + simpl. auto.
  - rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
    rewrite <- Hassign_idem.
    symmetry. apply Hcont.
    + reflexivity.
    + intros q Hq. specialize (Hrho_loop_agree q).
      assert (Hq' : q <> wtmp_path) by (intro Hc; apply Hq; simpl; auto).
      specialize (Hrho_loop_agree Hq'). exact Hrho_loop_agree.
    + intro Hc. apply Hp. simpl in Hc; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Helpers for closing [eval_creduce_equiv_gen]: re-assigning the final value
   to the temporary region is a no-op when the loop already stored it.      *)
(* -------------------------------------------------------------------------- *)

(* Assigning a vector value to a vector acceptor is the pointwise sequential
   loop over matching elements. *)
Lemma PCG_assign_mk_vec_pair : forall n (f : fle n) d
    (g : fin (fle2nat f) -> DE.acc d) (h : fin (fle2nat f) -> PCG.exp d) (rho : PCG.env),
  @PCG.assign (ary f d) (V.mk_vec g) (V.mk_vec h) rho =
  PCG.seqfor (fun i : fin (fle2nat f) => @PCG.assign d (g i) (h i)) rho.
Proof.
  intros n f d g h rho.
  rewrite PCG_assign_ary. f_equal.
  apply functional_extensionality. intro i.
  rewrite PCG_idxAcc_mk_vec. rewrite PCG_idx_mk_vec. reflexivity.
Qed.

(* If only iteration [i] of a [seqfor] touches [q], the result at [q] is that
   iteration's write. *)
Lemma seqfor_single_touch : forall n (F : fin n -> PCG.comm) (eta : PCG.env) (q : path)
    (i : fin n) (val : option R),
  (forall j rho', j <> i -> F j rho' q = rho' q) ->
  (forall rho', F i rho' q = val) ->
  PCG.seqfor F eta q = val.
Proof.
  induction n as [| n' IHn]; intros F eta q i val Hother Hthis.
  - destruct i as [k Hk]. exfalso. lia.
  - rewrite seqfor_S. unfold PCG.seq.
    destruct (fin_case i) as [[i' Hi'] | Hi']; subst i.
    + (* i = FS[i']: the last iteration preserves [q] *)
      rewrite (Hother (ltS n')).
      * apply (IHn _ _ _ i').
        -- intros j rho' Hj. apply Hother. intro Hc. apply Hj.
           apply fin_eq.
           apply (f_equal fin2nat) in Hc. rewrite !fin2nat_fin2finS in Hc. exact Hc.
        -- intros rho'. apply Hthis.
      * intro Hc.
        assert (Heq : fin2nat (ltS n') = fin2nat (fin2finS i')) by (rewrite Hc; reflexivity).
        rewrite fin2nat_ltS, fin2nat_fin2finS in Heq.
        pose proof (fin_correct i') as Hlt. lia.
    + (* i = last: the result is its write *)
      apply Hthis.
Qed.

(* Reading back the value that [eta] itself stores in the [CG.vwt d s] region
   and assigning it again does not change [eta] at region paths (the region
   must be defined). *)
Lemma assign_vwt_readback_id : forall d (s : string),
  (s <> "0")%string -> (s <> "1")%string ->
  forall (eta : PCG.env) (q : path),
    @PCG.in_acc d q (@CG.vwt d s) ->
    eta q <> None ->
    PCG.assign (@CG.vwt d s) (to_pcg_exp (@CG.vrd d s) eta) eta q = eta q.
Proof.
  induction d as [| n f d' IHd]; intros s Hs0 Hs1 eta q Hin Hdef.
  - rewrite vwt_num in Hin. simpl in Hin. subst q.
    rewrite vrd_num, vwt_num, PCG_assign_num.
    rewrite (proj2 (String.eqb_neq s "0") Hs0).
    rewrite (proj2 (String.eqb_neq s "1") Hs1).
    rewrite to_pcg_exp_REvar, PCG.update_eq.
    destruct (eta (DE.Var s)) as [r | ] eqn:Eq.
    + reflexivity.
    + contradiction.
  - rewrite vwt_ary in Hin. simpl in Hin. destruct Hin as [i Hi].
    rewrite PCG_idxAcc_mk_vec in Hi.
    rewrite vrd_ary, vwt_ary, to_pcg_exp_ary, PCG_assign_mk_vec_pair.
    apply seqfor_single_touch with (i := i).
    + (* other iterations write other indexed names *)
      intros j rho' Hji.
      apply PCG.assign_not_in_acc.
      intro Hc.
      destruct (in_acc_vwt _ _ _ Hc) as [u Hu].
      destruct (in_acc_vwt _ _ _ Hi) as [w Hw].
      rewrite Hu in Hw. injection Hw as Hw.
      assert (Hfin : fin2nat j <> fin2nat i).
      { intro Heq. apply Hji. apply fin_eq. exact Heq. }
      exact (tmp_idx_neq2 s Hfin u w Hw).
    + (* iteration i writes back exactly [eta q] *)
      intro rho'.
      rewrite V.v_nth_mk_vec with (H := fin_proof i).
      rewrite nat2fin_fin2nat.
      rewrite (assign_in_acc_independent_of_env d' (@CG.vwt d' _)
        (to_pcg_exp (@CG.vrd d' _) eta) rho' eta q Hi).
      apply (IHd _ (indexed_name_neq_0 _ _) (indexed_name_neq_1 _ _) eta q Hi Hdef).
Qed.

(* If some iteration of a [seqfor] writes [Some] at [q] and every iteration
   either writes [Some] or preserves [q], the final value at [q] is [Some]. *)
Lemma seqfor_exists_Some : forall n (F : fin n -> PCG.comm) (rho : PCG.env) (q : path),
  (exists i, forall rho', exists r, F i rho' q = Some r) ->
  (forall i rho', (exists r, F i rho' q = Some r) \/ F i rho' q = rho' q) ->
  exists r, PCG.seqfor F rho q = Some r.
Proof.
  induction n as [| n' IHn]; intros F rho q Hsome Hpres.
  - destruct Hsome as [i _]. destruct i as [k Hk]. exfalso. lia.
  - rewrite seqfor_S. unfold PCG.seq.
    destruct (Hpres (ltS n') (PCG.seqfor (fun i0 : fin n' => F (fin2finS i0)) rho))
      as [[r Hr] | Hkeep].
    + exists r. exact Hr.
    + destruct Hsome as [i Hi].
      destruct (fin_case i) as [[i' ->] | ->].
      * rewrite Hkeep.
        apply (IHn _ _ _).
        -- exists i'. exact Hi.
        -- intros i0 rho'. apply Hpres.
      * apply Hi.
Qed.

(* [assign] writes a defined value at every path inside its acceptor. *)
Lemma assign_in_acc_is_Some : forall d (a : acc d) (v : PCG.exp d) (rho : PCG.env) (q : path),
  @PCG.in_acc d q a -> exists r, PCG.assign a v rho q = Some r.
Proof.
  induction d as [| n f d' IHd]; simpl; intros a v rho q Hin.
  - subst. rewrite PCG.update_eq. eexists. reflexivity.
  - destruct Hin as [i Hi].
    apply (seqfor_exists_Some _ _).
    + exists i. intro rho'. apply (IHd (PCG.idxAcc a i) (PCG.idx v i) rho' q Hi).
    + intros i0 rho'.
      destruct (classic (@PCG.in_acc d' q (PCG.idxAcc a i0))) as [Hc | Hc].
      * left. apply (IHd (PCG.idxAcc a i0) (PCG.idx v i0) rho' q Hc).
      * right. apply PCG.assign_not_in_acc. exact Hc.
Qed.

(* A defined value at [q] stays defined through a [seqfor] whose iterations
   either preserve [q] or write a defined value. *)
Lemma seqfor_preserves_Some : forall n (F : fin n -> PCG.comm) (rho : PCG.env) (q : path) (r : R),
  rho q = Some r ->
  (forall i rho', F i rho' q = rho' q \/ (exists r', F i rho' q = Some r')) ->
  exists r', PCG.seqfor F rho q = Some r'.
Proof.
  induction n as [| n' IHn]; intros F rho q r Hr Hstep.
  - simpl. exists r. exact Hr.
  - rewrite seqfor_S. unfold PCG.seq.
    destruct (Hstep (ltS n') (PCG.seqfor (fun i0 : fin n' => F (fin2finS i0)) rho))
      as [Hkeep | [r' Hr']].
    + rewrite Hkeep. apply (IHn _ _ _ _ Hr).
      intros i0 rho'. apply Hstep.
    + exists r'. exact Hr'.
Qed.

(* Generalized semantic correctness of the continuation variant of [reduce]
   for an arbitrary accumulator type [d2].  The proof follows the scalar
   [eval_creduce_equiv] but uses the generic loop lemmas. *)
Theorem eval_creduce_equiv_gen :
  forall n d1 d2 (f : exp d1 -> exp d2 -> exp d2) (i : exp d2)
         (e : exp (ary '{n} d1)) (c : exp d2 -> CG.comm) (rho : PCG.env),
    reduce_op_proper f ->
    @PCG.StructUndefined d2 (@CG.vwt d2 "__tmp") rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e (@CG.vwt d2 "__tmp") ->
    loopacc_continuation_ok c (CD.reduce f i e) ->
    eval_aux (c (CD.reduce f i e)) 1 rho =
    eval (@CG.loopacc d2 (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, i),
        CG.seq (CG.seqfor (fun i0 => CG.assign (w, f (DE.idx e i0) v)),
          c v)))) rho.
Proof.
  intros n d1 d2 f i e c rho Hf Hundef Hindep Hok.
  set (wtmp := @CG.vwt d2 "__tmp") in *.
  destruct Hok as [Hstruct Hcont].
  apply functional_extensionality. intro p.
  unfold eval at 1. simpl.
  set (rho_init := PCG.assign (@CG.vwt d2 "__tmp") (to_pcg_exp i rho) rho).
  set (body := fun (i0 : fin n) (rho' : PCG.env) =>
    PCG.assign (@CG.vwt d2 "__tmp")
      (to_pcg_exp (f (DE.idx e i0) (CG.vrd "__tmp")) rho') rho').
  assert (Hval : to_pcg_exp (@CG.vrd d2 "__tmp") (PCG.seqfor body rho_init) =
                 to_pcg_exp (CD.reduce f i e) rho).
  { apply (@reduce_loop_invariant_gen _ _ _ f i e rho rho_init body); auto;
      try reflexivity; intros; reflexivity. }
  assert (Houtside : forall q, ~ @PCG.in_acc d2 q wtmp ->
    PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. apply (@reduce_loop_outside_gen _ _ _ f i e rho rho_init q body); auto;
      try reflexivity; intros; reflexivity. }
  set (vreduce := to_pcg_exp (CD.reduce f i e) rho).
  assert (Hrho_loop_agree : forall q, ~ @PCG.in_acc d2 q wtmp ->
    PCG.seqfor body rho_init q = rho q).
  { intros q Hq. rewrite Houtside by exact Hq. unfold rho_init.
    (* The initial assignment to [CG.vwt "__tmp"] only touches paths inside
       the temporary region [wtmp]. *)
    apply PCG.assign_not_in_acc. exact Hq. }
  assert (Hassign_idem : PCG.assign wtmp vreduce (PCG.seqfor body rho_init) =
                         PCG.seqfor body rho_init).
  { (* The loop result already stores [vreduce] at [wtmp]; re-assigning it
       is a no-op. *)
    apply functional_extensionality. intro q.
    destruct (classic (@PCG.in_acc d2 q wtmp)) as [Hqin | Hqout].
    - assert (Hdef : PCG.seqfor body rho_init q <> None).
      { unfold rho_init.
        assert (Hsome0 : exists r, PCG.assign (@CG.vwt d2 "__tmp") (to_pcg_exp i rho) rho q = Some r).
        { apply assign_in_acc_is_Some. exact Hqin. }
        destruct Hsome0 as [r0 Hr0].
        assert (Hpres : (forall i0 rho', body i0 rho' q = rho' q \/
                          (exists r', body i0 rho' q = Some r'))).
        { intros i0 rho''. unfold body.
          destruct (classic (@PCG.in_acc d2 q (@CG.vwt d2 "__tmp"))) as [Hin2 | Hout2].
          + right. apply assign_in_acc_is_Some. exact Hin2.
          + left. apply PCG.assign_not_in_acc. exact Hout2. }
        destruct (seqfor_preserves_Some _ _ Hr0 Hpres) as [r1 Hr1].
        rewrite Hr1. discriminate. }
      unfold vreduce. rewrite <- Hval. unfold wtmp.
      apply assign_vwt_readback_id; [ discriminate | discriminate | exact Hqin | exact Hdef ].
    - apply PCG.assign_not_in_acc. exact Hqout. }
  unfold PCG.seq. fold rho_init. fold body.
  destruct (classic (@PCG.in_acc d2 p wtmp)) as [Hp | Hp].
  - (* Path [p] is inside the temporary region.  The continuation preserves
       undefinedness of [wtmp] by [loopacc_continuation_ok]; [loopacc] removes
       [p] with [vrm]. *)
    assert (Hlhs : eval_aux (c (CD.reduce f i e)) 1 rho p = None).
    { apply PCG.StructUndefined_implies_None with (a := wtmp); auto. }
    rewrite Hlhs. symmetry. apply PCG.vrm_in_acc. exact Hp.
  - (* Path [p] is outside the temporary region; [vrm] is the identity there. *)
    assert (Hvrm : PCG.vrm wtmp (eval_aux (c (CG.vrd "__tmp")) 1 (PCG.seqfor body rho_init)) p =
                   eval_aux (c (CG.vrd "__tmp")) 1 (PCG.seqfor body rho_init) p).
    { apply PCG.vrm_not_in_acc. exact Hp. }
    unfold wtmp in Hvrm. rewrite Hvrm.
    rewrite <- Hassign_idem.
    symmetry. apply Hcont.
    + reflexivity.
    + intros q Hq. apply Hrho_loop_agree. exact Hq.
    + exact Hp.
Qed.

Theorem eval_max_equiv :
  forall n (e : exp (ary '{n} num)) (a : acc num) (rho : PCG.env),
    @PCG.StructUndefined num wtmp_acc rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp_acc ->
    a <> wtmp_acc ->
    eval (CG.assign (a, CD.max e)) rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, CD.zero),
        CG.seq (CG.seqfor (fun i0 =>
                  CG.If (CD.gtExp (DE.idx e i0) v)
                        (CG.assign (w, DE.idx e i0), CG.assign (w, v))),
          CG.assign (a, v))))) rho.
Proof.
  intros n e a rho Hundef Hindep Hneq.
  apply PCG.StructUndefined_num in Hundef.
  assert (Ha : a <> wtmp_path) by (intro Hc; apply Hneq; simpl; rewrite Hc; reflexivity).
  apply functional_extensionality. intro p.
  rewrite eval_assign.
  unfold eval at 1.
  simpl.
  unfold PCG.seq.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  set (rho_init := PCG.update rho wtmp_path (to_pcg_exp CD.zero rho)).
  match goal with
  | [ |- context[PCG.seqfor ?f rho_init] ] =>
      set (body := f)
  end.
  assert (Hrho_init : rho_init = PCG.update rho wtmp_path R0).
  { unfold rho_init. rewrite to_pcg_exp_zero. reflexivity. }
  assert (Hbody_update : forall i0 rho', body i0 rho' = PCG.update rho' wtmp_path
    (if eval_bexp (fun s => match rho' (Var s) with Some r => r | None => R0 end)
        (CD.gtExp e|[i0] (CG.vrd "__tmp"))
     then to_pcg_exp e|[i0] rho'
     else value_at rho' wtmp_path)).
  { intros i0 rho'. unfold body. unfold PCG.If. unfold PCG.assign.
    rewrite <- update_if_distribute.
    rewrite to_pcg_exp_REvar_tmp'. reflexivity. }
  assert (Hval : value_at (PCG.seqfor body rho_init) wtmp_path = to_pcg_exp (CD.max e) rho).
  { rewrite Hrho_init. apply max_loop_invariant; [reflexivity | | exact Hindep].
    intros i rho'. rewrite Hbody_update. reflexivity. }
  assert (Houtside : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. rewrite Hrho_init.
    apply (max_loop_outside e rho _ _ body); [auto | reflexivity |].
    intros i rho'. rewrite Hbody_update. reflexivity. }
  unfold PCG.seq. fold rho_init. fold body.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  fold body. fold rho_init.
  try rewrite (to_pcg_exp_REvar_tmp' (PCG.seqfor body rho_init)).
  rewrite Hval.
  destruct (path_eqb wtmp_path p) eqn:Etmp.
  - apply path_eqb_eq in Etmp. subst p.
    rewrite PCG.update_neq by exact Ha.
    rewrite Hundef. rewrite remove_eq. reflexivity.
  - assert (Hp : p <> wtmp_path) by (intro Hc; rewrite Hc in Etmp; discriminate).
    destruct (path_eqb a p) eqn:Ea.
    + apply path_eqb_eq in Ea. subst p.
      rewrite remove_neq by (intro Hc; apply Ha; symmetry; exact Hc).
      rewrite (PCG.update_eq rho a (to_pcg_exp (CD.max e) rho)).
      rewrite (PCG.update_eq (PCG.seqfor body rho_init) a (to_pcg_exp (CD.max e) rho)). reflexivity.
    + assert (Hp2 : (a : path) <> p).
      { intro Hc. apply path_eqb_eq in Hc. rewrite Hc in Ea. discriminate. }
      rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
      assert (Hupd1 : PCG.update rho a (to_pcg_exp (CD.max e) rho) p = rho p)
        by (apply PCG.update_neq; exact Hp2).
      assert (Hupd2 : PCG.update (PCG.seqfor body rho_init) a (to_pcg_exp (CD.max e) rho) p = (PCG.seqfor body rho_init) p)
        by (apply PCG.update_neq; exact Hp2).
      rewrite Hupd1. rewrite Hupd2.
      rewrite Houtside by exact Hp.
      unfold rho_init. rewrite PCG.update_neq by (intro Hc; apply Hp; symmetry; exact Hc).
      reflexivity.
Qed.

Theorem eval_cmax_equiv :
  forall n (e : exp (ary '{n} num)) (c : exp num -> CG.comm) (rho : PCG.env),
    @PCG.StructUndefined num wtmp_acc rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp_acc ->
    loopacc_continuation_ok c (CD.max e) ->
    eval_aux (c (CD.max e)) 1 rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, CD.zero),
        CG.seq (CG.seqfor (fun i0 =>
                  CG.If (CD.gtExp (DE.idx e i0) v)
                        (CG.assign (w, DE.idx e i0), CG.assign (w, v))),
          c v)))) rho.
Proof.
  intros n e c rho Hundef Hindep Hok.
  apply PCG.StructUndefined_num in Hundef.
  destruct Hok as [Hstruct Hcont].
  apply functional_extensionality. intro p.
  unfold eval at 1.
  simpl.
  unfold PCG.seq.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  set (rho_init := PCG.update rho wtmp_path (to_pcg_exp CD.zero rho)).
  match goal with
  | [ |- context[PCG.seqfor ?f rho_init] ] =>
      set (body := f)
  end.
  assert (Hrho_init : rho_init = PCG.update rho wtmp_path R0).
  { unfold rho_init. rewrite to_pcg_exp_zero. reflexivity. }
  assert (Hbody_cond : forall i rho', body i rho' = PCG.update rho' wtmp_path
    (if eval_bexp (fun s => match rho' (Var s) with Some r => r | None => R0 end)
        (CD.gtExp e|[i] (CG.vrd "__tmp"))
     then to_pcg_exp e|[i] rho'
     else value_at rho' wtmp_path)).
  { intros i rho'. unfold body, PCG.If. simpl.
    rewrite <- update_if_distribute.
    rewrite to_pcg_exp_REvar_tmp'. reflexivity. }
  assert (Hval : value_at (PCG.seqfor body rho_init) wtmp_path = to_pcg_exp (CD.max e) rho).
  { rewrite Hrho_init. apply max_loop_invariant; auto. }
  assert (Houtside : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. rewrite Hrho_init.
    apply (max_loop_outside e rho _ _ body).
    - auto.
    - reflexivity.
    - intros i rho'. rewrite Hbody_cond. reflexivity. }
  set (vmax := to_pcg_exp (CD.max e) rho).
  assert (Hval_loop : value_at (PCG.seqfor body rho_init) wtmp_path = vmax).
  { unfold vmax. exact Hval. }
  assert (Houtside_loop : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { apply Houtside. }
  assert (Hloop_some : PCG.seqfor body rho_init wtmp_path = Some (value_at (PCG.seqfor body rho_init) wtmp_path)).
  { induction n as [| n' IHn].
    - simpl. unfold rho_init. unfold PCG.update, value_at. reflexivity.
    - rewrite seqfor_S. unfold PCG.seq.
      rewrite Hbody_cond with (i := ltS n')
        (rho' := PCG.seqfor (fun i : fin n' => body FS[i]) rho_init).
      simpl. unfold PCG.update, value_at. reflexivity. }
  assert (Hassign_idem : PCG.assign wtmp_acc vmax (PCG.seqfor body rho_init) = PCG.seqfor body rho_init).
  { apply functional_extensionality. intro q.
    destruct (classic (q = wtmp_path)) as [Heq | Hne].
    - subst q. simpl. rewrite PCG.update_eq. rewrite Hloop_some. f_equal. symmetry. exact Hval_loop.
    - simpl. rewrite PCG.update_neq by (intro Hc; apply Hne; symmetry; exact Hc). reflexivity. }
  Opaque PCG.seqfor PCG.assign.
  simpl. unfold PCG.seq. simpl. fold rho_init.
  Transparent PCG.seqfor PCG.assign.
  assert (Hrho_loop_agree : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho q).
  { intros q Hq. rewrite Houtside_loop by exact Hq. unfold rho_init. apply PCG.update_neq. intro Hc. apply Hq. auto. }
  unfold PCG.vrm.
  destruct (classic (p = wtmp_path)) as [Hp | Hp].
  - subst p. rewrite remove_eq.
    apply PCG.StructUndefined_implies_None with (a := wtmp_acc).
    + apply Hstruct. exact Hundef.
    + simpl. auto.
  - rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
    rewrite <- Hassign_idem.
    symmetry. apply Hcont.
    + reflexivity.
    + intros q Hq. specialize (Hrho_loop_agree q).
      assert (Hq' : q <> wtmp_path) by (intro Hc; apply Hq; simpl; auto).
      specialize (Hrho_loop_agree Hq'). exact Hrho_loop_agree.
    + intro Hc. apply Hp. simpl in Hc; auto.
Qed.

Theorem eval_sum_equiv :
  forall n (e : exp (ary '{n} num)) (a : acc num) (rho : PCG.env),
    @PCG.StructUndefined num wtmp_acc rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp_acc ->
    a <> wtmp_acc ->
    eval (CG.assign (a, CD.sum e)) rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, CD.zero),
        CG.seq (CG.seqfor (fun i0 => CG.assign (w, CD.add (DE.idx e i0) v)),
          CG.assign (a, v))))) rho.
Proof.
  intros n e a rho Hundef Hindep Hneq.
  apply PCG.StructUndefined_num in Hundef.
  assert (Ha : a <> wtmp_path) by (intro Hc; apply Hneq; simpl; rewrite Hc; reflexivity).
  apply functional_extensionality. intro p.
  rewrite eval_assign.
  unfold eval at 1.
  simpl.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  set (rho_init := PCG.update rho wtmp_path (to_pcg_exp CD.zero rho)).
  set (body := fun (i : fin n) (rho' : PCG.env) =>
    PCG.update rho' wtmp_path
      (Rplus (to_pcg_exp (DE.idx e i) rho') (value_at rho' wtmp_path))).
  assert (Hrho_init : rho_init = PCG.update rho wtmp_path R0).
  { unfold rho_init. rewrite to_pcg_exp_zero. reflexivity. }
  assert (Hval_raw : value_at (PCG.seqfor body rho_init) wtmp_path = Rplus R0 (to_pcg_exp (CD.sum e) rho)).
  { rewrite Hrho_init. apply sum_loop_invariant; auto. }
  assert (Hval : value_at (PCG.seqfor body rho_init) wtmp_path = to_pcg_exp (CD.sum e) rho).
  { rewrite Hval_raw. rewrite Rplus_0_l. reflexivity. }
  assert (Houtside : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. rewrite Hrho_init.
    apply (sum_loop_outside (rho:=rho) (acc0:=R0) e body); auto; try reflexivity. }
  assert (Hpoint : forall i : fin n,
    (fun (i0 : fin n) (rho' : PCG.env) =>
      PCG.update rho' wtmp_path (to_pcg_exp (CD.add e|[i0] (CG.vrd "__tmp")) rho')) i =
    body i).
  { intro i. apply functional_extensionality. intro rho'.
    rewrite to_pcg_exp_add. rewrite to_pcg_exp_REvar_tmp'. reflexivity. }
  rewrite (PCG.seqfor_extensionality _ _ Hpoint).
  simpl. unfold PCG.seq. fold rho_init. fold body.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  fold body. fold rho_init.
  try rewrite (to_pcg_exp_REvar_tmp' (PCG.seqfor body rho_init)).
  rewrite Hval.
  destruct (path_eqb wtmp_path p) eqn:Etmp.
  - apply path_eqb_eq in Etmp. subst p.
    rewrite PCG.update_neq by exact Ha.
    rewrite Hundef. rewrite remove_eq. reflexivity.
  - assert (Hp : p <> wtmp_path) by (intro Hc; rewrite Hc in Etmp; discriminate).
    destruct (path_eqb a p) eqn:Ea.
    + apply path_eqb_eq in Ea. subst p.
      rewrite remove_neq by (intro Hc; apply Ha; symmetry; exact Hc).
      rewrite (PCG.update_eq rho a (to_pcg_exp (CD.sum e) rho)).
      rewrite (PCG.update_eq (PCG.seqfor body rho_init) a (to_pcg_exp (CD.sum e) rho)). reflexivity.
    + assert (Hp2 : (a : path) <> p).
      { intro Hc. apply path_eqb_eq in Hc. rewrite Hc in Ea. discriminate. }
      rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
      assert (Hupd1 : PCG.update rho a (to_pcg_exp (CD.sum e) rho) p = rho p)
        by (apply PCG.update_neq; exact Hp2).
      assert (Hupd2 : PCG.update (PCG.seqfor body rho_init) a (to_pcg_exp (CD.sum e) rho) p = (PCG.seqfor body rho_init) p)
        by (apply PCG.update_neq; exact Hp2).
      rewrite Hupd1. rewrite Hupd2.
      rewrite Houtside by exact Hp.
      unfold rho_init. rewrite PCG.update_neq by (intro Hc; apply Hp; symmetry; exact Hc).
      reflexivity.
Qed.

Theorem eval_csum_equiv :
  forall n (e : exp (ary '{n} num)) (c : exp num -> CG.comm) (rho : PCG.env),
    @PCG.StructUndefined num wtmp_acc rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp_acc ->
    loopacc_continuation_ok c (CD.sum e) ->
    eval_aux (c (CD.sum e)) 1 rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      CG.seq (CG.assign (w, CD.zero),
        CG.seq (CG.seqfor (fun i0 => CG.assign (w, CD.add (DE.idx e i0) v)),
          c v)))) rho.
Proof.
  intros n e c rho Hundef Hindep Hok.
  apply PCG.StructUndefined_num in Hundef.
  destruct Hok as [Hstruct Hcont].
  apply functional_extensionality. intro p.
  unfold eval at 1.
  simpl.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  set (rho_init := PCG.update rho wtmp_path (to_pcg_exp CD.zero rho)).
  set (body := fun (i : fin n) (rho' : PCG.env) =>
    PCG.update rho' wtmp_path
      (Rplus (to_pcg_exp (DE.idx e i) rho') (value_at rho' wtmp_path))).
  assert (Hrho_init : rho_init = PCG.update rho wtmp_path R0).
  { unfold rho_init. rewrite to_pcg_exp_zero. reflexivity. }
  assert (Hval_raw : value_at (PCG.seqfor body rho_init) wtmp_path = Rplus R0 (to_pcg_exp (CD.sum e) rho)).
  { rewrite Hrho_init. apply sum_loop_invariant; auto. }
  assert (Hval : value_at (PCG.seqfor body rho_init) wtmp_path = to_pcg_exp (CD.sum e) rho).
  { rewrite Hval_raw. rewrite Rplus_0_l. reflexivity. }
  assert (Houtside : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq. rewrite Hrho_init.
    apply (sum_loop_outside (rho:=rho) (acc0:=R0) e body); auto; try reflexivity. }
  assert (Hpoint : forall i : fin n,
    (fun (i0 : fin n) (rho' : PCG.env) =>
      PCG.update rho' wtmp_path (to_pcg_exp (CD.add (DE.idx e i0) (CG.vrd "__tmp")) rho')) i =
    body i).
  { intro i. apply functional_extensionality. intro rho'.
    rewrite to_pcg_exp_add. rewrite to_pcg_exp_REvar_tmp'. reflexivity. }
  rewrite (PCG.seqfor_extensionality _ _ Hpoint).
  set (vsum := to_pcg_exp (CD.sum e) rho).
  assert (Hval_loop : value_at (PCG.seqfor body rho_init) wtmp_path = vsum).
  { unfold vsum. exact Hval. }
  assert (Houtside_loop : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho_init q).
  { apply Houtside. }
  assert (Hloop_some : PCG.seqfor body rho_init wtmp_path = Some (value_at (PCG.seqfor body rho_init) wtmp_path)).
  { induction n as [| n' IHn].
    - simpl. unfold rho_init. unfold PCG.update, value_at. reflexivity.
    - rewrite seqfor_S. unfold PCG.seq. simpl. unfold PCG.update, value_at. reflexivity. }
  assert (Hassign_idem : PCG.assign wtmp_acc vsum (PCG.seqfor body rho_init) = PCG.seqfor body rho_init).
  { apply functional_extensionality. intro q.
    destruct (classic (q = wtmp_path)) as [Heq | Hne].
    - subst q. simpl. rewrite PCG.update_eq. rewrite Hloop_some. f_equal. symmetry. exact Hval_loop.
    - simpl. rewrite PCG.update_neq by (intro Hc; apply Hne; symmetry; exact Hc). reflexivity. }
  Opaque PCG.seqfor PCG.assign.
  simpl. unfold PCG.seq. simpl. fold rho_init. fold body.
  change (CG.vwt "__tmp") with wtmp_path in |- *.
  fold body. fold rho_init.
  Transparent PCG.seqfor PCG.assign.
  assert (Hrho_loop_agree : forall q, q <> wtmp_path -> PCG.seqfor body rho_init q = rho q).
  { intros q Hq. rewrite Houtside_loop by exact Hq. unfold rho_init. apply PCG.update_neq. intro Hc. apply Hq. auto. }
  unfold PCG.vrm.
  destruct (classic (p = wtmp_path)) as [Hp | Hp].
  - subst p. rewrite remove_eq.
    apply PCG.StructUndefined_implies_None with (a := wtmp_acc).
    + apply Hstruct. exact Hundef.
    + simpl. auto.
  - rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
    rewrite <- Hassign_idem.
    symmetry. apply Hcont.
    + reflexivity.
    + intros q Hq. specialize (Hrho_loop_agree q).
      assert (Hq' : q <> wtmp_path) by (intro Hc; apply Hq; simpl; auto).
      specialize (Hrho_loop_agree Hq'). exact Hrho_loop_agree.
    + intro Hc. apply Hp. simpl in Hc; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Depth-shifted (named) variant of [eval_csum_equiv]: the accumulator        *)
(* temporary is [tmp_name depth] instead of ["__tmp"], so the rule applies    *)
(* inside nested [loopacc] bodies (e.g. ["__tmp_"] at depth 1).               *)
(* -------------------------------------------------------------------------- *)

(* [tmp_name] always starts with the underscore character. *)
Lemma tmp_name_head_underscore : forall depth,
  exists s', tmp_name depth = ("_" ++ s')%string.
Proof.
  induction depth as [|d [s' IH]]; simpl.
  - exists "_tmp"%string. reflexivity.
  - exists (s' ++ "_")%string. rewrite IH. rewrite append_assoc_str. reflexivity.
Qed.

Lemma tmp_name_neq_0 : forall depth, (tmp_name depth <> "0")%string.
Proof.
  intros depth H. destruct (tmp_name_head_underscore depth) as [s' Hs].
  rewrite Hs in H. discriminate H.
Qed.

Lemma tmp_name_neq_1 : forall depth, (tmp_name depth <> "1")%string.
Proof.
  intros depth H. destruct (tmp_name_head_underscore depth) as [s' Hs].
  rewrite Hs in H. discriminate H.
Qed.

(* Reading a scalar temporary by name yields the stored value. *)
Lemma to_pcg_exp_vrd_num_value : forall (s : string) (rho : PCG.env),
  (s <> "0")%string -> (s <> "1")%string ->
  to_pcg_exp (@CG.vrd num s) rho = (value_at rho (DE.Var s) : PCG.exp num).
Proof.
  intros s rho Hs0 Hs1. rewrite vrd_num.
  rewrite (proj2 (String.eqb_neq s "0") Hs0).
  rewrite (proj2 (String.eqb_neq s "1") Hs1).
  rewrite to_pcg_exp_REvar. unfold value_at. reflexivity.
Qed.

Lemma to_pcg_exp_vrd_tmp_name : forall depth (rho : PCG.env),
  to_pcg_exp (@CG.vrd num (tmp_name depth)) rho =
  (value_at rho (DE.Var (tmp_name depth)) : PCG.exp num).
Proof.
  intros depth rho. apply to_pcg_exp_vrd_num_value.
  - apply tmp_name_neq_0.
  - apply tmp_name_neq_1.
Qed.

(* A scalar read by name only depends on the environment at that name. *)
Lemma to_pcg_exp_vrd_num_var : forall (s : string) (rho1 rho2 : PCG.env),
  rho1 (DE.Var s) = rho2 (DE.Var s) ->
  to_pcg_exp (@CG.vrd num s) rho1 = to_pcg_exp (@CG.vrd num s) rho2.
Proof.
  intros s rho1 rho2 H. rewrite !vrd_num.
  destruct (String.eqb s "0") eqn:E0.
  - reflexivity.
  - destruct (String.eqb s "1") eqn:E1.
    + reflexivity.
    + rewrite !to_pcg_exp_REvar. rewrite H. reflexivity.
Qed.

(* [loopacc_continuation_ok] at an arbitrary naming depth: on the functional
   side the continuation [c] runs at [depth], while inside the [loopacc] body
   it runs at [S depth] on the freshly assigned accumulator. *)
Definition loopacc_continuation_ok_at (name : string) (depth : nat) {d}
    (c : exp d -> CG.comm) (e_final : exp d) : Prop :=
  let wtmp := CG.vwt name in
  (forall rho, @PCG.StructUndefined d wtmp rho ->
               @PCG.StructUndefined d wtmp (eval_aux (c e_final) depth rho)) /\
  (forall rho eta (v : PCG.exp d),
     to_pcg_exp e_final rho = v ->
     (forall q, ~ @PCG.in_acc d q wtmp -> eta q = rho q) ->
     forall p, ~ @PCG.in_acc d p wtmp ->
       eval_aux (c (CG.vrd name)) (S depth) (PCG.assign wtmp v eta) p =
       eval_aux (c e_final) depth rho p).

(* The continuation variant of [sum] evaluated at an arbitrary naming depth.
   The proof mirrors [eval_csum_equiv], using the path-parameterised loop
   lemmas [sum_loop_invariant_path]/[sum_loop_outside_path]. *)
Theorem eval_csum_equiv_at :
  forall (depth : nat) n (e : exp (ary '{n} num)) (c : exp num -> CG.comm) (rho : PCG.env),
    rho (DE.Var (tmp_name depth)) = None ->
    @exp_independent_of_acc (ary '{n} num) num e (@PCG.acc' num (DE.Var (tmp_name depth))) ->
    loopacc_continuation_ok_at (tmp_name depth) depth c (CD.sum e) ->
    eval_aux (c (CD.sum e)) depth rho =
    eval_aux (@CG.loopacc num (fun tmp =>
      CG.seq (CG.assign (CG.vwt tmp, CD.zero),
        CG.seq (CG.seqfor (fun i0 => CG.assign (CG.vwt tmp, CD.add (DE.idx e i0) (CG.vrd tmp))),
          c (CG.vrd tmp))))) depth rho.
Proof.
  intros depth n e c rho Hundef Hindep Hok.
  destruct Hok as [Hstruct Hcont].
  set (tmp_p := DE.Var (tmp_name depth)) in *.
  set (vsum := to_pcg_exp (CD.sum e) rho).
  set (body := fun (i0 : fin n) (rho' : PCG.env) =>
    PCG.update rho' tmp_p (Rplus (to_pcg_exp (DE.idx e i0) rho') (value_at rho' tmp_p))).
  apply functional_extensionality. intro p.
  rewrite eval_loopacc_aux. cbn beta.
  unfold PCG.seq. rewrite !eval_seq_aux. unfold PCG.seq.
  rewrite eval_assign_aux.
  change (@CG.vwt num (tmp_name depth)) with tmp_p.
  rewrite PCG_assign_num.
  set (rho_init := PCG.update rho tmp_p (to_pcg_exp CD.zero rho)).
  rewrite !eval_seq_aux. unfold PCG.seq. rewrite eval_seqfor_aux.
  assert (Hpoint : forall i0 : fin n,
    eval_aux (CG.assign ((tmp_p : DE.acc num), CD.add (DE.idx e i0) (CG.vrd (tmp_name depth)))) (S depth) =
    body i0).
  { intro i0. apply functional_extensionality. intro rho'.
    rewrite eval_assign_aux, PCG_assign_num, to_pcg_exp_add, to_pcg_exp_vrd_tmp_name.
    reflexivity. }
  rewrite (PCG.seqfor_extensionality _ _ Hpoint).
  assert (Hval : value_at (PCG.seqfor body rho_init) tmp_p = vsum).
  { assert (Hraw := @sum_loop_invariant_path n e rho (to_pcg_exp CD.zero rho) tmp_p
      rho_init body eq_refl (fun i rho' => eq_refl) Hindep).
    rewrite to_pcg_exp_zero, Rplus_0_l in Hraw. exact Hraw. }
  assert (Houtside : forall q, q <> tmp_p -> PCG.seqfor body rho_init q = rho_init q).
  { intros q Hq.
    apply (@sum_loop_outside_path n e rho (to_pcg_exp CD.zero rho) q tmp_p rho_init body);
      auto; try reflexivity. }
  assert (Hloop_some : PCG.seqfor body rho_init tmp_p = Some vsum).
  { assert (Hraw := @seqfor_sum_tmp_path_Some n e rho (to_pcg_exp CD.zero rho) tmp_p
      rho_init body eq_refl (fun i rho' => eq_refl) Hindep).
    rewrite to_pcg_exp_zero, Rplus_0_l in Hraw. exact Hraw. }
  assert (Hassign_idem :
    PCG.assign ((@CG.vwt num (tmp_name depth)) : PCG.acc num) vsum (PCG.seqfor body rho_init) =
    PCG.seqfor body rho_init).
  { apply functional_extensionality. intro q.
    destruct (classic (q = tmp_p)) as [Heq | Hne].
    - subst q. rewrite PCG_assign_num.
      change (@CG.vwt num (tmp_name depth)) with tmp_p.
      rewrite PCG.update_eq. rewrite Hloop_some. reflexivity.
    - rewrite PCG_assign_num.
      change (@CG.vwt num (tmp_name depth)) with tmp_p.
      rewrite PCG.update_neq by (intro Hc; apply Hne; symmetry; exact Hc).
      reflexivity. }
  unfold PCG.vrm.
  destruct (classic (p = tmp_p)) as [Hp | Hp].
  - subst p. rewrite remove_eq.
    apply PCG.StructUndefined_implies_None with (a := ((@CG.vwt num (tmp_name depth)) : PCG.acc num)).
    + apply Hstruct.
      apply (proj2 (PCG.StructUndefined_num _ _)).
      exact Hundef.
    + reflexivity.
  - rewrite remove_neq by (intro Hc; apply Hp; symmetry; exact Hc).
    rewrite <- Hassign_idem.
    symmetry. apply Hcont.
    + reflexivity.
    + intros q Hq.
      assert (Hq' : q <> tmp_p).
      { intro Hc. apply Hq. simpl. rewrite Hc. reflexivity. }
      rewrite (Houtside q Hq').
      unfold rho_init.
      rewrite PCG.update_neq by (intro Hc; apply Hq'; symmetry; exact Hc).
      reflexivity.
    + intro Hc. apply Hp. simpl in Hc. symmetry. exact Hc.
Qed.
