(* Semantic equivalence proofs for core CNN operators.

   This file proves that the functional specifications of Linear, Softmax,
   and GlobalAvgPool are semantically equivalent to their imperative ASTs in
   [Ionia.CNN_Examples_Base.v].  The proofs use the semantic interpreter
   [CNN_CodeGen_Semantics.eval] and the semantic combinator theorems from
   [Ionia.CNN_CodeGen_Combinators.v], avoiding the Leibniz (syntactic)
   equality goals that are still axioms in [Ionia.CNN_CodeGen.v].

   The operator ASTs here use [loopacc] for scalar accumulators, which makes
   the interpreter semantics match the generated C code. *)

From Stdlib Require Import Reals String Nat List Bool Arith Lra Lia.
From Stdlib Require Import Extraction.
From Stdlib Require Import Classical_Prop.
Require Import Ionia.FusionTactics.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.CNN_CodeGen_Combinators.
Require Ionia.Proof_CodeGen.
Require Ionia.DataExp.
Require Import Ionia.CNN_OP.
Require Import Ionia.CNN_Examples_Base_Ops.
Require Import Ionia.CNN_Examples_Base.
From Stdlib Require Import Logic.FunctionalExtensionality.
From Stdlib Require Import Eqdep.
Import ListNotations.
Set Implicit Arguments.
Open Scope string_scope.

Module PCG := Ionia.Proof_CodeGen.
Module DE := Ionia.DataExp.
Module CD := Ionia.CNN_Defs.
Module CG := Ionia.CNN_CodeGen.

Definition tmp_path : DE.path := DE.Var "__tmp".
Definition tmp_scalar_acc : acc num := (@PCG.acc' num tmp_path : acc num).

(* The semantic model uses [Proof_CodeGen.acc] while the AST uses
   [DataExp.acc]; the two are definitionally equal. *)
Definition as_PCG_acc {d} (a : acc d) : PCG.acc d := a.
Definition from_PCG_acc {d} (a : PCG.acc d) : acc d := a.
Coercion as_PCG_acc : acc >-> PCG.acc.

Lemma in_acc_tmp_scalar_acc : @PCG.in_acc num tmp_path tmp_scalar_acc.
Proof. simpl. reflexivity. Qed.

Opaque eval.

(* ------------------------------------------------------------------------ *)
(* Generic helpers                                                          *)
(* ------------------------------------------------------------------------ *)

Lemma exp_independent_of_acc_sum :
  forall n d' (e : exp (ary '{n} num)) (a : acc d'),
    (forall i, exp_independent_of_acc (DE.idx e i) a) ->
    exp_independent_of_acc (CD.sum e) a.
Proof.
  intros n d' e a Hin q Hq. apply exp_independent_path_sum. intros i.
  apply Hin. exact Hq.
Qed.

Lemma exp_independent_of_acc_REvar :
  forall (name : string) (d' : data) (a : acc d'),
    ~ @PCG.in_acc d' (DE.Var name) a ->
    exp_independent_of_acc (DE.REvar name : exp num) a.
Proof.
  intros name d' a Hna p Hp. simpl. intro Hc. apply Hna.
  rewrite Hc. exact Hp.
Qed.

Lemma exp_independent_of_acc_pExp :
  forall d' (x : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc (CD.pExp x) a.
Proof.
  intros d' x a Hin p Hp. simpl. apply Hin. exact Hp.
Qed.

Lemma exp_independent_of_acc_div :
  forall d' (x y : exp num) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc y a ->
    exp_independent_of_acc (CD.div x y) a.
Proof.
  intros d' x y a Hx Hy p Hp. simpl. split; [apply Hx | apply Hy]; exact Hp.
Qed.

Lemma exp_independent_of_acc_div_n :
  forall d' (x : exp num) (n : nat) (a : acc d'),
    exp_independent_of_acc x a ->
    exp_independent_of_acc (CD.div_n x n) a.
Proof.
  intros d' x n a Hin p Hp. simpl. apply Hin. exact Hp.
Qed.

Lemma exp_default_independent :
  forall t d' (a : acc d'), exp_independent_of_acc (DE.exp_default t) a.
Proof.
  induction t; intros d' a; simpl.
  - unfold exp_independent_of_acc. intros q Hq. simpl. auto.
  - apply exp_independent_of_acc_mkvSeq. intros i. apply IHt.
Qed.

Lemma safe_idx_nat_independent :
  forall n t d' (e : exp (ary '{n} t)) (i : nat) (a : acc d'),
    exp_independent_of_acc e a ->
    exp_independent_of_acc (safe_idx_nat e i) a.
Proof.
  intros n t d' e i a Hin. unfold safe_idx_nat.
  destruct (Nat.ltb_spec0 i n).
  - apply exp_independent_of_acc_idx. exact Hin.
  - apply exp_default_independent.
Qed.

Definition tmp_disjoint_from_acc {d} (a : acc d) : Prop :=
  forall p, @PCG.in_acc num p tmp_scalar_acc -> ~ @PCG.in_acc d p a.

Lemma assign_preserves_StructUndefined_tmp :
  forall (a : acc num) (e : exp num) rho,
    tmp_disjoint_from_acc a ->
    @PCG.StructUndefined num tmp_scalar_acc rho ->
    @PCG.StructUndefined num tmp_scalar_acc (PCG.assign a (to_pcg_exp e rho) rho).
Proof.
  intros a e rho Hdisj Hundef.
  simpl in Hundef |- *. unfold as_PCG_acc at 1.
  rewrite (@PCG.update_neq rho a tmp_scalar_acc (to_pcg_exp e rho)); [exact Hundef | ].
  intro Hc. apply (Hdisj tmp_scalar_acc in_acc_tmp_scalar_acc).
  simpl. auto.
Qed.

Lemma to_pcg_exp_mul :
  forall x y rho,
    to_pcg_exp (CD.mul x y) rho = Rmult (to_pcg_exp x rho) (to_pcg_exp y rho).
Proof. intros. unfold CD.mul. cbv [to_pcg_exp]. simpl. reflexivity. Qed.

Lemma to_pcg_exp_add :
  forall x y rho,
    to_pcg_exp (CD.add x y) rho = Rplus (to_pcg_exp x rho) (to_pcg_exp y rho).
Proof. intros. unfold CD.add. cbv [to_pcg_exp]. simpl. reflexivity. Qed.

Lemma eval_assign_depth_independent :
  forall d (a : acc d) (e : exp d) (rho : PCG.env) (depth : nat),
    eval_aux (CG.assign (a, e)) depth rho = eval (CG.assign (a, e)) rho.
Proof.
  intros. rewrite eval_assign_aux. rewrite eval_assign. reflexivity.
Qed.

Lemma to_pcg_exp_div :
  forall x y rho,
    to_pcg_exp (CD.div x y) rho = Rdiv (to_pcg_exp x rho) (to_pcg_exp y rho).
Proof. intros. unfold CD.div. cbv [to_pcg_exp]. simpl. reflexivity. Qed.

Lemma to_pcg_exp_pExp :
  forall x rho,
    to_pcg_exp (CD.pExp x) rho = Rtrigo_def.exp (to_pcg_exp x rho).
Proof. intros. unfold CD.pExp. cbv [to_pcg_exp]. simpl. reflexivity. Qed.

Lemma to_pcg_exp_div_n :
  forall x n rho,
    to_pcg_exp (CD.div_n x n) rho = Rdiv (to_pcg_exp x rho) (INR n).
Proof. intros. unfold CD.div_n. cbv [to_pcg_exp]. simpl. reflexivity. Qed.

(* A continuation that assigns [f r] to a scalar acceptor [a] disjoint from
   [__tmp] satisfies [loopacc_continuation_ok], provided the final expression
   [e_final] and the expression [f e_final] are independent of [__tmp], and
   [f] maps the tmp-read [vrd "__tmp"] and the functional result [e_final]
   to the same PCG value whenever [__tmp] holds that result. *)
Lemma scalar_assign_continuation_ok :
  forall (a : acc num) (f : exp num -> exp num) (e_final : exp num),
    tmp_disjoint_from_acc a ->
    exp_independent_of_acc e_final tmp_scalar_acc ->
    exp_independent_of_acc (f e_final) tmp_scalar_acc ->
    (forall rho eta (v : PCG.exp num),
       to_pcg_exp e_final rho = v ->
       (forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> eta q = rho q) ->
       to_pcg_exp (f (CG.vrd "__tmp")) (PCG.update eta tmp_path v) =
       to_pcg_exp (f e_final) rho) ->
    loopacc_continuation_ok (fun r : exp num => a |:= f r) e_final.
Proof.
  intros a f e_final Hdisj He_indep Hf_indep Hf_proper. split.
  - (* preservation of StructUndefined *)
    intros rho Hundef. rewrite eval_assign_aux.
    apply assign_preserves_StructUndefined_tmp; [exact Hdisj | exact Hundef].
  - (* behaviour matches functional result when tmp holds the result *)
    intros rho eta v Hv Heta p Hp.
    rewrite !eval_assign_aux. unfold PCG.assign. unfold as_PCG_acc in |- *.
    assert (Hupd : forall env val, PCG.update env a val p =
      if path_eqb a p then Some val else env p).
    { intros env val. unfold PCG.update. reflexivity. }
    rewrite !Hupd.
    destruct (path_eqb a p) eqn:E.
    + apply path_eqb_eq in E. subst p. f_equal.
      apply Hf_proper; assumption.
    + rewrite PCG.update_neq by (intro Hc; apply Hp; simpl; auto).
      apply Heta. intro Hc. apply Hp. simpl. auto.
Qed.

(* If [e] is independent of the output array, then its value in an environment
   [env] that holds [v] at [__tmp] and agrees with [rho] everywhere outside
   [__tmp] and outside the output cells equals its value in [rho] updated with
   [v] at [__tmp]. *)
Lemma eval_agree_outside_output_with_tmp :
  forall {d n} (e : exp d) (output : acc (ary '{n} num)) (env rho : PCG.env)
         (v : PCG.exp num),
    exp_independent_of_acc e output ->
    env tmp_path = Some v ->
    (forall q, ~ @PCG.in_acc num q tmp_scalar_acc ->
               (forall j, ~ @PCG.in_acc num q (output |{ j})) ->
               env q = rho q) ->
    to_pcg_exp e env = to_pcg_exp e (PCG.update rho tmp_path v).
Proof.
  intros d n e output env rho v Hin Htmp Hagree.
  apply exp_independent_of_acc_eval with (a := output); [ exact Hin | ].
  intros q Hq. destruct (path_eqb tmp_path q) eqn:Et.
  - apply path_eqb_eq in Et; subst q.
    rewrite PCG.update_eq. exact Htmp.
  - apply path_eqb_neq in Et.
    rewrite PCG.update_neq by auto.
    apply Hagree.
    + intro Hc. unfold tmp_scalar_acc in Hc. rewrite PCG.acc'_num in Hc.
      contradiction.
    + intros j Hj. apply Hq. simpl. exists j. exact Hj.
Qed.

(* Same agreement, but the right-hand environment is the original [rho]
   (not [rho] updated with [v] at [__tmp]).  This needs [e] to also be
   independent of [__tmp]. *)
Lemma eval_agree_outside_cells_tmp :
  forall {d n} (e : exp d) (output : acc (ary '{n} num)) (env rho : PCG.env)
         (v : PCG.exp num),
    exp_independent_of_acc e output ->
    exp_independent_of_acc e tmp_scalar_acc ->
    env tmp_path = Some v ->
    (forall q, ~ @PCG.in_acc num q tmp_scalar_acc ->
               (forall j, ~ @PCG.in_acc num q (output |{ j})) ->
               env q = rho q) ->
    to_pcg_exp e env = to_pcg_exp e rho.
Proof.
  intros d n e output env rho v Hout Htmp Htmpv Hagree.
  rewrite (@eval_agree_outside_output_with_tmp _ _ e output env rho v Hout Htmpv Hagree).
  apply exp_independent_of_acc_eval with (a := tmp_scalar_acc); [ exact Htmp | ].
  intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
  reflexivity.
Qed.

(* One iteration of the scalar-output continuation preserves the invariant and
   assigns the same value whether it reads [__tmp] or the functional result. *)
Lemma seqfor_scalar_assign_step_ok :
  forall n (output : acc (ary '{n} num)) (g : fin n -> exp num -> exp num)
         (e_final : exp num) (Hdisj : tmp_disjoint_from_acc output)
         (Hg_tmp_out_indep : forall j, exp_independent_of_acc (g j (CG.vrd "__tmp")) output)
         (Hg_out_indep : forall j, exp_independent_of_acc (g j e_final) output)
         (Hg_tmp_indep : forall j, exp_independent_of_acc (g j e_final) tmp_scalar_acc)
         (Hg_proper : forall j rho eta (v0 : PCG.exp num),
            to_pcg_exp e_final rho = v0 ->
            (forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> eta q = rho q) ->
            to_pcg_exp (g j (CG.vrd "__tmp")) (PCG.update eta tmp_path v0) =
            to_pcg_exp (g j e_final) rho)
         (i : fin n) (env rho : PCG.env) (v : PCG.exp num)
         (Hv : to_pcg_exp e_final rho = v),
    let fL := fun (j : fin n) (env : PCG.env) =>
      PCG.assign (output |{ j}) (to_pcg_exp (g j (CG.vrd "__tmp")) env) env in
    let fR := fun (j : fin n) (env : PCG.env) =>
      PCG.assign (output |{ j}) (to_pcg_exp (g j e_final) env) env in
    let P := fun env =>
      env tmp_path = Some v /\
      forall q, ~ @PCG.in_acc num q tmp_scalar_acc ->
                (forall j, ~ @PCG.in_acc num q (output |{ j})) ->
                env q = rho q in
    P env -> fL i env = fR i env /\ P (fL i env).
Proof.
  intros n output g e_final Hdisj Hg_tmp_out_indep Hg_out_indep Hg_tmp_indep
    Hg_proper i env rho v Hv fL fR P HP.
  destruct HP as [Htmp Hagree].
  assert (Hdisj_j : forall j, tmp_disjoint_from_acc (output |{ j})).
  { intros j p Hp Hout. apply (Hdisj p Hp). simpl. exists j. exact Hout. }
  split.
  - apply functional_extensionality; intro q.
    destruct (path_eqb (output |{ i}) q) eqn:E.
    + apply path_eqb_eq in E. subst q.
      unfold fL, fR. rewrite !PCG.assign_num. rewrite !PCG.update_eq. f_equal.
      assert (Hlhs : to_pcg_exp (g i (CG.vrd "__tmp")) env =
                     to_pcg_exp (g i e_final) rho).
      { assert (Htmp_val :
          to_pcg_exp (g i (CG.vrd "__tmp")) env =
          to_pcg_exp (g i (CG.vrd "__tmp")) (PCG.update rho tmp_path v))
          by (apply (@eval_agree_outside_output_with_tmp _ _ (g i (CG.vrd "__tmp")) output env rho v
                       (Hg_tmp_out_indep i) Htmp Hagree)).
        rewrite Htmp_val.
        apply Hg_proper; [ exact Hv | intros q0 Hq0; reflexivity ]. }
      assert (Hrhs : to_pcg_exp (g i e_final) env =
                     to_pcg_exp (g i e_final) rho)
        by (apply (@eval_agree_outside_cells_tmp _ _ (g i e_final) output env rho v
                     (Hg_out_indep i) (Hg_tmp_indep i) Htmp Hagree)).
      rewrite Hlhs. rewrite Hrhs. reflexivity.
    + apply path_eqb_neq in E.
      unfold fL, fR. rewrite !PCG.assign_num. rewrite !PCG.update_neq by (intro Hc; apply E; exact Hc).
      reflexivity.
  - split.
    + unfold fL. rewrite PCG.assign_num.
      rewrite PCG.update_neq by (intro Hc;
        apply (Hdisj_j i tmp_path in_acc_tmp_scalar_acc); simpl; exact Hc).
      exact Htmp.
    + intros q Hq Hout. unfold fL. rewrite PCG.assign_num.
      destruct (path_eqb (output |{ i}) q) eqn:E;
        [ apply path_eqb_eq in E; subst q;
          exfalso; apply (Hout i); simpl; reflexivity
        | apply path_eqb_neq in E;
          rewrite PCG.update_neq by (intro Hc; apply E; exact Hc);
          apply Hagree; [ exact Hq | intros j; apply Hout ] ].
Qed.

(* A sequence of scalar assignments to distinct acceptors, each disjoint from
   [__tmp], yields the same result at any path outside [__tmp] regardless of
   the starting environment (as long as the two starts agree outside [__tmp]).
   This is because the assigned values do not depend on the accumulated env. *)
Lemma seqfor_assign_start_independent :
  forall n (cells : fin n -> acc num) (vals : fin n -> PCG.exp num)
         (env1 env2 : PCG.env) (p : path),
    (forall j, tmp_disjoint_from_acc (cells j)) ->
    (forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> env1 q = env2 q) ->
    ~ @PCG.in_acc num p tmp_scalar_acc ->
    PCG.seqfor (fun j => PCG.assign (cells j) (vals j)) env1 p =
    PCG.seqfor (fun j => PCG.assign (cells j) (vals j)) env2 p.
Proof.
  induction n as [| n' IHn']; intros cells vals env1 env2 p Hdisj Henv Hp.
  - simpl. apply Henv. exact Hp.
  - assert (Hexp : forall env,
      PCG.seqfor (fun j : fin (S n') => PCG.assign (cells j) (vals j)) env =
      PCG.seq (PCG.seqfor (fun i : fin n' => PCG.assign (cells (fin2finS i)) (vals (fin2finS i))))
              (PCG.assign (cells (ltS n')) (vals (ltS n'))) env).
    { intro env. rewrite PCG.seqfor_Sn. reflexivity. }
    rewrite (Hexp env1). rewrite (Hexp env2).
    unfold PCG.seq. simpl.
    destruct (path_eqb (cells (ltS n')) p) eqn:E.
    + apply path_eqb_eq in E. subst p.
      rewrite !PCG.update_eq. reflexivity.
    + apply path_eqb_neq in E.
      rewrite !PCG.update_neq by (intro Hc; apply E; exact Hc).
      apply IHn' with (cells := fun i : fin n' => cells (fin2finS i))
                      (vals := fun i : fin n' => vals (fin2finS i));
        [ intros j; apply Hdisj | auto | exact Hp ].
Qed.

(* If a sequence of scalar assignments computes each value from the current
   environment, but the value is the same for any two environments that agree
   outside [__tmp], then the whole loop produces the same result at any path
   outside [__tmp] regardless of the starting environment (again assuming the
   two starts agree outside [__tmp]). *)
Lemma seqfor_assign_env_value_independent :
  forall n (cells : fin n -> acc num) (vals : PCG.env -> fin n -> PCG.exp num)
         (env1 env2 : PCG.env) (p : path),
    (forall j, tmp_disjoint_from_acc (cells j)) ->
    (forall j env1 env2,
       (forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> env1 q = env2 q) ->
       vals env1 j = vals env2 j) ->
    (forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> env1 q = env2 q) ->
    ~ @PCG.in_acc num p tmp_scalar_acc ->
    PCG.seqfor (fun j env => PCG.assign (cells j) (vals env j) env) env1 p =
    PCG.seqfor (fun j env => PCG.assign (cells j) (vals env j) env) env2 p.
Proof.
  induction n as [| n' IHn']; intros cells vals env1 env2 p Hdisj Hval Henv Hp.
  - simpl. apply Henv. exact Hp.
  - assert (Hexp : forall env,
      PCG.seqfor (fun j env' => PCG.assign (cells j) (vals env' j) env') env =
      PCG.seq (PCG.seqfor (fun i env' => PCG.assign (cells (fin2finS i)) (vals env' (fin2finS i)) env'))
              (fun env' => PCG.assign (cells (ltS n')) (vals env' (ltS n')) env')
              env).
    { intro env. rewrite PCG.seqfor_Sn. reflexivity. }
    rewrite (Hexp env1). rewrite (Hexp env2).
    unfold PCG.seq. simpl.
    destruct (path_eqb (cells (ltS n')) p) eqn:E;
      [ apply path_eqb_eq in E; subst p;
        rewrite !PCG.update_eq; f_equal;
        apply Hval; intros q Hq;
        apply IHn' with (p := q); auto;
        intros j; apply Hdisj
      | apply path_eqb_neq in E;
        rewrite !PCG.update_neq by (intro Hc; apply E; exact Hc);
        apply IHn' with (p := p); auto;
        intros j; apply Hdisj ].
Qed.

(* [seqfor_scalar_assign_continuation_ok] handles continuations that assign
   one scalar expression per element of a 1-D output array.  It is the form
   used by Softmax. *)
Lemma seqfor_scalar_assign_continuation_ok :
  forall n (output : acc (ary '{n} num))
         (g : fin n -> exp num -> exp num) (e_final : exp num),
    tmp_disjoint_from_acc output ->
    exp_independent_of_acc e_final tmp_scalar_acc ->
    (forall j, exp_independent_of_acc (g j e_final) tmp_scalar_acc) ->
    (forall j, exp_independent_of_acc (g j e_final) output) ->
    (forall j, exp_independent_of_acc (g j (CG.vrd "__tmp")) output) ->
    (forall j rho eta (v : PCG.exp num),
       to_pcg_exp e_final rho = v ->
       (forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> eta q = rho q) ->
       to_pcg_exp (g j (CG.vrd "__tmp")) (PCG.update eta tmp_path v) =
       to_pcg_exp (g j e_final) rho) ->
    loopacc_continuation_ok
      (fun r : exp num => seqfor (fun j : fin n => output|{j} |:= g j r))
      e_final.
Proof.
  intros n output g e_final Hdisj He_indep Hg_tmp_indep Hg_out_indep
    Hg_tmp_out_indep Hg_proper.
  assert (Hdisj_j : forall j, tmp_disjoint_from_acc (output |{ j})).
  { intros j p Hp Hout. apply (Hdisj p Hp). simpl. exists j. exact Hout. }
  split.
  - (* preservation of StructUndefined *)
    intros rho Hundef.
    rewrite eval_seqfor_aux.
    apply PCG.seqfor_preserves_None.
    + exact Hundef.
    + intros j rho'. rewrite eval_assign_aux. right.
      apply PCG.update_neq. intro Hc.
      apply (Hdisj_j j tmp_path in_acc_tmp_scalar_acc).
      simpl. exact Hc.
  - (* behaviour matches functional result when tmp holds the result *)
    intros rho eta v Hv Heta p Hp.
    set (env0 := PCG.assign tmp_scalar_acc v eta).
    assert (Henv0_tmp : env0 tmp_path = Some v).
    { unfold env0. apply PCG.update_eq. }
    assert (Henv0_agrees : forall q, ~ @PCG.in_acc num q tmp_scalar_acc -> env0 q = rho q).
    { intros q Hq. unfold env0. rewrite PCG.assign_num. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
      rewrite Heta by exact Hq. reflexivity. }
    rewrite !eval_seqfor_aux.
    set (fL := fun (j : fin n) (env : PCG.env) =>
      PCG.assign (output |{ j}) (to_pcg_exp (g j (CG.vrd "__tmp")) env) env).
    set (fR := fun (j : fin n) (env : PCG.env) =>
      PCG.assign (output |{ j}) (to_pcg_exp (g j e_final) env) env).
    assert (HfL : forall j, eval_aux (output |{ j} |:= g j (CG.vrd "__tmp")) 1 = fL j).
    { intro j. apply functional_extensionality; intro env. apply eval_assign_aux. }
    assert (HfR : forall j, eval_aux (output |{ j} |:= g j e_final) 1 = fR j).
    { intro j. apply functional_extensionality; intro env. apply eval_assign_aux. }
    rewrite (PCG.seqfor_extensionality _ _ HfL).
    rewrite (PCG.seqfor_extensionality _ _ HfR).
    (* Invariant: [__tmp] holds [v], and every other path that is not an output
       cell still agrees with the original [rho]. *)
    set (P := fun env =>
      env tmp_path = Some v /\
      forall q, ~ @PCG.in_acc num q tmp_scalar_acc ->
                (forall j, ~ @PCG.in_acc num q (output |{ j})) ->
                env q = rho q).
    assert (HP0 : P env0).
    { split; [ exact Henv0_tmp | ].
      intros q Hq Hout. apply Henv0_agrees. exact Hq. }
    assert (Hstep : forall i env, P env -> fL i env = fR i env /\ P (fL i env)).
    { intros i env HP.
      apply (@seqfor_scalar_assign_step_ok _ output g e_final Hdisj
               Hg_tmp_out_indep Hg_out_indep Hg_tmp_indep
               Hg_proper i env rho v Hv HP). }
    destruct (seqfor_pointwise_inv fL fR env0 P HP0 Hstep) as [Heq _].
    apply eq_trans with (y := PCG.seqfor fR env0 p).
    + apply f_equal with (f := fun h => h p). exact Heq.
    + unfold fR.
      apply (@seqfor_assign_env_value_independent _ (fun j => output |{ j})
               (fun env j => to_pcg_exp (g j e_final) env) env0 rho p);
        [ intros j p' Hp' Hout'; apply (Hdisj_j j p' Hp' Hout')
        | intros j env1 env2 Henv12;
          apply exp_independent_of_acc_eval with (a := tmp_scalar_acc);
          [ apply Hg_tmp_indep | exact Henv12 ]
        | exact Henv0_agrees
        | exact Hp ].
Qed.

Section Linear1d_Sem.

  Variables (m outnum : nat)
            (w : exp (ary '{outnum} (ary '{m} num)))
            (b : exp (ary '{outnum} num))
            (input : exp (ary '{m} num))
            (Hm : m > 0) (Houtnum : outnum > 0).

  Let tmp_scalar_acc : acc num := @PCG.acc' num tmp_path.

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hw_indep : exp_independent_of_acc w tmp_scalar_acc.
  Hypothesis Hb_indep : exp_independent_of_acc b tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{outnum} num)),
    exp_independent_of_acc input output.
  Hypothesis Hw_out : forall (output : acc (ary '{outnum} num)),
    exp_independent_of_acc w output.
  Hypothesis Hb_out : forall (output : acc (ary '{outnum} num)),
    exp_independent_of_acc b output.

  Definition tmp_disjoint_from_output
    (output : acc (ary '{outnum} num)) : Prop :=
    forall p out, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ out}).

  Lemma Linear1d_cell_independent_of_output :
    forall (output : acc (ary '{outnum} num)) (out : fin outnum),
      exp_independent_of_acc
        (add (sum (mkvSeq (fun i : fin m => mul input|[i] w|[out]|[i]))) b|[out])
        output.
  Proof.
    intros output out.
    apply exp_independent_of_acc_add;
      [ | apply exp_independent_of_acc_idx; apply Hb_out ].
    apply exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    apply exp_independent_of_acc_mul;
      [ apply exp_independent_of_acc_idx; apply Hinput_out
      | apply exp_independent_of_acc_idx; apply exp_independent_of_acc_idx; apply Hw_out ].
  Qed.

  Lemma Linear1d_cell_continuation_ok :
    forall (output : acc (ary '{outnum} num)) (out : fin outnum),
      tmp_disjoint_from_output output ->
      loopacc_continuation_ok
        (fun r : exp num => output|{out} |:= add r b|[out])
        (sum (mkvSeq (fun i : fin m => mul input|[i] w|[out]|[i]))).
Proof.
    intros output out Hdisj.
    apply scalar_assign_continuation_ok;
      [ intros p Hp Hout; apply (Hdisj p out Hp); exact Hout
      | apply exp_independent_of_acc_sum; intro i;
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec;
        apply exp_independent_of_acc_mul;
        [ apply exp_independent_of_acc_idx; exact Hinput_indep
        | apply exp_independent_of_acc_idx; apply exp_independent_of_acc_idx; exact Hw_indep ]
      | apply exp_independent_of_acc_add;
        [ apply exp_independent_of_acc_sum; intro i;
          unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec;
          apply exp_independent_of_acc_mul;
          [ apply exp_independent_of_acc_idx; exact Hinput_indep
          | apply exp_independent_of_acc_idx; apply exp_independent_of_acc_idx; exact Hw_indep ]
        | apply exp_independent_of_acc_idx; exact Hb_indep ]
      | intros rho eta v Hv Heta;
        rewrite !to_pcg_exp_add; f_equal;
        [ unfold CG.vrd; simpl; rewrite to_pcg_exp_REvar; rewrite PCG.update_eq by reflexivity; symmetry; exact Hv
        | apply exp_independent_of_acc_eval with (a := tmp_scalar_acc);
          [ apply exp_independent_of_acc_idx; exact Hb_indep
          | intros q Hq; rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto);
            apply Heta; intro Hc; apply Hq; simpl; auto ] ] ].
  Qed.

  Theorem Linear1d_sem :
    forall (output : acc (ary '{outnum} num)) (rho : PCG.env),
      tmp_disjoint_from_output output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Linear m outnum w b input)) rho =
      eval (@Linear1d_comm m outnum w b input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Linear, Linear1d_comm.
    rewrite eval_mkvSeq; [ | intros out; apply Linear1d_cell_independent_of_output ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros out eta HPeta. split.
    - set (e := mkvSeq (fun i : fin m => mul input|[i] w|[out]|[i])).
      set (c := fun r : exp num => output|{out} |:= add r b|[out]).
      (* The source AST uses [mul ...] directly; [eval_csum_equiv] emits [e|[i]].
         These are propositionally equal by [v_idx_mk_vec]. *)
      assert (Hrhs : (@loopacc num (fun tmp : string =>
          (vwt tmp |:= zero) '; seqfor (fun i : fin m =>
            vwt tmp |:= add (mul input|[i] w|[out]|[i]) (vrd tmp))
          '; output|{out} |:= add (vrd tmp) b|[out]))
        = (@loopacc num (fun tmp : string =>
          (vwt tmp |:= zero) '; seqfor (fun i : fin m =>
            vwt tmp |:= add e|[i] (vrd tmp))
          '; output|{out} |:= add (vrd tmp) b|[out]))).
      { f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : seqfor (fun i : fin m =>
                        vwt tmp |:= add (mul input|[i] w|[out]|[i]) (vrd tmp))
                    = seqfor (fun i : fin m =>
                        vwt tmp |:= add e|[i] (vrd tmp))).
        { apply seqfor_extensionality; intro i.
          assert (Heq : mul input|[i] w|[out]|[i] = e|[i]).
          { unfold e, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
          rewrite Heq. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      rewrite eval_assign.
      rewrite <- (eval_assign_aux 1 num _ _ eta).
      change (eval_aux (c (sum e)) 1 eta =
        eval (@loopacc num
          (fun tmp : string =>
            let wtmp := vwt tmp in let v := vrd tmp in
            wtmp |:= zero '; seqfor (fun i : fin m =>
              wtmp |:= add e|[i] v)
            '; c v)) eta).
      unfold P in HPeta.
      change (@PCG.StructUndefined num Ionia.CNN_CodeGen_Semantics.wtmp_acc eta) in HPeta.
      assert (Hindep : @exp_independent_of_acc (ary '{m} num) num e Ionia.CNN_CodeGen_Semantics.wtmp_acc).
      { apply exp_independent_of_acc_mkvSeq. intro i.
        apply exp_independent_of_acc_mul.
        - apply exp_independent_of_acc_idx. exact Hinput_indep.
        - apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hw_indep. }
      assert (Hok : loopacc_continuation_ok c (CD.sum e)).
      { apply (@Linear1d_cell_continuation_ok output out Hdisj). }
      assert (Hinst := @eval_csum_equiv m e c eta HPeta Hindep Hok).
      rewrite Hinst. reflexivity.
    - rewrite eval_assign.
      apply assign_preserves_StructUndefined_tmp.
      + intros p Hp Hout. apply (Hdisj p out Hp). exact Hout.
      + exact HPeta.
  Qed.

End Linear1d_Sem.

(* ------------------------------------------------------------------------ *)
(* Softmax1d                                                                *)
(* ------------------------------------------------------------------------ *)

Section Softmax1d_Sem.

  Variables (n : nat) (input : exp (ary '{n} num)) (Hn : n > 0).

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{n} num)),
    exp_independent_of_acc input output.

  Definition Softmax1d_cell (s : exp num) (j : fin n) : exp num :=
    div (pExp input|[j]) s.

  Lemma Softmax1d_cell_independent_of_output :
    forall (output : acc (ary '{n} num)) (s : exp num) (j : fin n),
      exp_independent_of_acc s output ->
      exp_independent_of_acc (Softmax1d_cell s j) output.
  Proof.
    intros output s j Hs.
    unfold Softmax1d_cell.
    apply exp_independent_of_acc_div.
    - apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply Hinput_out.
    - exact Hs.
  Qed.

  Lemma Softmax1d_continuation_ok :
    forall (output : acc (ary '{n} num)),
      (forall p j, @PCG.in_acc num p tmp_scalar_acc ->
        ~ @PCG.in_acc num p (output |{ j})) ->
      loopacc_continuation_ok
        (fun r : exp num => seqfor (fun j : fin n => output|{j} |:= div (pExp input|[j]) r))
        (sum (mkvSeq (fun i : fin n => pExp input|[i]))).
  Proof.
    intros output Hdisj.
    set (e_final := sum (mkvSeq (fun i : fin n => pExp input|[i]))).
    set (g := fun (j : fin n) (r : exp num) => div (pExp input|[j]) r).
    assert (Hdisj_acc : tmp_disjoint_from_acc output).
    { intros p Hp Hout. unfold PCG.in_acc in Hout. simpl in Hout.
      destruct Hout as [j Hj]. apply (Hdisj p j Hp). exact Hj. }
    apply seqfor_scalar_assign_continuation_ok.
    - exact Hdisj_acc.
    - unfold e_final. apply exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. exact Hinput_indep.
    - intros j. unfold g, e_final. apply exp_independent_of_acc_div.
      + apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. exact Hinput_indep.
      + apply exp_independent_of_acc_sum. intro i.
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. exact Hinput_indep.
    - intros j. unfold g, e_final. apply exp_independent_of_acc_div.
      + apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply Hinput_out.
      + apply exp_independent_of_acc_sum. intro i.
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply Hinput_out.
    - intros j. unfold g. apply exp_independent_of_acc_div.
      + apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply Hinput_out.
      + apply exp_independent_of_acc_REvar.
        intro Hc. apply (Hdisj_acc (DE.Var "__tmp") in_acc_tmp_scalar_acc Hc).
    - intros j rho eta v Hv Heta.
      rewrite !to_pcg_exp_div; f_equal.
      + rewrite !to_pcg_exp_pExp; f_equal.
        apply exp_independent_of_acc_eval with (a := tmp_scalar_acc).
        * apply exp_independent_of_acc_idx. apply Hinput_indep.
        * intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
          apply Heta. intro Hc. apply Hq. simpl. auto.
      + unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
        rewrite PCG.update_eq by reflexivity. symmetry. exact Hv.
  Qed.

  Theorem Softmax1d_sem :
    forall (output : acc (ary '{n} num)) (rho : PCG.env),
      (forall p j, @PCG.in_acc num p tmp_scalar_acc ->
        ~ @PCG.in_acc num p (output |{ j})) ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Softmax1d n input)) rho =
      eval (@Softmax1d_comm n input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Softmax1d, let_binding.
    set (e := mkvSeq (fun i : fin n => pExp input|[i])).
    assert (Hcell_indep : forall j,
      exp_independent_of_acc (div (pExp input|[j]) (CD.sum e)) output).
    { intros j. apply exp_independent_of_acc_div.
      - apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply Hinput_out.
      - apply exp_independent_of_acc_sum. intro i.
        unfold e, DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply Hinput_out. }
    rewrite eval_mkvSeq; [ | intros j; apply Hcell_indep ].
    apply eq_trans with (y := eval_aux (seqfor (fun j : fin n =>
      output|{j} |:= div (pExp input|[j]) (CD.sum e))) 1 rho).
    - rewrite eval_seqfor.
      assert (Hpoint : forall j,
        eval (output|{j} |:= div (pExp input|[j]) (CD.sum e)) =
        eval_aux (output|{j} |:= div (pExp input|[j]) (CD.sum e)) 1).
      { intro j. apply functional_extensionality; intro rho''.
        rewrite eval_assign. symmetry. apply eval_assign_aux. }
      replace (PCG.seqfor (fun j : fin n =>
                 eval (output|{j} |:= div (pExp input|[j]) (CD.sum e))) rho)
        with (PCG.seqfor (fun j : fin n =>
                 eval_aux (output|{j} |:= div (pExp input|[j]) (CD.sum e)) 1) rho).
      2: { apply f_equal with (f := fun h => PCG.seqfor h rho).
           apply functional_extensionality; intro j. symmetry. apply Hpoint. }
      rewrite eval_seqfor_aux. reflexivity.
    - assert (Hrhs : @Softmax1d_comm n input output =
        @loopacc num (fun tmp : string =>
          let w := vwt tmp in let v := vrd tmp in
          (w |:= zero) '; seqfor (fun i : fin n => w |:= add e|[i] v) ';
          seqfor (fun j : fin n => output|{j} |:= div (pExp input|[j]) v))).
      { unfold Softmax1d_comm. f_equal. apply functional_extensionality; intro tmp.
        assert (Hfor : seqfor (fun i : fin n =>
                        vwt tmp |:= add (pExp input|[i]) (vrd tmp))
                    = seqfor (fun i : fin n =>
                        vwt tmp |:= add e|[i] (vrd tmp))).
        { apply seqfor_extensionality; intro i.
          assert (Heq_i : pExp input|[i] = e|[i]).
          { unfold e, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
          rewrite Heq_i. reflexivity. }
        rewrite Hfor. reflexivity. }
      rewrite Hrhs.
      apply (@eval_csum_equiv n e
        (fun s : exp num => seqfor (fun j : fin n =>
          output|{j} |:= div (pExp input|[j]) s)) rho).
      + exact Hundef.
      + unfold e. apply exp_independent_of_acc_mkvSeq. intro i.
        apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. exact Hinput_indep.
      + apply Softmax1d_continuation_ok. exact Hdisj.
  Qed.

End Softmax1d_Sem.

(* ------------------------------------------------------------------------ *)
(* Linear2d                                                                 *)
(* ------------------------------------------------------------------------ *)

Section Linear2d_Sem.

  Variables (batch m outnum : nat)
            (w : exp (ary '{outnum} (ary '{m} num)))
            (b : exp (ary '{outnum} num))
            (input : exp (ary '{batch} (ary '{m} num)))
            (Hbatch : batch > 0) (Hm : m > 0) (Houtnum : outnum > 0).

  Let tmp_scalar_acc : acc num := @PCG.acc' num tmp_path.

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hw_indep : exp_independent_of_acc w tmp_scalar_acc.
  Hypothesis Hb_indep : exp_independent_of_acc b tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{batch} (ary '{outnum} num))),
    exp_independent_of_acc input output.
  Hypothesis Hw_out : forall (output : acc (ary '{batch} (ary '{outnum} num))),
    exp_independent_of_acc w output.
  Hypothesis Hb_out : forall (output : acc (ary '{batch} (ary '{outnum} num))),
    exp_independent_of_acc b output.

  Definition tmp_disjoint_from_output2d
    (output : acc (ary '{batch} (ary '{outnum} num))) : Prop :=
    forall p bi out, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ bi} |{ out}).

  Lemma Linear2d_cell_independent_of_output :
    forall (output : acc (ary '{batch} (ary '{outnum} num))) (bi : fin batch) (out : fin outnum),
      exp_independent_of_acc
        (add (sum (mkvSeq (fun i : fin m => mul input|[bi]|[i] w|[out]|[i]))) b|[out])
        output.
  Proof.
    intros output bi out.
    apply exp_independent_of_acc_add.
    - apply exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_mul.
      + apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. apply Hinput_out.
      + apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. apply Hw_out.
    - apply exp_independent_of_acc_idx. apply Hb_out.
  Qed.

  Lemma Linear2d_cell_continuation_ok :
    forall (output : acc (ary '{batch} (ary '{outnum} num))) (bi : fin batch) (out : fin outnum),
      tmp_disjoint_from_output2d output ->
      loopacc_continuation_ok
        (fun r : exp num => (output|{bi}|{out}) |:= add r b|[out])
        (sum (mkvSeq (fun i : fin m => mul input|[bi]|[i] w|[out]|[i]))).
  Proof.
    intros output bi out Hdisj.
    set (e := mkvSeq (fun i : fin m => mul input|[bi]|[i] w|[out]|[i])).
    apply scalar_assign_continuation_ok.
    - intros p Hp Hout. apply (Hdisj p bi out Hp). exact Hout.
    - unfold e. apply exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_mul.
      + apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
      + apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hw_indep.
    - apply exp_independent_of_acc_add.
      + unfold e. apply exp_independent_of_acc_sum. intro i.
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_mul.
        * apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
        * apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hw_indep.
      + apply exp_independent_of_acc_idx. exact Hb_indep.
    - intros rho eta v Hv Heta. rewrite !to_pcg_exp_add. f_equal.
      + unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
        rewrite PCG.update_eq by reflexivity. symmetry. exact Hv.
      + apply exp_independent_of_acc_eval with (a := tmp_scalar_acc).
        * apply exp_independent_of_acc_idx. exact Hb_indep.
        * intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
          apply Heta. intro Hc. apply Hq. simpl. auto.
  Qed.

  Theorem Linear2d_sem :
    forall (output : acc (ary '{batch} (ary '{outnum} num))),
      tmp_disjoint_from_output2d output ->
      forall (rho : PCG.env),
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Linear2d batch m outnum w b input)) rho =
      eval (@Linear2d_comm batch m outnum w b input output) rho.
  Proof.
    intros output Hdisj rho Hundef.
    unfold A, Linear2d, Linear2d_comm.
    set (row := fun bi : fin batch => mkvSeq (fun out : fin outnum =>
      add (sum (mkvSeq (fun i : fin m => mul input|[bi]|[i] w|[out]|[i]))) b|[out])).
    assert (Hrow_indep : forall bi, exp_independent_of_acc (row bi) output).
    { intros bi. unfold row. apply exp_independent_of_acc_mkvSeq. intros out.
      apply Linear2d_cell_independent_of_output. }
    rewrite eval_mkvSeq; [ | intros bi; apply Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros bi eta HPeta. split.
    - (* Row-level equivalence. *)
      assert (Hcell_indep_bi : forall out,
        exp_independent_of_acc
          (add (sum (mkvSeq (fun i : fin m => mul input|[bi]|[i] w|[out]|[i]))) b|[out])
          (output |{ bi})).
      { intros out. unfold exp_independent_of_acc. intros p Hp.
        apply (@Linear2d_cell_independent_of_output output bi out).
        simpl in Hp. destruct Hp as [out' Hout'].
        simpl. exists bi. exists out'. exact Hout'. }
      unfold row in |- *. rewrite eval_mkvSeq; [ | intros out; apply Hcell_indep_bi ].
      rewrite !eval_seqfor.
      apply seqfor_pointwise_inv with (P := P); [exact HPeta |].
      intros out eta' HPeta'. split.
      + set (e := mkvSeq (fun i : fin m => mul input|[bi]|[i] w|[out]|[i])).
        set (c := fun r : exp num => (output|{bi}|{out}) |:= add r b|[out]).
        assert (Hrhs : (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun i : fin m =>
              vwt tmp |:= add (mul input|[bi]|[i] w|[out]|[i]) (vrd tmp)) ';
            (output|{bi}|{out}) |:= add (vrd tmp) b|[out]))
          = (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun i : fin m =>
              vwt tmp |:= add e|[i] (vrd tmp)) ';
            (output|{bi}|{out}) |:= add (vrd tmp) b|[out]))).
        { f_equal. apply functional_extensionality; intro tmp.
          assert (Hfor : seqfor (fun i : fin m =>
                          vwt tmp |:= add (mul input|[bi]|[i] w|[out]|[i]) (vrd tmp))
                      = seqfor (fun i : fin m =>
                          vwt tmp |:= add e|[i] (vrd tmp))).
          { apply seqfor_extensionality; intro i.
            assert (Heq : mul input|[bi]|[i] w|[out]|[i] = e|[i]).
            { unfold e, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
            rewrite Heq. reflexivity. }
          rewrite Hfor. reflexivity. }
        rewrite Hrhs.
        rewrite eval_assign.
        rewrite <- (eval_assign_aux 1 num _ _ eta').
        change (eval_aux (c (sum e)) 1 eta' =
          eval (@loopacc num (fun tmp : string =>
            let wtmp := vwt tmp in let v := vrd tmp in
            wtmp |:= zero '; seqfor (fun i : fin m =>
              wtmp |:= add e|[i] v)
            '; c v)) eta').
        apply (@eval_csum_equiv m e c eta').
        * exact HPeta'.
        * unfold e. apply exp_independent_of_acc_mkvSeq. intro i.
          apply exp_independent_of_acc_mul.
          -- apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
          -- apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hw_indep.
        * apply Linear2d_cell_continuation_ok. exact Hdisj.
      + rewrite eval_assign.
        apply assign_preserves_StructUndefined_tmp.
        * intros p Hp Hout. apply (Hdisj p bi out Hp). exact Hout.
        * exact HPeta'.
    - rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta tmp_path).
      + unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros out rho'. apply PCG.assign_not_in_acc.
        intros Hc. apply (Hdisj tmp_path bi out in_acc_tmp_scalar_acc). exact Hc.
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End Linear2d_Sem.

(* ------------------------------------------------------------------------ *)
(* Softmax2d / Log_Softmax2d                                                *)
(* ------------------------------------------------------------------------ *)

Section Softmax2d_Sem.

  Variables (batch m : nat) (input : exp (ary '{batch} (ary '{m} num)))
            (Hbatch : batch > 0) (Hm : m > 0).

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{batch} (ary '{m} num))),
    exp_independent_of_acc input output.

  Definition Softmax2d_cell (b : fin batch) (s : exp num) (j : fin m) : exp num :=
    div (pExp input|[b]|[j]) s.

  Lemma Softmax2d_cell_independent_of_output :
    forall d' (a : acc d') (b : fin batch) (s : exp num) (j : fin m),
      exp_independent_of_acc input a ->
      exp_independent_of_acc s a ->
      exp_independent_of_acc (Softmax2d_cell b s j) a.
  Proof.
    intros d' a b s j Hin Hs.
    unfold Softmax2d_cell.
    apply exp_independent_of_acc_div.
    - apply exp_independent_of_acc_pExp. repeat apply exp_independent_of_acc_idx. apply Hin.
    - exact Hs.
  Qed.

  Lemma Softmax2d_batch_continuation_ok :
    forall (output : acc (ary '{batch} (ary '{m} num))) (b : fin batch),
      (forall p j, @PCG.in_acc num p tmp_scalar_acc -> output |{ b} |{ j} <> p) ->
      loopacc_continuation_ok
        (fun r : exp num => seqfor (fun j : fin m => output|{b}|{j} |:= div (pExp input|[b]|[j]) r))
        (sum (mkvSeq (fun i : fin m => pExp input|[b]|[i]))).
  Proof.
    intros output b Hdisj_row.
    set (e_final := sum (mkvSeq (fun i : fin m => pExp input|[b]|[i]))).
    set (g := fun (j : fin m) (r : exp num) => div (pExp input|[b]|[j]) r).
    assert (Hdisj_acc : tmp_disjoint_from_acc (output |{ b})).
    { intros p Hp Hout. unfold PCG.in_acc in Hout. simpl in Hout.
      destruct Hout as [j Hj]. simpl in Hj. assert (Hc := Hdisj_row p j Hp Hj). contradiction. }
    assert (Hinput_row : exp_independent_of_acc input (output |{ b})).
    { intros p Hp. apply (@Hinput_out output). unfold PCG.in_acc in Hp |- *. simpl in Hp |- *.
      exists b. destruct Hp as [j Hj]. exists j. exact Hj. }
    apply seqfor_scalar_assign_continuation_ok.
    - exact Hdisj_acc.
    - unfold e_final. apply exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
    - intros j. unfold g, e_final. apply exp_independent_of_acc_div.
      + apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
      + apply exp_independent_of_acc_sum. intro i.
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
    - intros j. unfold g, e_final. apply exp_independent_of_acc_div.
      + apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. apply Hinput_row.
      + apply exp_independent_of_acc_sum. intro i.
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. apply Hinput_row.
    - intros j. unfold g. apply exp_independent_of_acc_div.
      + apply exp_independent_of_acc_pExp. apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. apply Hinput_row.
      + apply exp_independent_of_acc_REvar.
        intro Hc. apply (Hdisj_acc (DE.Var "__tmp") in_acc_tmp_scalar_acc Hc).
    - intros j rho eta v Hv Heta.
      rewrite !to_pcg_exp_div; f_equal.
      + rewrite !to_pcg_exp_pExp; f_equal.
        apply exp_independent_of_acc_eval with (a := tmp_scalar_acc).
        * apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx. exact Hinput_indep.
        * intros q Hq. rewrite PCG.update_neq by (intro Hc; apply Hq; simpl; auto).
          apply Heta. intro Hc. apply Hq. simpl. auto.
      + unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
        rewrite PCG.update_eq by reflexivity. symmetry. exact Hv.
  Qed.

  Theorem Softmax2d_sem :
    forall (output : acc (ary '{batch} (ary '{m} num))) (rho : PCG.env),
      (forall p b j, @PCG.in_acc num p tmp_scalar_acc ->
        ~ @PCG.in_acc num p (output |{ b} |{ j})) ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Softmax2d batch m input)) rho =
      eval (@Softmax2d_comm batch m input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Softmax2d, Softmax2d_comm, let_binding.
    set (s := mkvSeq (fun b : fin batch =>
      sum (mkvSeq (fun i : fin m => pExp input|[b]|[i])))).
    set (row := fun b : fin batch => mkvSeq (fun j : fin m =>
      div (pExp input|[b]|[j]) (s|[b]))).
    assert (Hs_indep : exp_independent_of_acc s output).
    { unfold s. apply exp_independent_of_acc_mkvSeq. intro b'.
      apply exp_independent_of_acc_sum. intro i.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_pExp. repeat apply exp_independent_of_acc_idx. apply Hinput_out. }
    assert (Hrow_indep : forall b, exp_independent_of_acc (row b) output).
    { intros b. unfold row. apply exp_independent_of_acc_mkvSeq. intros j.
      apply exp_independent_of_acc_div.
      - apply exp_independent_of_acc_pExp. repeat apply exp_independent_of_acc_idx. apply Hinput_out.
      - apply exp_independent_of_acc_idx. exact Hs_indep. }
    rewrite eval_mkvSeq; [ | intros b; apply Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros b eta HPeta. split.
    - assert (Hinput_row : exp_independent_of_acc input (output |{ b})).
      { intros p Hp. apply (@Hinput_out output). unfold PCG.in_acc in Hp |- *. simpl in Hp |- *.
        exists b. destruct Hp as [j Hj]. exists j. exact Hj. }
      assert (Hs_row : exp_independent_of_acc s (output |{ b})).
      { unfold s. apply exp_independent_of_acc_mkvSeq. intro b'.
        apply exp_independent_of_acc_sum. intro i.
        unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
        apply exp_independent_of_acc_pExp. repeat apply exp_independent_of_acc_idx.
        apply Hinput_row. }
      assert (Hcell_indep_b : forall j,
        exp_independent_of_acc (div (pExp input|[b]|[j]) (s|[b])) (output |{ b})).
      { intros j.
        apply (Softmax2d_cell_independent_of_output (d' := ary '{ m} num) (a := output |{ b}));
          [ apply Hinput_row | apply exp_independent_of_acc_idx; apply Hs_row ]. }
      unfold row in |- *. rewrite eval_mkvSeq; [ | intros j; apply Hcell_indep_b ].
      apply eq_trans with (y := eval_aux (seqfor (fun j : fin m =>
        (output|{b})|{j} |:= div (pExp input|[b]|[j]) (s|[b]))) 1 eta).
      + rewrite eval_seqfor.
        assert (Hpoint : forall j,
          eval ((output|{b})|{j} |:= div (pExp input|[b]|[j]) (s|[b])) =
          eval_aux ((output|{b})|{j} |:= div (pExp input|[b]|[j]) (s|[b])) 1).
        { intro j. apply functional_extensionality; intro rho''.
          rewrite eval_assign. symmetry. apply eval_assign_aux. }
        replace (PCG.seqfor (fun j : fin m =>
          eval ((output|{b})|{j} |:= div (pExp input|[b]|[j]) (s|[b]))) eta)
          with (PCG.seqfor (fun j : fin m =>
            eval_aux ((output|{b})|{j} |:= div (pExp input|[b]|[j]) (s|[b])) 1) eta).
        2: { apply f_equal with (f := fun h => PCG.seqfor h eta).
             apply functional_extensionality; intro j. symmetry. apply Hpoint. }
        rewrite eval_seqfor_aux. reflexivity.
      + set (e := mkvSeq (fun i : fin m => pExp input|[b]|[i])).
        assert (Heq : s|[b] = sum e).
        { unfold e, s, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
        rewrite Heq.
        set (c := fun r : exp num => seqfor (fun j : fin m =>
          (output|{b})|{j} |:= div (pExp input|[b]|[j]) r)).
        assert (Hrhs : (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun i : fin m =>
              vwt tmp |:= add (pExp input|[b]|[i]) (vrd tmp)) ';
            seqfor (fun j : fin m =>
              (output|{b})|{j} |:= div (pExp input|[b]|[j]) (vrd tmp))))
          = (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun i : fin m =>
              vwt tmp |:= add e|[i] (vrd tmp)) ';
            seqfor (fun j : fin m =>
              (output|{b})|{j} |:= div (pExp input|[b]|[j]) (vrd tmp))))).
        { f_equal. apply functional_extensionality; intro tmp.
          assert (Hfor : seqfor (fun i : fin m =>
                          vwt tmp |:= add (pExp input|[b]|[i]) (vrd tmp))
                      = seqfor (fun i : fin m =>
                          vwt tmp |:= add e|[i] (vrd tmp))).
          { apply seqfor_extensionality; intro i.
            assert (Heq_i : pExp input|[b]|[i] = e|[i]).
            { unfold e, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
            rewrite Heq_i. reflexivity. }
          rewrite Hfor. reflexivity. }
        rewrite Hrhs.
        apply (@eval_csum_equiv m e c eta).
        * exact HPeta.
        * unfold e. apply exp_independent_of_acc_mkvSeq. intro i.
          apply exp_independent_of_acc_pExp. repeat apply exp_independent_of_acc_idx. exact Hinput_indep.
        * apply Softmax2d_batch_continuation_ok.
          intros p j' Hp Hc. apply (Hdisj p b j' Hp). simpl. rewrite Hc. simpl. reflexivity.
    - rewrite eval_assign.
      assert (Hpres : PCG.assign (output|{b}) (to_pcg_exp (row b) eta) eta tmp_path = eta tmp_path).
      { unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros j rho'.
        apply PCG.assign_not_in_acc.
        intros Hc. apply (Hdisj tmp_path b j in_acc_tmp_scalar_acc). exact Hc. }
      apply PCG.StructUndefined_num. apply eq_trans with (y := eta tmp_path).
      + exact Hpres.
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End Softmax2d_Sem.

(* ------------------------------------------------------------------------ *)
(* GlobalAvgPool4d                                                          *)
(* ------------------------------------------------------------------------ *)

Fixpoint sumR_nat (n : nat) (f : nat -> R) : R :=
  match n with
  | 0 => R0
  | S n' => Rplus (f n') (sumR_nat n' f)
  end.

Lemma sumR_nat_eq : forall n (f g : nat -> R),
  (forall k, k < n -> f k = g k) -> sumR_nat n f = sumR_nat n g.
Proof.
  intros n f g H. induction n as [| n' IHn]; [reflexivity |].
  simpl. rewrite H by lia. rewrite IHn; [reflexivity |].
  intros k Hk. apply H. lia.
Qed.

Lemma sumR_nat_split : forall n1 n2 (f : nat -> R),
  sumR_nat (n1 + n2) f =
  Rplus (sumR_nat n1 (fun i => f (n2 + i)))
        (sumR_nat n2 f).
Proof.
  intros n1 n2. induction n1 as [| n1' IHn1]; intro f.
  - simpl. rewrite Rplus_0_l. reflexivity.
  - simpl. rewrite IHn1.
    replace (n1' + n2) with (n2 + n1') by lia.
    rewrite Rplus_assoc. reflexivity.
Qed.

Lemma sum_mkvSeq_Sn : forall n (f : fin (S n) -> exp num),
  sum (mkvSeq f) = add (f (ltS n)) (sum (mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold sum, CD.sum, DE.mkvSeq. rewrite mk_vec_Sn. simpl. reflexivity.
Qed.

Lemma to_pcg_exp_sum_empty : forall (f : fin 0 -> exp num) (rho : PCG.env),
  to_pcg_exp (sum (mkvSeq f)) rho = R0.
Proof.
  intros f rho. unfold sum, CD.sum, DE.mkvSeq. simpl. rewrite to_pcg_exp_zero. reflexivity.
Qed.

Definition sumR_nat_fin {n} (f : forall k, k < n -> R) : R :=
  sumR_nat n (fun k => match lt_dec k n with
                       | left H => f k H
                       | right _ => R0
                       end).

Lemma sumR_nat_fin_eq : forall n (f g : forall k, k < n -> R),
  (forall k Hk, f k Hk = g k Hk) -> sumR_nat_fin f = sumR_nat_fin g.
Proof.
  intros n f g H. unfold sumR_nat_fin. apply sumR_nat_eq. intros k Hk.
  destruct (lt_dec k n) as [H' | H']; [apply H | reflexivity].
Qed.

Lemma sumR_nat_fin_proof_irrelevance_bound :
  forall n1 n2 (Heq : n1 = n2) (f : forall k, k < n1 -> R) (g : forall k, k < n2 -> R),
    (forall k (H1 : k < n1) (H2 : k < n2), f k H1 = g k H2) ->
    sumR_nat_fin f = sumR_nat_fin g.
Proof.
  intros n1 n2 Heq. destruct Heq. intros f g H.
  apply sumR_nat_fin_eq. intros k Hk. apply H.
Qed.

Lemma sumR_nat_fin_S : forall n (f : forall k, k < S n -> R),
  sumR_nat_fin f =
  Rplus (f n (Nat.lt_succ_diag_r n))
        (sumR_nat_fin (fun k (Hk : k < n) => f k (Nat.lt_lt_succ_r k n Hk))).
Proof.
  intros n f. unfold sumR_nat_fin. simpl. apply f_equal2;
  [ destruct (lt_dec n (S n)) as [H | H]; [ | exfalso; lia ];
    apply f_equal; apply proof_irrelevance
  | apply sumR_nat_eq; intros k Hk;
    destruct (lt_dec k (S n)) as [H | H]; [ | exfalso; lia ];
    destruct (lt_dec k n) as [H0 | H0]; [ | exfalso; lia ];
    simpl; apply f_equal; apply proof_irrelevance ].
Qed.

Lemma to_pcg_exp_sum_nat : forall n (f : fin n -> exp num) rho (Hn : n > 0),
  to_pcg_exp (sum (mkvSeq f)) rho = sumR_nat_fin (fun k Hk => to_pcg_exp (f (nat2fin Hk)) rho).
Proof.
  intros n f rho Hn. induction n as [| n' IHn].
  - inversion Hn.
  - destruct n' as [| n''].
    + rewrite sum_mkvSeq_Sn. rewrite to_pcg_exp_add. rewrite to_pcg_exp_sum_empty.
      unfold sumR_nat_fin. simpl. apply (f_equal2 Rplus);
      [ destruct (lt_dec 0 1) as [H1 | H1]; [ | exfalso; lia ];
        apply (f_equal (fun x : exp num => to_pcg_exp x rho));
        apply (f_equal f); apply fin_eq; simpl; auto
      | reflexivity ].
    + rewrite sum_mkvSeq_Sn. rewrite to_pcg_exp_add. rewrite IHn by lia.
      rewrite (@sumR_nat_fin_S (S n'') (fun k Hk => to_pcg_exp (f (nat2fin Hk)) rho)).
      apply f_equal2;
      [ destruct (lt_dec (S n'') (S (S n''))) as [H1 | H1]; [ | exfalso; lia ];
        apply (f_equal (fun x : exp num => to_pcg_exp x rho));
        apply (f_equal f); apply fin_eq; simpl; auto
      | apply sumR_nat_fin_eq; intros k Hk;
        apply (f_equal (fun x : exp num => to_pcg_exp x rho));
        apply (f_equal f); apply fin_eq; simpl; auto ].
Qed.


Lemma test_Rplus_0_r : forall x : R, (x + R0)%R = x.
Proof. intros. rewrite Rplus_0_r. reflexivity. Qed.
Lemma sumR_nat_nested_flat :
  forall m1 m2 (Hm1 : m1 > 0) (Hm2 : m2 > 0) (f : nat -> nat -> R),
    sumR_nat m1 (fun i => sumR_nat m2 (fun j => f i j)) =
    sumR_nat (m1 * m2) (fun k => f (k / m2) (k mod m2)).
Proof.
  intros m1 m2 Hm1 Hm2. induction m1 as [| m1' IHm1]; intro f.
  - reflexivity.
  - simpl.
    rewrite (sumR_nat_split m2 (m1' * m2) (fun k => f (k / m2) (k mod m2))).
    f_equal.
    + apply sumR_nat_eq. intros j Hj. apply f_equal2;
      [ rewrite Nat.div_add_l by lia; rewrite Nat.div_small by exact Hj; lia
      | rewrite Nat.add_comm; rewrite Nat.Div0.mod_add;
        rewrite Nat.mod_small by exact Hj; reflexivity ].
    + destruct m1' as [| m1''].
      * reflexivity.
      * apply IHm1; lia.
Qed.

Lemma sumR_nat_fin_nested_flat :
  forall m1 m2 (Hm1 : m1 > 0) (Hm2 : m2 > 0) (f : nat -> nat -> R),
    @sumR_nat_fin m1 (fun i (Hi : i < m1) => @sumR_nat_fin m2 (fun j (Hj : j < m2) => f i j)) =
    @sumR_nat_fin (m1 * m2) (fun k (Hk : k < m1 * m2) => f (k / m2) (k mod m2)).
Proof.
  intros m1 m2 Hm1 Hm2 f.
  unfold sumR_nat_fin at 1 2.
  replace (sumR_nat m1 (fun i : nat => match lt_dec i m1 with
              | left _ => sumR_nat m2 (fun j : nat => match lt_dec j m2 with
                                                | left _ => f i j
                                                | right _ => R0
                                                end)
              | right _ => R0
              end))
    with (sumR_nat m1 (fun i : nat => sumR_nat m2 (fun j : nat => f i j))).
  - rewrite sumR_nat_nested_flat by lia.
    apply sumR_nat_eq. intros k Hk.
    destruct (lt_dec k (m1 * m2)) as [Hk' | Hk']; [reflexivity | exfalso; lia].
  - apply sumR_nat_eq. intros i Hi. destruct (lt_dec i m1) as [Hi' | Hi']; [|exfalso; lia].
    apply sumR_nat_eq. intros j Hj.
    destruct (lt_dec j m2) as [Hj' | Hj']; [reflexivity | exfalso; lia].
Qed.

Lemma sumR_nat_fin_nested_flat' :
  forall m1 m2 (Hm1 : m1 > 0) (Hm2 : m2 > 0)
    (f : forall i j, i < m1 -> j < m2 -> R)
    (g : forall k, k < m1 * m2 -> R)
    (bounds : forall k, k < m1 * m2 -> (k / m2 < m1) /\
      (k mod m2 < m2)),
    (forall i j Hi1 Hi2 Hj1 Hj2, f i j Hi1 Hj1 = f i j Hi2 Hj2) ->
    (forall k Hk, g k Hk = match bounds k Hk with
                           | conj Hi Hj => f (k / m2) (k mod m2) Hi Hj
                           end) ->
    sumR_nat_fin (fun i (Hi : i < m1) => sumR_nat_fin (fun j (Hj : j < m2) => f i j Hi Hj)) =
    sumR_nat_fin (fun k (Hk : k < m1 * m2) => g k Hk).
Proof.
  intros m1 m2 Hm1 Hm2 f g bounds Hf Hg.
  set (g' := fun (i j : nat) =>
    match lt_dec i m1 with
    | left Hi =>
      match lt_dec j m2 with
      | left Hj => f i j Hi Hj
      | right _ => R0
      end
    | right _ => R0
    end).
  assert (Heq1 :
    sumR_nat_fin (fun i (Hi : i < m1) => sumR_nat_fin (fun j (Hj : j < m2) => f i j Hi Hj)) =
    sumR_nat m1 (fun i : nat => sumR_nat m2 (fun j : nat => g' i j))).
  { unfold sumR_nat_fin at 1 2.
    apply sumR_nat_eq. intros i Hi.
    destruct (lt_dec i m1) as [Hi' | Hi']; [| exfalso; lia ].
    replace (sumR_nat m2 (fun j : nat => match lt_dec j m2 with
                      | left Hj => f i j Hi' Hj
                      | right _ => R0
                      end))
      with (sumR_nat m2 (fun j : nat => g' i j));
      [| apply sumR_nat_eq; intros j Hj; unfold g';
         destruct (lt_dec i m1) as [Hi'' | Hi'']; [| contradiction ];
         destruct (lt_dec j m2) as [Hj' | Hj']; [| reflexivity ];
         rewrite (Hf i j Hi'' Hi' Hj' Hj'); reflexivity ].
    reflexivity. }
  assert (Heq2 :
    sumR_nat (m1 * m2) (fun k : nat => g' (k / m2) (k mod m2)) =
    sumR_nat_fin (fun k (Hk : k < m1 * m2) => g k Hk)).
  { unfold sumR_nat_fin.
    apply sumR_nat_eq. intros k Hk.
    replace (g' (k / m2) (k mod m2))
      with (match bounds k Hk with
            | conj Hi Hj => f (k / m2) (k mod m2) Hi Hj
            end);
      [| unfold g';
         destruct (lt_dec (k / m2) m1) as [Hi' | Hi'];
           [| exfalso; assert (Hk' : k / m2 < m1) by (apply Nat.div_lt_upper_bound; lia);
              lia ];
         destruct (lt_dec (k mod m2) m2) as [Hj' | Hj'];
           [| exfalso; assert (Hj'' : k mod m2 < m2) by (apply Nat.mod_upper_bound; lia);
              lia ];
         destruct (bounds k Hk) as [Hi Hj];
         rewrite (Hf (k / m2) (k mod m2) Hi' Hi Hj' Hj);
         reflexivity ].
    destruct (lt_dec k (m1 * m2)) as [Hk' | Hk']; [| exfalso; lia ].
    assert (Hbounds : bounds k Hk = bounds k Hk') by apply proof_irrelevance.
    rewrite Hbounds. symmetry. apply Hg. }
  rewrite Heq1. rewrite sumR_nat_nested_flat by lia. exact Heq2.
Qed.

(* ------------------------------------------------------------------------ *)
(* maxR: semantic evaluation of [CD.max] as a fold of [Rmax]                 *)
(* (mirrors the [sumR_nat] infrastructure for [CD.sum] above)                *)
(* ------------------------------------------------------------------------ *)

Fixpoint maxR_nat (n : nat) (f : nat -> R) : R :=
  match n with
  | 0 => R0
  | S n' => Rmax (f n') (maxR_nat n' f)
  end.

Lemma maxR_nat_eq : forall n (f g : nat -> R),
  (forall k, k < n -> f k = g k) -> maxR_nat n f = maxR_nat n g.
Proof.
  intros n f g H. induction n as [| n' IHn]; [reflexivity |].
  simpl. rewrite H by lia. rewrite IHn; [reflexivity |].
  intros k Hk. apply H. lia.
Qed.

Lemma maxR_nat_nonneg : forall n (f : nat -> R), (0 <= maxR_nat n f)%R.
Proof.
  intros n f. induction n as [| n' IHn]; simpl.
  - apply Rle_refl.
  - eapply Rle_trans; [exact IHn | apply Rmax_r].
Qed.

Lemma Rmax_0_nonneg_l : forall x : R, (0 <= x)%R -> Rmax R0 x = x.
Proof.
  intros x Hx. unfold Rmax. destruct (Rle_dec R0 x) as [H | H].
  - reflexivity.
  - exfalso. lra.
Qed.

Lemma maxR_nat_split : forall n1 n2 (f : nat -> R),
  maxR_nat (n1 + n2) f =
  Rmax (maxR_nat n1 (fun i => f (n2 + i)))
       (maxR_nat n2 f).
Proof.
  intros n1 n2. induction n1 as [| n1' IHn1]; intro f.
  - simpl. rewrite Rmax_0_nonneg_l by apply maxR_nat_nonneg. reflexivity.
  - simpl. rewrite IHn1.
    replace (n1' + n2) with (n2 + n1') by lia.
    rewrite Rmax_assoc. reflexivity.
Qed.

Definition maxR_nat_fin {n} (f : forall k, k < n -> R) : R :=
  maxR_nat n (fun k => match lt_dec k n with
                       | left H => f k H
                       | right _ => R0
                       end).

Lemma maxR_nat_fin_eq : forall n (f g : forall k, k < n -> R),
  (forall k Hk, f k Hk = g k Hk) -> maxR_nat_fin f = maxR_nat_fin g.
Proof.
  intros n f g H. unfold maxR_nat_fin. apply maxR_nat_eq. intros k Hk.
  destruct (lt_dec k n) as [H' | H']; [apply H | reflexivity].
Qed.

Lemma maxR_nat_fin_S : forall n (f : forall k, k < S n -> R),
  maxR_nat_fin f =
  Rmax (f n (Nat.lt_succ_diag_r n))
       (maxR_nat_fin (fun k (Hk : k < n) => f k (Nat.lt_lt_succ_r k n Hk))).
Proof.
  intros n f. unfold maxR_nat_fin. simpl. apply f_equal2;
  [ destruct (lt_dec n (S n)) as [H | H]; [ | exfalso; lia ];
    apply f_equal; apply proof_irrelevance
  | apply maxR_nat_eq; intros k Hk;
    destruct (lt_dec k (S n)) as [H | H]; [ | exfalso; lia ];
    destruct (lt_dec k n) as [H0 | H0]; [ | exfalso; lia ];
    simpl; apply f_equal; apply proof_irrelevance ].
Qed.

Lemma max_mkvSeq_Sn : forall n (f : fin (S n) -> exp num),
  max (mkvSeq f) = REif (gtExp (f (ltS n)) (max (mkvSeq (fun i : fin n => f (fin2finS i)))))
                        (f (ltS n))
                        (max (mkvSeq (fun i : fin n => f (fin2finS i)))).
Proof.
  intros n f. unfold max, CD.max, DE.mkvSeq. rewrite mk_vec_Sn. simpl. reflexivity.
Qed.

Lemma to_pcg_exp_max_empty : forall (f : fin 0 -> exp num) (rho : PCG.env),
  to_pcg_exp (max (mkvSeq f)) rho = R0.
Proof.
  intros f rho. unfold max, CD.max, DE.mkvSeq. simpl. rewrite to_pcg_exp_zero. reflexivity.
Qed.

(* The runtime conditional of [CD.max] computes [Rmax]. *)
Lemma Rgt_dec_if_Rmax : forall x y : R,
  (if match Rgt_dec x y with
      | left _ => true
      | right _ => false
      end then x else y) = Rmax x y.
Proof.
  intros x y. unfold Rmax.
  destruct (Rgt_dec x y) as [Hgt | Hngt]; destruct (Rle_dec x y) as [Hle | Hnle]; simpl.
  - exfalso. lra.
  - reflexivity.
  - reflexivity.
  - exfalso. lra.
Qed.

Lemma to_pcg_exp_max_nat : forall n (f : fin n -> exp num) rho (Hn : n > 0),
  to_pcg_exp (max (mkvSeq f)) rho = maxR_nat_fin (fun k Hk => to_pcg_exp (f (nat2fin Hk)) rho).
Proof.
  intros n f rho Hn. induction n as [| n' IHn].
  - inversion Hn.
  - destruct n' as [| n''].
    + rewrite max_mkvSeq_Sn. rewrite to_pcg_exp_REif. rewrite to_pcg_exp_BGt.
      rewrite Rgt_dec_if_Rmax. rewrite to_pcg_exp_max_empty.
      unfold maxR_nat_fin. simpl. apply (f_equal2 Rmax);
      [ destruct (lt_dec 0 1) as [H1 | H1]; [ | exfalso; lia ];
        apply (f_equal (fun x : exp num => to_pcg_exp x rho));
        apply (f_equal f); apply fin_eq; simpl; auto
      | reflexivity ].
    + rewrite max_mkvSeq_Sn. rewrite to_pcg_exp_REif. rewrite to_pcg_exp_BGt.
      rewrite Rgt_dec_if_Rmax. rewrite IHn by lia.
      rewrite (@maxR_nat_fin_S (S n'') (fun k Hk => to_pcg_exp (f (nat2fin Hk)) rho)).
      apply f_equal2;
      [ destruct (lt_dec (S n'') (S (S n''))) as [H1 | H1]; [ | exfalso; lia ];
        apply (f_equal (fun x : exp num => to_pcg_exp x rho));
        apply (f_equal f); apply fin_eq; simpl; auto
      | apply maxR_nat_fin_eq; intros k Hk;
        apply (f_equal (fun x : exp num => to_pcg_exp x rho));
        apply (f_equal f); apply fin_eq; simpl; auto ].
Qed.

Lemma maxR_nat_nested_flat :
  forall m1 m2 (Hm1 : m1 > 0) (Hm2 : m2 > 0) (f : nat -> nat -> R),
    maxR_nat m1 (fun i => maxR_nat m2 (fun j => f i j)) =
    maxR_nat (m1 * m2) (fun k => f (k / m2) (k mod m2)).
Proof.
  intros m1 m2 Hm1 Hm2. induction m1 as [| m1' IHm1]; intro f.
  - reflexivity.
  - simpl.
    rewrite (maxR_nat_split m2 (m1' * m2) (fun k => f (k / m2) (k mod m2))).
    f_equal.
    + apply maxR_nat_eq. intros j Hj. apply f_equal2;
      [ rewrite Nat.div_add_l by lia; rewrite Nat.div_small by exact Hj; lia
      | rewrite Nat.add_comm; rewrite Nat.Div0.mod_add;
        rewrite Nat.mod_small by exact Hj; reflexivity ].
    + destruct m1' as [| m1''].
      * reflexivity.
      * apply IHm1; lia.
Qed.

Lemma maxR_nat_fin_nested_flat :
  forall m1 m2 (Hm1 : m1 > 0) (Hm2 : m2 > 0) (f : nat -> nat -> R),
    @maxR_nat_fin m1 (fun i (Hi : i < m1) => @maxR_nat_fin m2 (fun j (Hj : j < m2) => f i j)) =
    @maxR_nat_fin (m1 * m2) (fun k (Hk : k < m1 * m2) => f (k / m2) (k mod m2)).
Proof.
  intros m1 m2 Hm1 Hm2 f.
  unfold maxR_nat_fin at 1 2.
  replace (maxR_nat m1 (fun i : nat => match lt_dec i m1 with
              | left _ => maxR_nat m2 (fun j : nat => match lt_dec j m2 with
                                                | left _ => f i j
                                                | right _ => R0
                                                end)
              | right _ => R0
              end))
    with (maxR_nat m1 (fun i : nat => maxR_nat m2 (fun j : nat => f i j))).
  - rewrite maxR_nat_nested_flat by lia.
    apply maxR_nat_eq. intros k Hk.
    destruct (lt_dec k (m1 * m2)) as [Hk' | Hk']; [reflexivity | exfalso; lia].
  - apply maxR_nat_eq. intros i Hi. destruct (lt_dec i m1) as [Hi' | Hi']; [|exfalso; lia].
    apply maxR_nat_eq. intros j Hj.
    destruct (lt_dec j m2) as [Hj' | Hj']; [reflexivity | exfalso; lia].
Qed.

Lemma maxR_nat_fin_nested_flat' :
  forall m1 m2 (Hm1 : m1 > 0) (Hm2 : m2 > 0)
    (f : forall i j, i < m1 -> j < m2 -> R)
    (g : forall k, k < m1 * m2 -> R)
    (bounds : forall k, k < m1 * m2 -> (k / m2 < m1) /\
      (k mod m2 < m2)),
    (forall i j Hi1 Hi2 Hj1 Hj2, f i j Hi1 Hj1 = f i j Hi2 Hj2) ->
    (forall k Hk, g k Hk = match bounds k Hk with
                           | conj Hi Hj => f (k / m2) (k mod m2) Hi Hj
                           end) ->
    maxR_nat_fin (fun i (Hi : i < m1) => maxR_nat_fin (fun j (Hj : j < m2) => f i j Hi Hj)) =
    maxR_nat_fin (fun k (Hk : k < m1 * m2) => g k Hk).
Proof.
  intros m1 m2 Hm1 Hm2 f g bounds Hf Hg.
  set (g' := fun (i j : nat) =>
    match lt_dec i m1 with
    | left Hi =>
      match lt_dec j m2 with
      | left Hj => f i j Hi Hj
      | right _ => R0
      end
    | right _ => R0
    end).
  assert (Heq1 :
    maxR_nat_fin (fun i (Hi : i < m1) => maxR_nat_fin (fun j (Hj : j < m2) => f i j Hi Hj)) =
    maxR_nat m1 (fun i : nat => maxR_nat m2 (fun j : nat => g' i j))).
  { unfold maxR_nat_fin at 1 2.
    apply maxR_nat_eq. intros i Hi.
    destruct (lt_dec i m1) as [Hi' | Hi']; [| exfalso; lia ].
    replace (maxR_nat m2 (fun j : nat => match lt_dec j m2 with
                      | left Hj => f i j Hi' Hj
                      | right _ => R0
                      end))
      with (maxR_nat m2 (fun j : nat => g' i j));
      [| apply maxR_nat_eq; intros j Hj; unfold g';
         destruct (lt_dec i m1) as [Hi'' | Hi'']; [| contradiction ];
         destruct (lt_dec j m2) as [Hj' | Hj']; [| reflexivity ];
         rewrite (Hf i j Hi'' Hi' Hj' Hj'); reflexivity ].
    reflexivity. }
  assert (Heq2 :
    maxR_nat (m1 * m2) (fun k : nat => g' (k / m2) (k mod m2)) =
    maxR_nat_fin (fun k (Hk : k < m1 * m2) => g k Hk)).
  { unfold maxR_nat_fin.
    apply maxR_nat_eq. intros k Hk.
    replace (g' (k / m2) (k mod m2))
      with (match bounds k Hk with
            | conj Hi Hj => f (k / m2) (k mod m2) Hi Hj
            end);
      [| unfold g';
         destruct (lt_dec (k / m2) m1) as [Hi' | Hi'];
           [| exfalso; assert (Hk' : k / m2 < m1) by (apply Nat.div_lt_upper_bound; lia);
              lia ];
         destruct (lt_dec (k mod m2) m2) as [Hj' | Hj'];
           [| exfalso; assert (Hj'' : k mod m2 < m2) by (apply Nat.mod_upper_bound; lia);
              lia ];
         destruct (bounds k Hk) as [Hi Hj];
         rewrite (Hf (k / m2) (k mod m2) Hi' Hi Hj' Hj);
         reflexivity ].
    destruct (lt_dec k (m1 * m2)) as [Hk' | Hk']; [| exfalso; lia ].
    assert (Hbounds : bounds k Hk = bounds k Hk') by apply proof_irrelevance.
    rewrite Hbounds. symmetry. apply Hg. }
  rewrite Heq1. rewrite maxR_nat_nested_flat by lia. exact Heq2.
Qed.

(* [max] preserves path/acceptor independence (mirrors [exp_independent_path_sum]). *)
Lemma exp_independent_path_max :
  forall n (e : exp (ary '{n} num)) (p : DE.path),
    (forall i, exp_independent_of_path (DE.idx e i) p) ->
    exp_independent_of_path (CD.max e) p.
Proof.
  intros n. induction n as [| n' IHn]; intros e p Hindep.
  - exact I.
  - rewrite (max_Sn e). simpl. repeat split.
    + apply Hindep.
    + apply IHn. intro i. rewrite <- idx_fin2finS_eq. apply Hindep.
    + apply Hindep.
    + apply IHn. intro i. rewrite <- idx_fin2finS_eq. apply Hindep.
Qed.

Lemma exp_independent_of_acc_max :
  forall n d' (e : exp (ary '{n} num)) (a : acc d'),
    (forall i, exp_independent_of_acc (DE.idx e i) a) ->
    exp_independent_of_acc (CD.max e) a.
Proof.
  intros n d' e a Hin q Hq. apply exp_independent_path_max. intros i.
  apply Hin. exact Hq.
Qed.

Section GlobalAvgPool4d_Sem.

  Variables (batch channel m1 m2 : nat)
            (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
            (Hbatch : batch > 0) (Hchannel : channel > 0)
            (Hm1 : m1 > 0) (Hm2 : m2 > 0).

  Let tmp_scalar_acc : acc num := @PCG.acc' num tmp_path.

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{batch} (ary '{channel} num))),
    exp_independent_of_acc input output.

  Definition tmp_disjoint_from_output_gap
    (output : acc (ary '{batch} (ary '{channel} num))) : Prop :=
    forall p b c, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ b} |{ c}).

  Definition GAP_flat_cell (b : fin batch) (c : fin channel) (k : fin (m1 * m2)) : exp num :=
    let i := Nat.div (fin2nat k) m2 in
    let j := Nat.modulo (fin2nat k) m2 in
    safe_idx_nat (safe_idx_nat input|[b]|[c] i) j.

  Lemma GAP_flat_index_bounds :
    forall (k : fin (m1 * m2)),
      Nat.div (fin2nat k) m2 < m1 /\
      Nat.modulo (fin2nat k) m2 < m2.
  Proof.
    intro k. destruct k as [k Hk]. simpl.
    split.
    - apply Nat.div_lt_upper_bound; [lia |].
      rewrite Nat.mul_comm. exact Hk.
    - apply Nat.mod_upper_bound. lia.
  Qed.

  Lemma GAP_flat_cell_unfold :
    forall (b : fin batch) (c : fin channel) (k : fin (m1 * m2)),
      GAP_flat_cell b c k =
      input|[b]|[c]|[nat2fin (proj1 (GAP_flat_index_bounds k))]|[nat2fin (proj2 (GAP_flat_index_bounds k))].
  Proof.
    intros b c k. unfold GAP_flat_cell.
    destruct (GAP_flat_index_bounds k) as [Hi Hj].
    replace (safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat k / m2)) (fin2nat k mod m2))
      with (input|[b]|[c]|[nat2fin Hi]|[nat2fin Hj]) by
      (unfold safe_idx_nat;
       destruct (Nat.ltb_spec0 (fin2nat k / m2) m1) as [Hi' | Hi']; [| contradiction ];
       destruct (Nat.ltb_spec0 (fin2nat k mod m2) m2) as [Hj' | Hj']; [| contradiction ];
       reflexivity).
    reflexivity.
  Qed.

  Lemma GAP_nested_sum_flat :
    forall (b : fin batch) (c : fin channel) (rho : PCG.env),
      to_pcg_exp (sum (mkvSeq (fun i : fin m1 => sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) rho =
      to_pcg_exp (sum (mkvSeq (GAP_flat_cell b c))) rho.
  Proof.
    intros b c rho.
    set (idx_cell := fun (i j : nat) (Hi : i < m1) (Hj : j < m2) =>
      input|[b]|[c]|[nat2fin Hi]|[nat2fin Hj]).
    assert (Heq_lhs :
      to_pcg_exp (sum (mkvSeq (fun i : fin m1 => sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) rho =
      sumR_nat_fin (fun i (Hi : i < m1) => sumR_nat_fin (fun j (Hj : j < m2) => to_pcg_exp (idx_cell i j Hi Hj) rho))).
    { rewrite to_pcg_exp_sum_nat by lia.
      apply sumR_nat_fin_eq. intros i Hi.
      rewrite to_pcg_exp_sum_nat by lia.
      apply sumR_nat_fin_eq. intros j Hj.
      reflexivity. }
    assert (Heq_rhs :
      to_pcg_exp (sum (mkvSeq (GAP_flat_cell b c))) rho =
      sumR_nat_fin (fun k (Hk : k < m1 * m2) => to_pcg_exp (GAP_flat_cell b c (nat2fin Hk)) rho)).
    { rewrite to_pcg_exp_sum_nat by lia. reflexivity. }
    rewrite Heq_lhs, Heq_rhs.
    pose (lemma := @sumR_nat_fin_nested_flat' m1 m2 Hm1 Hm2
      (fun i j Hi Hj => to_pcg_exp (idx_cell i j Hi Hj) rho)
      (fun k Hk => to_pcg_exp (GAP_flat_cell b c (nat2fin Hk)) rho)
      (fun k Hk => GAP_flat_index_bounds (nat2fin Hk))).
    apply lemma; [ intros i j Hi1 Hi2 Hj1 Hj2;
         unfold idx_cell;
         repeat rewrite to_pcg_exp_idx;
         f_equal;
         apply fin_eq; rewrite !fin2nat_nat2fin; reflexivity
       | intros k Hk;
         unfold GAP_flat_cell, idx_cell;
         destruct (GAP_flat_index_bounds (nat2fin Hk)) as [Hi Hj];
         unfold safe_idx_nat;
         destruct (Nat.ltb_spec0 (fin2nat (nat2fin Hk) / m2) m1) as [Hi' | Hi']; [| contradiction ];
         destruct (Nat.ltb_spec0 (fin2nat (nat2fin Hk) mod m2) m2) as [Hj' | Hj']; [| contradiction ];
         reflexivity ].
  Qed.

  Lemma GlobalAvgPool4d_cell_independent_of_output :
    forall (output : acc (ary '{batch} (ary '{channel} num))) (b : fin batch) (c : fin channel),
      exp_independent_of_acc
        (div_n (sum (mkvSeq (fun i : fin m1 => sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) (m1 * m2))
        output.
  Proof.
    intros output b c.
    apply exp_independent_of_acc_div_n.
    apply exp_independent_of_acc_sum. intro i.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    apply exp_independent_of_acc_sum. intro j.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    repeat apply exp_independent_of_acc_idx. apply Hinput_out.
  Qed.

  Lemma GlobalAvgPool4d_cell_continuation_ok :
    forall (output : acc (ary '{batch} (ary '{channel} num))) (b : fin batch) (c : fin channel),
      tmp_disjoint_from_output_gap output ->
      loopacc_continuation_ok
        (fun r : exp num => output|{b}|{c} |:= div_n r (m1 * m2))
        (sum (mkvSeq (GAP_flat_cell b c))).
  Proof.
    intros output b c Hdisj.
    assert (Hin_bc : exp_independent_of_acc (input|[b]|[c]) tmp_scalar_acc).
    { apply exp_independent_of_acc_idx.
      apply exp_independent_of_acc_idx.
      exact Hinput_indep. }
    apply scalar_assign_continuation_ok.
    - (* output cell is disjoint from __tmp *)
      intros p Hp. apply Hdisj. exact Hp.
    - (* the summed expression is independent of __tmp *)
      apply exp_independent_of_acc_sum. intro k.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold GAP_flat_cell.
      repeat apply safe_idx_nat_independent.
      exact Hin_bc.
    - (* div_n of the sum is independent of __tmp *)
      apply exp_independent_of_acc_div_n.
      apply exp_independent_of_acc_sum. intro k.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold GAP_flat_cell.
      repeat apply safe_idx_nat_independent.
      exact Hin_bc.
    - (* div_n agrees when reading __tmp vs. using the functional result *)
      intros rho eta v Hv Heta.
      rewrite !to_pcg_exp_div_n.
      f_equal.
      rewrite to_pcg_exp_REvar_tmp'.
      rewrite value_at_update_same.
      symmetry. exact Hv.
  Qed.

  Theorem GlobalAvgPool4d_sem :
    forall (output : acc (ary '{batch} (ary '{channel} num))) (rho : PCG.env),
      tmp_disjoint_from_output_gap output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @GlobalAvgPool4d batch channel m1 m2 input)) rho =
      eval (@GlobalAvgPool4d_comm batch channel m1 m2 input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, GlobalAvgPool4d, GlobalAvgPool4d_comm.
    set (row := fun b : fin batch => mkvSeq (fun c : fin channel =>
      div_n (sum (mkvSeq (fun i : fin m1 =>
        sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) (m1 * m2))).
    assert (Hrow_indep : forall b, exp_independent_of_acc (row b) output).
    { intros b. unfold row. apply exp_independent_of_acc_mkvSeq. intros c.
      apply GlobalAvgPool4d_cell_independent_of_output. }
    rewrite eval_mkvSeq; [ | intros b; apply Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros b eta HPeta. split.
    - (* Row-level equivalence. *)
      assert (Hcell_indep_b : forall c,
        exp_independent_of_acc
          (div_n (sum (mkvSeq (fun i : fin m1 =>
            sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) (m1 * m2))
          (output |{ b})).
      { intros c. unfold exp_independent_of_acc. intros p Hp.
        apply (@GlobalAvgPool4d_cell_independent_of_output output b c).
        simpl in Hp. destruct Hp as [c' Hc'].
        simpl. exists b. exists c'. exact Hc'. }
      unfold row in |- *. rewrite eval_mkvSeq; [ | intros c; apply Hcell_indep_b ].
      rewrite !eval_seqfor.
      apply seqfor_pointwise_inv with (P := P); [exact HPeta |].
      intros c eta' HPeta'. split.
      + set (e := mkvSeq (GAP_flat_cell b c)).
        set (c' := fun r : exp num => (output|{b}|{c}) |:= div_n r (m1 * m2)).
        assert (Hrhs : (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun k : fin (m1 * m2) =>
              vwt tmp |:= add (safe_idx_nat (safe_idx_nat input|[b]|[c]
                (Nat.div (fin2nat k) m2)) (Nat.modulo (fin2nat k) m2)) (vrd tmp))
            '; (output|{b}|{c}) |:= div_n (vrd tmp) (m1 * m2)))
          = (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun k : fin (m1 * m2) =>
              vwt tmp |:= add e|[k] (vrd tmp))
            '; (output|{b}|{c}) |:= div_n (vrd tmp) (m1 * m2)))).
        { f_equal. apply functional_extensionality; intro tmp.
          assert (Hfor : seqfor (fun k : fin (m1 * m2) =>
                          vwt tmp |:= add (safe_idx_nat (safe_idx_nat input|[b]|[c]
                            (Nat.div (fin2nat k) m2)) (Nat.modulo (fin2nat k) m2)) (vrd tmp))
                      = seqfor (fun k : fin (m1 * m2) =>
                          vwt tmp |:= add e|[k] (vrd tmp))).
          { apply seqfor_extensionality; intro k.
            assert (Heq : safe_idx_nat (safe_idx_nat input|[b]|[c]
                            (Nat.div (fin2nat k) m2)) (Nat.modulo (fin2nat k) m2) = e|[k]).
            { unfold e, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
            rewrite Heq. reflexivity. }
          rewrite Hfor. reflexivity. }
        rewrite Hrhs.
        rewrite eval_assign.
        rewrite <- (eval_assign_aux 1 num _ _ eta').
        change (eval_aux (c' (sum (mkvSeq (fun i : fin m1 =>
          sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j])))))) 1 eta' =
          eval (@loopacc num (fun tmp : string =>
            let wtmp := vwt tmp in let v := vrd tmp in
            wtmp |:= zero '; seqfor (fun k : fin (m1 * m2) =>
              wtmp |:= add e|[k] v)
            '; c' v)) eta').
        assert (Hsum_eq : to_pcg_exp (sum (mkvSeq (fun i : fin m1 =>
          sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j]))))) eta' =
          to_pcg_exp (sum e) eta').
        { unfold e. apply GAP_nested_sum_flat. }
        assert (Heq_aux : eval_aux (c' (sum (mkvSeq (fun i : fin m1 =>
          sum (mkvSeq (fun j : fin m2 => input|[b]|[c]|[i]|[j])))))) 1 eta' =
          eval_aux (c' (sum e)) 1 eta').
        { unfold c'. rewrite !eval_assign_aux. f_equal.
          rewrite !to_pcg_exp_div_n. f_equal. exact Hsum_eq. }
        rewrite Heq_aux.
        apply eval_csum_equiv.
        * exact HPeta'.
        * unfold e. apply exp_independent_of_acc_mkvSeq. intro k.
          unfold GAP_flat_cell. repeat apply safe_idx_nat_independent.
          apply exp_independent_of_acc_idx. apply exp_independent_of_acc_idx.
          exact Hinput_indep.
        * apply GlobalAvgPool4d_cell_continuation_ok. exact Hdisj.
      + rewrite eval_assign.
        apply assign_preserves_StructUndefined_tmp.
        * intros p Hp Hout. apply (Hdisj p b c Hp). exact Hout.
        * exact HPeta'.
    - rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta tmp_path).
      + unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros c rho'. apply PCG.assign_not_in_acc.
        intros Hc. apply (Hdisj tmp_path b c in_acc_tmp_scalar_acc). exact Hc.
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End GlobalAvgPool4d_Sem.

(* ------------------------------------------------------------------------ *)
(* Generic seqfor decomposition for row-major nested loops                  *)
(* ------------------------------------------------------------------------ *)

Definition fin_shift_l {p q : nat} (k : fin p) : fin (p + q) :=
  @nat2fin (p + q) (fin2nat k)
    (Nat.lt_le_trans _ _ _ (fin_proof k) (Nat.le_add_r p q)).

Definition fin_shift_r {p q : nat} (k : fin q) : fin (p + q) :=
  @nat2fin (p + q) (p + fin2nat k)
    (proj1 (Nat.add_lt_mono_l _ _ p) (fin_proof k)).

Definition fin_cast {n m : nat} (H : n = m) (k : fin n) : fin m :=
  eq_rect n fin k m H.

Lemma fin_cast_nat : forall n m (H : n = m) (k : fin n),
  fin2nat (fin_cast H k) = fin2nat k.
Proof.
  intros. unfold fin_cast. destruct H. reflexivity.
Qed.

Lemma fin2nat_shift_l : forall p q (k : fin p), fin2nat (@fin_shift_l p q k) = fin2nat k.
Proof.
  intros. unfold fin_shift_l. destruct k as [k Hk]. simpl. auto.
Qed.

Lemma fin2nat_shift_r : forall p q (k : fin q), fin2nat (@fin_shift_r p q k) = p + fin2nat k.
Proof.
  intros. unfold fin_shift_r. destruct k as [k Hk]. simpl. auto.
Qed.

Lemma seqfor_fin1 : forall (f : fin 1 -> PCG.comm), PCG.seqfor f = f '[0].
Proof.
  intros. rewrite PCG.seqfor_Sn. simpl. rewrite PCG.skip_l. reflexivity.
Qed.

Lemma seqfor_body_cast :
  forall n m (H : n = m) (body : fin n -> PCG.comm),
    PCG.seqfor body =
    PCG.seqfor (fun k : fin m => body (fin_cast (eq_sym H) k)).
Proof.
  intros n m H body.
  apply functional_extensionality; intro rho.
  case H. simpl. reflexivity.
Qed.

Lemma seqfor_app_Sn :
  forall n p q (H : S n = p + q) (body : fin (S n) -> PCG.comm),
    q > 0 ->
    PCG.seqfor body =
    PCG.seq (PCG.seqfor (fun k : fin p => body (fin_cast (eq_sym H) (@fin_shift_l p q k))))
            (PCG.seqfor (fun k : fin q => body (fin_cast (eq_sym H) (@fin_shift_r p q k)))).
Proof.
  induction n as [| n' IHn']; intros p q H body Hq.
  - (* n = 0, so S 0 = 1 = p + q, q > 0 implies p = 0, q = 1 *)
    assert (Hp : p = 0) by lia. assert (Hq1 : q = 1) by lia.
    subst p q. simpl in H.
    assert (Heq0 : '[0] = fin_cast (eq_sym H) (@fin_shift_r 0 1 '[0])).
    { apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
    apply functional_extensionality; intro rho.
    rewrite PCG.seqfor_Sn. cbn [PCG.seqfor]. unfold PCG.seq. simpl.
    rewrite Heq0 at 1. reflexivity.
  - (* n = S n', so S (S n') = p + q *)
    destruct q as [| q'].
    + inversion Hq.
    + destruct q' as [| q''].
      * (* q = 1, so p = S n' *)
        assert (Hp : p = S n') by lia. subst p.
        apply functional_extensionality; intro rho.
        rewrite PCG.seqfor_Sn.
        assert (Heq1 : PCG.seqfor (fun i : fin (S n') => body FS[i]) =
                       PCG.seqfor (fun k : fin (S n') => body (fin_cast (eq_sym H) (@fin_shift_l (S n') 1 k)))).
        { apply PCG.seqfor_extensionality. intro k. f_equal.
          apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        assert (Heq2 : '[S n'] = fin_cast (eq_sym H) (@fin_shift_r (S n') 1 '[0])).
        { apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        rewrite Heq1. rewrite Heq2 at 1.
        cbn [PCG.seqfor]. unfold PCG.seq. simpl. reflexivity.
      * (* q = S (S q''), so S n' = p + S q'' *)
        assert (Heq : S n' = p + S q'') by lia.
        apply functional_extensionality; intro rho.
        rewrite PCG.seqfor_Sn.
        rewrite IHn' with (H := Heq) (body := fun i : fin (S n') => body FS[i]);
          [ | lia ].
        assert (Heq1 : PCG.seqfor (fun k : fin p => body FS[fin_cast (eq_sym Heq) (@fin_shift_l p (S q'') k)]) =
                       PCG.seqfor (fun k : fin p => body (fin_cast (eq_sym H) (@fin_shift_l p (S (S q'')) k)))).
        { apply PCG.seqfor_extensionality. intro k. f_equal.
          apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        assert (Heq2 : PCG.seqfor (fun k : fin (S q'') => body FS[fin_cast (eq_sym Heq) (@fin_shift_r p (S q'') k)]) =
                       PCG.seqfor (fun k : fin (S q'') => body (fin_cast (eq_sym H) (@fin_shift_r p (S (S q'')) FS[k])))).
        { apply PCG.seqfor_extensionality. intro k. f_equal.
          apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        assert (Heq3 : '[S n'] = fin_cast (eq_sym H) (@fin_shift_r p (S (S q'')) '[S q''])).
        { apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        rewrite Heq1, Heq2, Heq3 at 1.
        rewrite PCG.seqfor_Sn.
        cbn [PCG.seqfor]. unfold PCG.seq. simpl. reflexivity.
Qed.

Lemma seqfor_app :
  forall p q (body : fin (p + q) -> PCG.comm),
    q > 0 ->
    PCG.seqfor body =
    PCG.seq (PCG.seqfor (fun k : fin p => body (fin_shift_l k)))
            (PCG.seqfor (fun k : fin q => body (fin_shift_r k))).
Proof.
  intros p q body Hq.
  induction q as [| q' IHq'].
  - lia.
  - destruct q' as [| q''].
    + (* q = 1, p + 1 = S p *)
      assert (Heq : p + 1 = S p) by lia.
      assert (Hcast := @seqfor_body_cast (p + 1) (S p) Heq body).
      rewrite Hcast.
      rewrite PCG.seqfor_Sn.
      rewrite (seqfor_fin1 (fun k : fin 1 => body (fin_shift_r k))).
      f_equal.
      * apply PCG.seqfor_extensionality. intro k. f_equal.
        apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l; auto.
      * f_equal. apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r; auto.
    + (* q = S (S q''), p + S (S q'') = S (p + S q'') *)
      assert (Heq : p + S (S q'') = S (p + S q'')) by lia.
      assert (Hcast := @seqfor_body_cast (p + S (S q'')) (S (p + S q'')) Heq body).
      rewrite Hcast.
      rewrite PCG.seqfor_Sn.
      assert (Hind := IHq' (fun i : fin (p + S q'') => body (fin_cast (eq_sym Heq) (fin2finS i))) ltac:(lia)).
      rewrite Hind. rewrite <- PCG.seq_assoc.
      f_equal.
      * apply PCG.seqfor_extensionality. intro k. f_equal.
        apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_fin2finS; auto.
      * assert (HR : PCG.seqfor (fun k : fin (S (S q'')) => body (fin_shift_r k)) =
                     PCG.seq (PCG.seqfor (fun i : fin (S q'') => body (fin_shift_r FS[i])))
                             (body (fin_shift_r '[S q'']))).
        { apply PCG.seqfor_Sn. }
        rewrite HR.
        f_equal.
        -- apply PCG.seqfor_extensionality. intro k. f_equal.
           apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto.
        -- f_equal. apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r; auto.
Qed.

Lemma seqfor_2d :
  forall m n (Hm : m > 0) (Hn : n > 0) (body : fin (m * n) -> PCG.comm),
    PCG.seqfor body =
    PCG.seqfor (fun i : fin m => PCG.seqfor (fun j : fin n => body (idx_2d_to_1d i j))).
Proof.
  induction m as [| m' IHm']; intros n Hm Hn body.
  - lia.
  - destruct m' as [| m''].
    + assert (Heq : 1 * n = n) by (apply Nat.mul_1_l).
      rewrite (@seqfor_body_cast (1 * n) n Heq body).
      rewrite seqfor_fin1.
      apply PCG.seqfor_extensionality. intro j.
      f_equal.
      apply fin_eq; simpl; rewrite ?fin_cast_nat.
      unfold idx_2d_to_1d. simpl. destruct j as [j Hj]. lia.
    + assert (Heq : S (S m'') * n = S m'' * n + n) by lia.
      rewrite (@seqfor_body_cast (S (S m'') * n) (S m'' * n + n) Heq body).
      rewrite (@seqfor_app (S m'' * n) n (fun k => body (fin_cast (eq_sym Heq) k))) by lia.
      rewrite IHm' with (body := fun k : fin (S m'' * n) => body (fin_cast (eq_sym Heq) (fin_shift_l k)));
        [ | lia | lia ].
      assert (HR : PCG.seqfor (fun i : fin (S (S m'')) => PCG.seqfor (fun j : fin n => body (idx_2d_to_1d i j))) =
                   PCG.seq (PCG.seqfor (fun i : fin (S m'') => PCG.seqfor (fun j : fin n => body (idx_2d_to_1d FS[i] j))))
                           (PCG.seqfor (fun j : fin n => body (idx_2d_to_1d '[S m''] j)))).
      { apply PCG.seqfor_Sn. }
      rewrite HR.
      f_equal.
      * apply PCG.seqfor_extensionality. intro i.
        apply PCG.seqfor_extensionality. intro j. f_equal.
        apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l.
        unfold idx_2d_to_1d. simpl. lia.
      * apply PCG.seqfor_extensionality. intro j. f_equal.
        apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r.
        unfold idx_2d_to_1d. simpl. lia.
Qed.

(* Convenience corollary of [seqfor_2d] that avoids the administrative
   [idx_2d_to_1d] wrapper inside the nested body. *)
Lemma seqfor_2d_body :
  forall m n (Hm : m > 0) (Hn : n > 0) (body : fin m -> fin n -> PCG.comm),
    PCG.seqfor (fun i : fin m => PCG.seqfor (fun j : fin n => body i j)) =
    PCG.seqfor (fun k : fin (m * n) =>
      let '(i, j) := idx_1d_to_2d k in body i j).
Proof.
  intros m n Hm Hn body.
  assert (H := @seqfor_2d m n Hm Hn (fun k : fin (m * n) =>
    let '(i, j) := idx_1d_to_2d k in body i j)).
  rewrite H. apply PCG.seqfor_extensionality. intro i.
  apply PCG.seqfor_extensionality. intro j.
  rewrite idx_1d_to_2d_after_idx_2d_to_1d. reflexivity.
Qed.

(* Lifting of [seqfor_2d_body] to [CG.seqfor] through the interpreter.
   The right-hand side is already a flat [PCG.seqfor] so no further
   [eval_seqfor] steps are needed. *)
Lemma seqfor_2d_CG :
  forall m n (Hm : m > 0) (Hn : n > 0) (body : fin m -> fin n -> CG.comm),
    eval (CG.seqfor (fun i : fin m => CG.seqfor (fun j : fin n => body i j))) =
    PCG.seqfor (fun k : fin (m * n) =>
      let '(i, j) := idx_1d_to_2d k in eval (body i j)).
Proof.
  intros m n Hm Hn body. apply functional_extensionality. intro rho.
  rewrite !eval_seqfor.
  assert (Heq : PCG.seqfor (fun i : fin m =>
      eval (CG.seqfor (fun j : fin n => body i j))) =
    PCG.seqfor (fun i : fin m => PCG.seqfor (fun j : fin n => eval (body i j)))).
  { apply f_equal. apply functional_extensionality. intro i.
    apply functional_extensionality. intro rho'.
    rewrite eval_seqfor. reflexivity. }
  rewrite Heq.
  rewrite (seqfor_2d_body Hm Hn (fun i j => eval (body i j))).
  reflexivity.
Qed.


(* ------------------------------------------------------------------------ *)
(* Flatten4d semantic equivalence                                          *)
(* ------------------------------------------------------------------------ *)

Section Flatten4d_Sem.

  Variables (batch channel m1 m2 : nat)
            (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))).

  Hypothesis Hchannel : channel > 0.
  Hypothesis Hm1 : m1 > 0.
  Hypothesis Hm2 : m2 > 0.

  (* Input must be independent of the output acceptor so that [eval_mkvSeq]
     applies. *)
  Hypothesis Hinput_out : forall (output : acc (ary '{batch} (ary '{channel * m1 * m2} num))),
    exp_independent_of_acc input output.

  (* [join] is definitionally a [mkvSeq] over [idx_1d_to_2d]. *)
  Lemma join_mkvSeq :
    forall {m n} {t:data} (e : exp (ary '{m} (ary '{n} t))),
      join e = DE.mkvSeq (fun k : fin (m * n) =>
        let '(i, j) := idx_1d_to_2d k in e|[i]|[j]).
  Proof.
    intros m n t e.
    unfold join, DE.mkvSeq, CNN_Defs.join, V.v_join.
    apply V.mk_vec_ext. intro k. reflexivity.
  Qed.

  (* The [flatten_idx] used in [Flatten4d_comm] is exactly the 2D->1D encoding
     with [m1*m2] as the inner dimension. *)
  Lemma flatten_idx_as_idx_2d_to_1d :
    forall (c : fin channel) (i : fin m1) (j : fin m2),
      fin2nat (flatten_idx c i j) = fin2nat (idx_2d_to_1d c (idx_2d_to_1d i j)).
  Proof.
    intros c i j. unfold flatten_idx, idx_2d_to_1d. simpl. ring.
  Qed.

  (* For a flat index k in [(channel * m1) * m2], decoding it twice with
     [idx_1d_to_2d] yields the same (c, i, j) triple as [flatten_idx], up to
     the associativity of multiplication. *)
  Lemma flatten_idx_1d_to_2d :
    forall (k : fin ((channel * m1) * m2)),
    let (ci, j) := idx_1d_to_2d k in
    let (c, i) := idx_1d_to_2d ci in
      fin2nat k = fin2nat (flatten_idx c i j).
  Proof.
    intro k. destruct (idx_1d_to_2d k) as [ci j] eqn:Hck.
    destruct (idx_1d_to_2d ci) as [c i] eqn:Hci.
    rewrite (flatten_idx_as_idx_2d_to_1d c i j).
    assert (Hk : fin2nat k = fin2nat (idx_2d_to_1d ci j)).
    { rewrite <- (idx_2d_to_1d_after_idx_1d_to_2d (channel * m1) m2 k).
      rewrite Hck. reflexivity. }
    assert (Hci' : fin2nat ci = fin2nat (idx_2d_to_1d c i)).
    { rewrite <- (idx_2d_to_1d_after_idx_1d_to_2d channel m1 ci).
      rewrite Hci. reflexivity. }
    unfold idx_2d_to_1d in Hk, Hci' |- *. simpl in Hk, Hci' |- *.
    rewrite Hk, Hci'. ring.
  Qed.

  Lemma flatten_idx_1d_to_2d_cast :
    forall (k : fin (channel * (m1 * m2))),
    let (c, k_inner) := idx_1d_to_2d k in
    let (i, j) := idx_1d_to_2d k_inner in
      fin_cast (Nat.mul_assoc channel m1 m2) k = flatten_idx c i j.
  Proof.
    intros k. destruct (idx_1d_to_2d k) as [c k_inner] eqn:Hck.
    destruct (idx_1d_to_2d k_inner) as [i j] eqn:Hki.
    apply fin_eq. simpl.
    rewrite fin_cast_nat.
    unfold flatten_idx. simpl.
    assert (Hk : fin2nat k = fin2nat (idx_2d_to_1d c k_inner)).
    { rewrite <- (idx_2d_to_1d_after_idx_1d_to_2d channel (m1 * m2) k).
      rewrite Hck. reflexivity. }
    assert (Hki' : fin2nat k_inner = fin2nat (idx_2d_to_1d i j)).
    { rewrite <- (idx_2d_to_1d_after_idx_1d_to_2d m1 m2 k_inner).
      rewrite Hki. reflexivity. }
    unfold idx_2d_to_1d in Hk, Hki' |- *. simpl in Hk, Hki' |- *.
    rewrite Hk, Hki'. ring.
  Qed.


  (* [flatten_idx] is injective: the row-major encoding of (c,i,j) uniquely
     determines the three indices. *)
  Lemma flatten_idx_injective :
    forall (c1 c2 : fin channel) (i1 i2 : fin m1) (j1 j2 : fin m2),
      flatten_idx c1 i1 j1 = flatten_idx c2 i2 j2 ->
      c1 = c2 /\ i1 = i2 /\ j1 = j2.
  Proof.
    intros c1 c2 i1 i2 j1 j2 H.
    pose proof (f_equal fin2nat H) as Hnat.
    destruct c1 as [c1 Hc1]. destruct c2 as [c2 Hc2].
    destruct i1 as [i1 Hi1]. destruct i2 as [i2 Hi2].
    destruct j1 as [j1 Hj1]. destruct j2 as [j2 Hj2].
    unfold fin2nat, flatten_idx in Hnat. simpl in Hnat.
    replace ((c1 * m1) * m2 + i1 * m2 + j1) with ((c1 * m1 + i1) * m2 + j1) in Hnat by ring.
    replace ((c2 * m1) * m2 + i2 * m2 + j2) with ((c2 * m1 + i2) * m2 + j2) in Hnat by ring.
    assert (Hj : j1 = j2).
    { assert (Hmod : ((c1 * m1 + i1) * m2 + j1) mod m2 = ((c2 * m1 + i2) * m2 + j2) mod m2) by (rewrite Hnat; reflexivity).
      assert (Hleft : ((c1 * m1 + i1) * m2 + j1) mod m2 = j1).
      { replace (((c1 * m1 + i1) * m2 + j1)) with (j1 + (c1 * m1 + i1) * m2) by ring.
        rewrite Nat.mod_add by (apply Nat.neq_0_lt_0; assumption).
        apply Nat.mod_small. assumption. }
      assert (Hright : ((c2 * m1 + i2) * m2 + j2) mod m2 = j2).
      { replace (((c2 * m1 + i2) * m2 + j2)) with (j2 + (c2 * m1 + i2) * m2) by ring.
        rewrite Nat.mod_add by (apply Nat.neq_0_lt_0; assumption).
        apply Nat.mod_small. assumption. }
      rewrite Hleft, Hright in Hmod. exact Hmod. }
    assert (Hi : i1 = i2).
    { assert (Hdiv : ((c1 * m1 + i1) * m2 + j1) / m2 = ((c2 * m1 + i2) * m2 + j2) / m2) by (rewrite Hnat; reflexivity).
      assert (Hleft : ((c1 * m1 + i1) * m2 + j1) / m2 = c1 * m1 + i1).
      { replace (((c1 * m1 + i1) * m2 + j1)) with (j1 + (c1 * m1 + i1) * m2) by ring.
        rewrite Nat.div_add by (apply Nat.neq_0_lt_0; assumption).
        replace (j1 / m2) with 0 by (symmetry; apply Nat.div_small; assumption).
        reflexivity. }
      assert (Hright : ((c2 * m1 + i2) * m2 + j2) / m2 = c2 * m1 + i2).
      { replace (((c2 * m1 + i2) * m2 + j2)) with (j2 + (c2 * m1 + i2) * m2) by ring.
        rewrite Nat.div_add by (apply Nat.neq_0_lt_0; assumption).
        replace (j2 / m2) with 0 by (symmetry; apply Nat.div_small; assumption).
        reflexivity. }
      rewrite Hleft, Hright in Hdiv.
      assert (Hmod : (i1 + c1 * m1) mod m1 = (i2 + c2 * m1) mod m1).
      { replace (c1 * m1 + i1) with (i1 + c1 * m1) in Hdiv by ring.
        replace (c2 * m1 + i2) with (i2 + c2 * m1) in Hdiv by ring.
        rewrite <- Hdiv. reflexivity. }
      assert (Hleft2 : (i1 + c1 * m1) mod m1 = i1).
      { rewrite Nat.mod_add by (apply Nat.neq_0_lt_0; assumption). apply Nat.mod_small. assumption. }
      assert (Hright2 : (i2 + c2 * m1) mod m1 = i2).
      { rewrite Nat.mod_add by (apply Nat.neq_0_lt_0; assumption). apply Nat.mod_small. assumption. }
      rewrite Hleft2, Hright2 in Hmod. exact Hmod. }
    assert (Hc : c1 = c2).
    { rewrite Hj, Hi in Hnat.
      apply Nat.add_cancel_r in Hnat.
      apply Nat.mul_cancel_r in Hnat.
      - apply Nat.add_cancel_r in Hnat.
        apply Nat.mul_cancel_r in Hnat.
        + exact Hnat.
        + apply Nat.neq_0_lt_0. assumption.
      - apply Nat.neq_0_lt_0. assumption. }
    repeat split; apply fin_eq; simpl; auto.
  Qed.

  (* Per-cell functional equivalence for the doubly-joined batch slice. *)
  Lemma Flatten4d_cell_value :
    forall (b : fin batch) (c : fin channel) (i : fin m1) (j : fin m2),
      (join (join input|[b]))|[flatten_idx c i j] = (((input|[b])|[c])|[i])|[j].
  Proof.
    intros b c i j.
    rewrite (join_mkvSeq (join input|[b])).
    rewrite (join_mkvSeq input|[b]).
    unfold DE.idx, DE.mkvSeq, CNN_Defs.join, V.v_join.
    rewrite V.v_idx_mk_vec.
    destruct (idx_1d_to_2d (flatten_idx c i j)) as [ci j'] eqn:Hck'.
    rewrite V.v_idx_mk_vec.
    destruct (idx_1d_to_2d ci) as [c' i'] eqn:Hci'.
    assert (Hdecode : c = c' /\ i = i' /\ j = j').
    { assert (Hflat : flatten_idx c i j = flatten_idx c' i' j').
      { apply fin_eq'.
        pose proof (flatten_idx_1d_to_2d (flatten_idx c i j)) as Hflat0.
        simpl in Hflat0. rewrite Hck' in Hflat0. rewrite Hci' in Hflat0. simpl in Hflat0.
        exact Hflat0. }
      apply flatten_idx_injective in Hflat.
      exact Hflat. }
    destruct Hdecode as [Hc [Hi Hj]].
    symmetry in Hc. symmetry in Hi. symmetry in Hj.
    subst c'. subst i'. subst j'.
    reflexivity.
  Qed.

  Lemma Flatten4d_cell_independent_of_output :
    forall (output : acc (ary '{batch} (ary '{channel * m1 * m2} num))) (b : fin batch),
      exp_independent_of_acc (join (join input|[b])) output.
  Proof.
    intros output b.
    rewrite (join_mkvSeq (join input|[b])).
    rewrite (join_mkvSeq input|[b]).
    apply exp_independent_of_acc_mkvSeq. intro i.
    destruct (idx_1d_to_2d i) as [x y].
    repeat apply exp_independent_of_acc_idx.
    apply exp_independent_of_acc_mkvSeq. intro k.
    destruct (idx_1d_to_2d k) as [z w].
    repeat apply exp_independent_of_acc_idx.
    apply Hinput_out.
  Qed.

  (* The core per-batch equivalence: assigning the joined input to one batch
     slice of the output is the same as the three-level nested seqfor used in
     [Flatten4d_comm]. *)
  (* Indexing into the doubly-joined batch slice at the [flatten_idx] position
     recovers the original four-dimensional cell. *)


  Lemma Flatten4d_batch_sem :
    forall (output : acc (ary '{channel * m1 * m2} num)) (b : fin batch) (rho : PCG.env),
      eval (CG.assign (output, join (join input|[b]))) rho =
      eval (CG.seqfor (fun c : fin channel => CG.seqfor (fun i : fin m1 => CG.seqfor (fun j : fin m2 =>
        CG.assign (DE.idxAcc output (flatten_idx c i j), input|[b]|[c]|[i]|[j]))))) rho.
  Proof.
    intros output b rho.
    rewrite (join_mkvSeq (join input|[b])).
    rewrite (join_mkvSeq input|[b]).
    rewrite eval_mkvSeq.
    - rewrite !eval_seqfor.
      assert (Heq1 : PCG.seqfor (fun c : fin channel =>
        eval (CG.seqfor (fun i : fin m1 => CG.seqfor (fun j : fin m2 =>
          DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j])))) =
        PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
          let '(i, j) := idx_1d_to_2d k in
          eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j])))).
      { apply PCG.seqfor_extensionality. intro c.
        rewrite (seqfor_2d_CG Hm1 Hm2 (fun i j =>
          DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j])). reflexivity. }
      assert (Heq_m : channel * (m1 * m2) = (channel * m1) * m2) by (apply Nat.mul_assoc).
      assert (Heq2 : PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
        let '(i, j) := idx_1d_to_2d k in
        eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))) =
        PCG.seqfor (fun k : fin ((channel * m1) * m2) =>
          (fun k' : fin (channel * (m1 * m2)) =>
            let '(c, k0) := idx_1d_to_2d k' in
            let '(i, j) := idx_1d_to_2d k0 in
            eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))
          (fin_cast (eq_sym Heq_m) k))).
      { assert (Heq2' : PCG.seqfor (fun c : fin channel => PCG.seqfor (fun k : fin (m1 * m2) =>
          let '(i, j) := idx_1d_to_2d k in
          eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))) =
          PCG.seqfor (fun k' : fin (channel * (m1 * m2)) =>
            let '(c, k0) := idx_1d_to_2d k' in
            let '(i, j) := idx_1d_to_2d k0 in
            eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))).
        { apply seqfor_2d_body; [assumption | apply Nat.mul_pos_pos; assumption ]. }
        rewrite Heq2'. rewrite -> (@seqfor_body_cast (channel * (m1 * m2)) ((channel * m1) * m2) Heq_m
          (fun k' : fin (channel * (m1 * m2)) =>
            let '(c, k0) := idx_1d_to_2d k' in
            let '(i, j) := idx_1d_to_2d k0 in
            eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))). reflexivity. }
      rewrite Heq1. rewrite Heq2.
      assert (Heq3 : PCG.seqfor (fun i : fin (channel * m1 * m2) =>
        eval (DE.idxAcc output i |:=
          (let '(i0, j) := idx_1d_to_2d i in
            ((DE.mkvSeq (fun k : fin (channel * m1) =>
              let '(i1, j0) := idx_1d_to_2d k in ((input|[b])|[i1])|[j0]))
            |[i0])|[j]))) =
        PCG.seqfor (fun k : fin ((channel * m1) * m2) =>
          let '(c, k0) := idx_1d_to_2d (fin_cast (eq_sym Heq_m) k) in
          let '(i, j) := idx_1d_to_2d k0 in
          eval (DE.idxAcc output (flatten_idx c i j) |:= (((input|[b])|[c])|[i])|[j]))).
      { apply PCG.seqfor_extensionality. intro k.
        destruct (idx_1d_to_2d (fin_cast (eq_sym Heq_m) k)) as [c k_inner] eqn:Hck.
        destruct (idx_1d_to_2d k_inner) as [i j] eqn:Hki.
        assert (Hcast : fin_cast (Nat.mul_assoc channel m1 m2) (fin_cast (eq_sym Heq_m) k) = k).
        { apply fin_eq. simpl. repeat rewrite fin_cast_nat. reflexivity. }
        assert (Hidx : k = flatten_idx c i j).
        { pose proof (flatten_idx_1d_to_2d_cast (fin_cast (eq_sym Heq_m) k)) as Hflat0.
          simpl in Hflat0. rewrite Hck in Hflat0. rewrite Hki in Hflat0. simpl in Hflat0.
          rewrite <- Hcast. exact Hflat0. }
        rewrite Hidx.
        apply (f_equal (fun e => eval (CG.assign (DE.idxAcc output (flatten_idx c i j), e)))).
        unfold DE.idx, DE.mkvSeq, CNN_Defs.join, V.v_join in *.
        destruct (idx_1d_to_2d (flatten_idx c i j)) as [ci j0] eqn:Hck'.
        rewrite V.v_idx_mk_vec.
        destruct (idx_1d_to_2d ci) as [c' i'] eqn:Hci'.
        assert (Hdecode : c = c' /\ i = i' /\ j = j0).
        { assert (Hflat : flatten_idx c i j = flatten_idx c' i' j0).
          { apply fin_eq'.
            pose proof (flatten_idx_1d_to_2d (flatten_idx c i j)) as Hflat0.
            simpl in Hflat0. rewrite Hck' in Hflat0. rewrite Hci' in Hflat0. simpl in Hflat0.
            exact Hflat0. }
          apply flatten_idx_injective in Hflat.
          exact Hflat. }
        destruct Hdecode as [Hc [Hi Hj]].
        symmetry in Hc. symmetry in Hi. symmetry in Hj.
        subst c'. subst i'. subst j0.
        reflexivity. }
      rewrite Heq3. reflexivity.
    - (* Side condition for [eval_mkvSeq]: each cell is independent of output. *)
      intro k. destruct (idx_1d_to_2d k) as [ci j] eqn:?.
      repeat apply exp_independent_of_acc_idx.
      apply exp_independent_of_acc_mkvSeq. intro k0.
      destruct (idx_1d_to_2d k0) as [x y] eqn:?.
      repeat apply exp_independent_of_acc_idx.
      unfold exp_independent_of_acc. intros p Hp.
      assert (Hin : exp_independent_of_path input p).
      { apply Hinput_out with (output := V.mk_vec (fun _ : fin batch => output)).
        exists b. unfold PCG.idxAcc at 1. rewrite V.v_idx_mk_vec. exact Hp. }
      exact Hin.
  Qed.

  Theorem Flatten4d_sem :
    forall (output : acc (ary '{batch} (ary '{channel * m1 * m2} num))) (rho : PCG.env),
      tmp_disjoint_from_output2d batch (channel * m1 * m2) output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Flatten4d batch channel m1 m2 input)) rho =
      eval (@Flatten4d_comm batch channel m1 m2 input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Flatten4d, Flatten4d_comm.
    rewrite eval_mkvSeq; [ | intros b; apply Flatten4d_cell_independent_of_output ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [ exact Hundef | ].
    intros b eta HPeta. split.
    - rewrite eval_assign. rewrite !eval_seqfor.
      apply (Flatten4d_batch_sem (output|{b}) b eta).
    - rewrite eval_assign.
      apply PCG_assign_preserves_StructUndefined.
      + exact HPeta.
      + intros p Hp Hout. simpl in Hout. destruct Hout as [out Hout'].
        apply (Hdisj p b out Hp). exact Hout'.
  Qed.

End Flatten4d_Sem.

(* ------------------------------------------------------------------------ *)
(* Avgpool2d semantic equivalence                                            *)
(* (mirrors the [GlobalAvgPool4d_Sem] section; the k x k window is           *)
(* flattened into a single accumulator loop over [k * k])                    *)
(* ------------------------------------------------------------------------ *)

Section Avgpool2d_Sem.

  Variables (m1 m2 k : nat)
            (input : exp (ary '{m1} (ary '{m2} num)))
            (Hk : k > 0).

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{m1/k} (ary '{m2/k} num))),
    exp_independent_of_acc input output.

  Definition tmp_disjoint_from_output_avg2d
    (output : acc (ary '{m1/k} (ary '{m2/k} num))) : Prop :=
    forall p i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ i0} |{ i1}).

  (* Flat window cell, matching the loop body of [Avgpool2d_comm]. *)
  Definition AVG2d_flat_cell (i0 : fin (m1/k)) (i1 : fin (m2/k)) (kk : fin (k * k)) : exp num :=
    safe_idx_nat (safe_idx_nat input
      (fin2nat i0 * k + Nat.div (fin2nat kk) k))
      (fin2nat i1 * k + Nat.modulo (fin2nat kk) k).

  Lemma AVG2d_flat_index_bounds :
    forall (kk : fin (k * k)),
      Nat.div (fin2nat kk) k < k /\
      Nat.modulo (fin2nat kk) k < k.
  Proof.
    intro kk. destruct kk as [v Hv]. simpl.
    split.
    - apply Nat.div_lt_upper_bound; [lia |].
      exact Hv.
    - apply Nat.mod_upper_bound. lia.
  Qed.

  (* The nested functional window sum evaluates to the same real number as
     the flat sum accumulated by the imperative loop. *)
  Lemma AVG2d_nested_sum_flat :
    forall (i0 : fin (m1/k)) (i1 : fin (m2/k)) (rho : PCG.env),
      to_pcg_exp (sum (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
        input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))) rho =
      to_pcg_exp (sum (mkvSeq (AVG2d_flat_cell i0 i1))) rho.
  Proof.
    intros i0 i1 rho.
    set (idx_cell := fun (i j : nat) (Hi : i < k) (Hj : j < k) =>
      input|[nat2fin (fin_mul_add_lt_div m1 k i0 (nat2fin Hi))]|[nat2fin (fin_mul_add_lt_div m2 k i1 (nat2fin Hj))]).
    assert (Heq_lhs :
      to_pcg_exp (sum (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
        input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))) rho =
      sumR_nat_fin (fun i (Hi : i < k) => sumR_nat_fin (fun j (Hj : j < k) => to_pcg_exp (idx_cell i j Hi Hj) rho))).
    { rewrite to_pcg_exp_sum_nat by exact Hk.
      apply sumR_nat_fin_eq. intros i Hi.
      rewrite to_pcg_exp_sum_nat by exact Hk.
      apply sumR_nat_fin_eq. intros j Hj.
      reflexivity. }
    assert (Heq_rhs :
      to_pcg_exp (sum (mkvSeq (AVG2d_flat_cell i0 i1))) rho =
      sumR_nat_fin (fun kk (Hkk : kk < k * k) => to_pcg_exp (AVG2d_flat_cell i0 i1 (nat2fin Hkk)) rho)).
    { rewrite to_pcg_exp_sum_nat by nia. reflexivity. }
    rewrite Heq_lhs, Heq_rhs.
    pose (lemma := @sumR_nat_fin_nested_flat' k k Hk Hk
      (fun i j Hi Hj => to_pcg_exp (idx_cell i j Hi Hj) rho)
      (fun kk Hkk => to_pcg_exp (AVG2d_flat_cell i0 i1 (nat2fin Hkk)) rho)
      (fun kk Hkk => AVG2d_flat_index_bounds (nat2fin Hkk))).
    apply lemma; [ intros i j Hi1 Hi2 Hj1 Hj2;
         unfold idx_cell;
         repeat rewrite to_pcg_exp_idx;
         f_equal;
         apply fin_eq; rewrite !fin2nat_nat2fin; reflexivity
       | intros kk Hkk;
         unfold AVG2d_flat_cell, idx_cell;
         destruct (AVG2d_flat_index_bounds (nat2fin Hkk)) as [Hi Hj];
         unfold safe_idx_nat;
         destruct (Nat.ltb_spec0 (fin2nat i0 * k + fin2nat (nat2fin Hkk) / k) m1) as [Hi' | Hi'];
           [| exfalso; apply Hi'; exact (fin_mul_add_lt_div m1 k i0 (nat2fin Hi)) ];
         destruct (Nat.ltb_spec0 (fin2nat i1 * k + fin2nat (nat2fin Hkk) mod k) m2) as [Hj' | Hj'];
           [| exfalso; apply Hj'; exact (fin_mul_add_lt_div m2 k i1 (nat2fin Hj)) ];
         reflexivity ].
  Qed.

  Lemma Avgpool2d_cell_independent_of_output :
    forall (output : acc (ary '{m1/k} (ary '{m2/k} num))) (i0 : fin (m1/k)) (i1 : fin (m2/k)),
      exp_independent_of_acc
        (div_n (sum (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
          input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))
        output.
  Proof.
    intros output i0 i1.
    apply exp_independent_of_acc_div_n.
    apply exp_independent_of_acc_sum. intro j0.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    apply exp_independent_of_acc_sum. intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    repeat apply exp_independent_of_acc_idx. apply Hinput_out.
  Qed.

  Lemma Avgpool2d_cell_continuation_ok :
    forall (output : acc (ary '{m1/k} (ary '{m2/k} num))) (i0 : fin (m1/k)) (i1 : fin (m2/k)),
      tmp_disjoint_from_output_avg2d output ->
      loopacc_continuation_ok
        (fun r : exp num => output|{i0}|{i1} |:= div_n r (k * k))
        (sum (mkvSeq (AVG2d_flat_cell i0 i1))).
  Proof.
    intros output i0 i1 Hdisj.
    apply scalar_assign_continuation_ok.
    - (* output cell is disjoint from __tmp *)
      intros p Hp. apply Hdisj. exact Hp.
    - (* the summed expression is independent of __tmp *)
      apply exp_independent_of_acc_sum. intro kk.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold AVG2d_flat_cell.
      repeat apply safe_idx_nat_independent.
      exact Hinput_indep.
    - (* div_n of the sum is independent of __tmp *)
      apply exp_independent_of_acc_div_n.
      apply exp_independent_of_acc_sum. intro kk.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold AVG2d_flat_cell.
      repeat apply safe_idx_nat_independent.
      exact Hinput_indep.
    - (* div_n agrees when reading __tmp vs. using the functional result *)
      intros rho eta v Hv Heta.
      rewrite !to_pcg_exp_div_n.
      f_equal.
      rewrite to_pcg_exp_REvar_tmp'.
      rewrite value_at_update_same.
      symmetry. exact Hv.
  Qed.

  Theorem Avgpool2d_sem :
    forall (output : acc (ary '{m1/k} (ary '{m2/k} num))) (rho : PCG.env),
      tmp_disjoint_from_output_avg2d output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Avgpool2d m1 m2 k input)) rho =
      eval (@Avgpool2d_comm m1 m2 k input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Avgpool2d, Avgpool2d_comm.
    set (row := fun i0 : fin (m1/k) => mkvSeq (fun i1 : fin (m2/k) =>
      div_n (sum (mkvSeq (fun j0 : fin k =>
        sum (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))).
    assert (Hrow_indep : forall i0, exp_independent_of_acc (row i0) output).
    { intros i0. unfold row. apply exp_independent_of_acc_mkvSeq. intros i1.
      apply Avgpool2d_cell_independent_of_output. }
    rewrite eval_mkvSeq; [ | intros i0; apply Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros i0 eta HPeta. split.
    - (* Row-level equivalence. *)
      assert (Hcell_indep_i0 : forall i1,
        exp_independent_of_acc
          (div_n (sum (mkvSeq (fun j0 : fin k =>
            sum (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))) (k * k))
          (output |{ i0})).
      { intros i1. unfold exp_independent_of_acc. intros p Hp.
        apply (@Avgpool2d_cell_independent_of_output output i0 i1).
        simpl in Hp. destruct Hp as [i1' Hc']. simpl. exists i0. exists i1'. exact Hc'. }
      unfold row in |- *. rewrite eval_mkvSeq; [ | intros i1; apply Hcell_indep_i0 ].
      rewrite !eval_seqfor.
      apply seqfor_pointwise_inv with (P := P); [exact HPeta |].
      intros i1 eta' HPeta'. split.
      + set (e := mkvSeq (AVG2d_flat_cell i0 i1)).
        set (c' := fun r : exp num => (output|{i0}|{i1}) |:= div_n r (k * k)).
        assert (Hrhs : (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun kk : fin (k * k) =>
              vwt tmp |:= add (safe_idx_nat (safe_idx_nat input
                (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                (fin2nat i1 * k + Nat.modulo (fin2nat kk) k)) (vrd tmp))
            '; (output|{i0}|{i1}) |:= div_n (vrd tmp) (k * k)))
          = (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun kk : fin (k * k) =>
              vwt tmp |:= add e|[kk] (vrd tmp))
            '; (output|{i0}|{i1}) |:= div_n (vrd tmp) (k * k)))).
        { f_equal. apply functional_extensionality; intro tmp.
          assert (Hfor : seqfor (fun kk : fin (k * k) =>
                          vwt tmp |:= add (safe_idx_nat (safe_idx_nat input
                            (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                            (fin2nat i1 * k + Nat.modulo (fin2nat kk) k)) (vrd tmp))
                      = seqfor (fun kk : fin (k * k) =>
                          vwt tmp |:= add e|[kk] (vrd tmp))).
          { apply seqfor_extensionality; intro kk.
            assert (Heq : safe_idx_nat (safe_idx_nat input
                            (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                            (fin2nat i1 * k + Nat.modulo (fin2nat kk) k) = e|[kk]).
            { unfold e, AVG2d_flat_cell, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
            rewrite Heq. reflexivity. }
          rewrite Hfor. reflexivity. }
        rewrite Hrhs.
        rewrite eval_assign.
        rewrite <- (eval_assign_aux 1 num _ _ eta').
        change (eval_aux (c' (sum (mkvSeq (fun j0 : fin k =>
          sum (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))) 1 eta' =
          eval (@loopacc num (fun tmp : string =>
            let wtmp := vwt tmp in let v := vrd tmp in
            wtmp |:= zero '; seqfor (fun kk : fin (k * k) =>
              wtmp |:= add e|[kk] v)
            '; c' v)) eta').
        assert (Hsum_eq : to_pcg_exp (sum (mkvSeq (fun j0 : fin k =>
          sum (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))) eta' =
          to_pcg_exp (sum e) eta').
        { unfold e. apply AVG2d_nested_sum_flat. }
        assert (Heq_aux : eval_aux (c' (sum (mkvSeq (fun j0 : fin k =>
          sum (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))) 1 eta' =
          eval_aux (c' (sum e)) 1 eta').
        { unfold c'. rewrite !eval_assign_aux. f_equal.
          rewrite !to_pcg_exp_div_n. f_equal. exact Hsum_eq. }
        rewrite Heq_aux.
        apply eval_csum_equiv.
        * exact HPeta'.
        * unfold e. apply exp_independent_of_acc_mkvSeq. intro kk.
          unfold AVG2d_flat_cell. repeat apply safe_idx_nat_independent.
          exact Hinput_indep.
        * apply Avgpool2d_cell_continuation_ok. exact Hdisj.
      + rewrite eval_assign.
        apply assign_preserves_StructUndefined_tmp.
        * intros p Hp Hout. apply (Hdisj p i0 i1 Hp). exact Hout.
        * exact HPeta'.
    - rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta tmp_path).
      + unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros i1 rho'. apply PCG.assign_not_in_acc.
        intros Hc. apply (Hdisj tmp_path i0 i1 in_acc_tmp_scalar_acc). exact Hc.
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End Avgpool2d_Sem.

(* ------------------------------------------------------------------------ *)
(* Maxpool2d semantic equivalence                                            *)
(* (mirrors [Avgpool2d_Sem]; the accumulator loop computes the zero-based    *)
(* fold of [Rmax], matching [CD.max])                                        *)
(* ------------------------------------------------------------------------ *)

Section Maxpool2d_Sem.

  Variables (m1 m2 k : nat)
            (input : exp (ary '{m1} (ary '{m2} num)))
            (Hk : k > 0).

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{m1/k} (ary '{m2/k} num))),
    exp_independent_of_acc input output.

  Definition tmp_disjoint_from_output_maxp2d
    (output : acc (ary '{m1/k} (ary '{m2/k} num))) : Prop :=
    forall p i0 j0, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ i0} |{ j0}).

  (* Flat window cell, matching the loop body of [Maxpool2d_comm]. *)
  Definition MAXP2d_flat_cell (i0 : fin (m1/k)) (j0 : fin (m2/k)) (kk : fin (k * k)) : exp num :=
    safe_idx_nat (safe_idx_nat input
      (fin2nat i0 * k + Nat.div (fin2nat kk) k))
      (fin2nat j0 * k + Nat.modulo (fin2nat kk) k).

  Lemma MAXP2d_flat_index_bounds :
    forall (kk : fin (k * k)),
      Nat.div (fin2nat kk) k < k /\
      Nat.modulo (fin2nat kk) k < k.
  Proof.
    intro kk. destruct kk as [v Hv]. simpl.
    split.
    - apply Nat.div_lt_upper_bound; [lia |]. exact Hv.
    - apply Nat.mod_upper_bound. lia.
  Qed.

  (* The nested functional window max evaluates to the same real number as
     the flat max computed by the imperative loop. *)
  Lemma MAXP2d_nested_max_flat :
    forall (i0 : fin (m1/k)) (j0 : fin (m2/k)) (rho : PCG.env),
      to_pcg_exp (max (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
        input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)]))))) rho =
      to_pcg_exp (max (mkvSeq (MAXP2d_flat_cell i0 j0))) rho.
  Proof.
    intros i0 j0 rho.
    set (idx_cell := fun (i j : nat) (Hi : i < k) (Hj : j < k) =>
      input|[nat2fin (fin_mul_add_lt_div m1 k i0 (nat2fin Hi))]|[nat2fin (fin_mul_add_lt_div m2 k j0 (nat2fin Hj))]).
    assert (Heq_lhs :
      to_pcg_exp (max (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
        input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)]))))) rho =
      maxR_nat_fin (fun i (Hi : i < k) => maxR_nat_fin (fun j (Hj : j < k) => to_pcg_exp (idx_cell i j Hi Hj) rho))).
    { rewrite to_pcg_exp_max_nat by exact Hk.
      apply maxR_nat_fin_eq. intros i Hi.
      rewrite to_pcg_exp_max_nat by exact Hk.
      apply maxR_nat_fin_eq. intros j Hj.
      reflexivity. }
    assert (Heq_rhs :
      to_pcg_exp (max (mkvSeq (MAXP2d_flat_cell i0 j0))) rho =
      maxR_nat_fin (fun kk (Hkk : kk < k * k) => to_pcg_exp (MAXP2d_flat_cell i0 j0 (nat2fin Hkk)) rho)).
    { rewrite to_pcg_exp_max_nat by nia. reflexivity. }
    rewrite Heq_lhs, Heq_rhs.
    pose (lemma := @maxR_nat_fin_nested_flat' k k Hk Hk
      (fun i j Hi Hj => to_pcg_exp (idx_cell i j Hi Hj) rho)
      (fun kk Hkk => to_pcg_exp (MAXP2d_flat_cell i0 j0 (nat2fin Hkk)) rho)
      (fun kk Hkk => MAXP2d_flat_index_bounds (nat2fin Hkk))).
    apply lemma; [ intros i j Hi1 Hi2 Hj1 Hj2;
         unfold idx_cell;
         repeat rewrite to_pcg_exp_idx;
         f_equal;
         apply fin_eq; rewrite !fin2nat_nat2fin; reflexivity
       | intros kk Hkk;
         unfold MAXP2d_flat_cell, idx_cell;
         destruct (MAXP2d_flat_index_bounds (nat2fin Hkk)) as [Hi Hj];
         unfold safe_idx_nat;
         destruct (Nat.ltb_spec0 (fin2nat i0 * k + fin2nat (nat2fin Hkk) / k) m1) as [Hi' | Hi'];
           [| exfalso; apply Hi'; exact (fin_mul_add_lt_div m1 k i0 (nat2fin Hi)) ];
         destruct (Nat.ltb_spec0 (fin2nat j0 * k + fin2nat (nat2fin Hkk) mod k) m2) as [Hj' | Hj'];
           [| exfalso; apply Hj'; exact (fin_mul_add_lt_div m2 k j0 (nat2fin Hj)) ];
         reflexivity ].
  Qed.

  Lemma Maxpool2d_cell_independent_of_output :
    forall (output : acc (ary '{m1/k} (ary '{m2/k} num))) (i0 : fin (m1/k)) (j0 : fin (m2/k)),
      exp_independent_of_acc
        (max (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
          input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)])))))
        output.
  Proof.
    intros output i0 j0.
    apply exp_independent_of_acc_max. intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    apply exp_independent_of_acc_max. intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    repeat apply exp_independent_of_acc_idx. apply Hinput_out.
  Qed.

  Lemma Maxpool2d_cell_continuation_ok :
    forall (output : acc (ary '{m1/k} (ary '{m2/k} num))) (i0 : fin (m1/k)) (j0 : fin (m2/k)),
      tmp_disjoint_from_output_maxp2d output ->
      loopacc_continuation_ok
        (fun r : exp num => output|{i0}|{j0} |:= r)
        (max (mkvSeq (MAXP2d_flat_cell i0 j0))).
  Proof.
    intros output i0 j0 Hdisj.
    apply scalar_assign_continuation_ok.
    - (* output cell is disjoint from __tmp *)
      intros p Hp. apply Hdisj. exact Hp.
    - (* the max expression is independent of __tmp *)
      apply exp_independent_of_acc_max. intro kk.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold MAXP2d_flat_cell.
      repeat apply safe_idx_nat_independent.
      exact Hinput_indep.
    - (* the identity continuation preserves independence *)
      apply exp_independent_of_acc_max. intro kk.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold MAXP2d_flat_cell.
      repeat apply safe_idx_nat_independent.
      exact Hinput_indep.
    - (* the read of __tmp agrees with the functional result *)
      intros rho eta v Hv Heta. cbv beta.
      rewrite to_pcg_exp_REvar_tmp'.
      rewrite value_at_update_same.
      symmetry. exact Hv.
  Qed.

  Theorem Maxpool2d_sem :
    forall (output : acc (ary '{m1/k} (ary '{m2/k} num))) (rho : PCG.env),
      tmp_disjoint_from_output_maxp2d output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Maxpool2d m1 m2 k input)) rho =
      eval (@Maxpool2d_comm m1 m2 k input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Maxpool2d, Maxpool2d_comm.
    set (row := fun i0 : fin (m1/k) => mkvSeq (fun j0 : fin (m2/k) =>
      max (mkvSeq (fun i1 : fin k =>
        max (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)])))))).
    assert (Hrow_indep : forall i0, exp_independent_of_acc (row i0) output).
    { intros i0. unfold row. apply exp_independent_of_acc_mkvSeq. intros j0.
      apply Maxpool2d_cell_independent_of_output. }
    rewrite eval_mkvSeq; [ | intros i0; apply Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros i0 eta HPeta. split.
    - (* Row-level equivalence. *)
      assert (Hcell_indep_i0 : forall j0,
        exp_independent_of_acc
          (max (mkvSeq (fun i1 : fin k =>
            max (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)])))))
          (output |{ i0})).
      { intros j0. unfold exp_independent_of_acc. intros p Hp.
        apply (@Maxpool2d_cell_independent_of_output output i0 j0).
        simpl in Hp. destruct Hp as [j0' Hc']. simpl. exists i0. exists j0'. exact Hc'. }
      unfold row in |- *. rewrite eval_mkvSeq; [ | intros j0; apply Hcell_indep_i0 ].
      rewrite !eval_seqfor.
      apply seqfor_pointwise_inv with (P := P); [exact HPeta |].
      intros j0 eta' HPeta'. split.
      + set (e := mkvSeq (MAXP2d_flat_cell i0 j0)).
        set (c' := fun r : exp num => (output|{i0}|{j0}) |:= r).
        assert (Hrhs : (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun kk : fin (k * k) =>
              If (gtExp (safe_idx_nat (safe_idx_nat input
                (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                (fin2nat j0 * k + Nat.modulo (fin2nat kk) k)) (vrd tmp))
              (vwt tmp |:= safe_idx_nat (safe_idx_nat input
                (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                (fin2nat j0 * k + Nat.modulo (fin2nat kk) k),
               vwt tmp |:= (vrd tmp : exp num)))
            '; (output|{i0}|{j0}) |:= (vrd tmp : exp num)))
          = (@loopacc num (fun tmp : string =>
            (vwt tmp |:= zero) '; seqfor (fun kk : fin (k * k) =>
              If (gtExp e|[kk] (vrd tmp))
              (vwt tmp |:= e|[kk], vwt tmp |:= (vrd tmp : exp num)))
            '; (output|{i0}|{j0}) |:= (vrd tmp : exp num)))).
        { f_equal. apply functional_extensionality; intro tmp.
          assert (Hfor : seqfor (fun kk : fin (k * k) =>
                          If (gtExp (safe_idx_nat (safe_idx_nat input
                            (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                            (fin2nat j0 * k + Nat.modulo (fin2nat kk) k)) (vrd tmp))
                          (vwt tmp |:= safe_idx_nat (safe_idx_nat input
                            (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                            (fin2nat j0 * k + Nat.modulo (fin2nat kk) k),
                           vwt tmp |:= (vrd tmp : exp num)))
                      = seqfor (fun kk : fin (k * k) =>
                          If (gtExp e|[kk] (vrd tmp))
                          (vwt tmp |:= e|[kk], vwt tmp |:= (vrd tmp : exp num)))).
          { apply seqfor_extensionality; intro kk.
            assert (Heq : safe_idx_nat (safe_idx_nat input
                            (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                            (fin2nat j0 * k + Nat.modulo (fin2nat kk) k) = e|[kk]).
            { unfold e, MAXP2d_flat_cell, DE.idx, DE.mkvSeq. rewrite v_idx_mk_vec. reflexivity. }
            rewrite Heq. reflexivity. }
          rewrite Hfor. reflexivity. }
        rewrite Hrhs.
        rewrite eval_assign.
        rewrite <- (eval_assign_aux 1 num _ _ eta').
        change (eval_aux (c' (max (mkvSeq (fun i1 : fin k =>
          max (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)])))))) 1 eta' =
          eval (@loopacc num (fun tmp : string =>
            let wtmp := vwt tmp in let v := vrd tmp in
            wtmp |:= zero '; seqfor (fun kk : fin (k * k) =>
              If (gtExp e|[kk] v) (wtmp |:= e|[kk], wtmp |:= v))
            '; c' v)) eta').
        assert (Hmax_eq : to_pcg_exp (max (mkvSeq (fun i1 : fin k =>
          max (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)]))))) eta' =
          to_pcg_exp (max e) eta').
        { unfold e. apply MAXP2d_nested_max_flat. }
        assert (Heq_aux : eval_aux (c' (max (mkvSeq (fun i1 : fin k =>
          max (mkvSeq (fun j1 : fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)])))))) 1 eta' =
          eval_aux (c' (max e)) 1 eta').
        { unfold c'. rewrite !eval_assign_aux. f_equal. exact Hmax_eq. }
        rewrite Heq_aux.
        apply eval_cmax_equiv.
        * exact HPeta'.
        * unfold e. apply exp_independent_of_acc_mkvSeq. intro kk.
          unfold MAXP2d_flat_cell. repeat apply safe_idx_nat_independent.
          exact Hinput_indep.
        * apply Maxpool2d_cell_continuation_ok. exact Hdisj.
      + rewrite eval_assign.
        apply assign_preserves_StructUndefined_tmp.
        * intros p Hp Hout. apply (Hdisj p i0 j0 Hp). exact Hout.
        * exact HPeta'.
    - rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta tmp_path).
      + unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros j0 rho'. apply PCG.assign_not_in_acc.
        intros Hc. apply (Hdisj tmp_path i0 j0 in_acc_tmp_scalar_acc). exact Hc.
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End Maxpool2d_Sem.

(* ------------------------------------------------------------------------ *)
(* Maxpool3d semantic equivalence (reduced to [Maxpool2d_sem] per channel)   *)
(* ------------------------------------------------------------------------ *)

Section Maxpool3d_Sem.

  Variables (filernum m1 m2 k : nat)
            (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
            (Hf : filernum > 0) (Hk : k > 0).

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))),
    exp_independent_of_acc input output.

  Definition tmp_disjoint_from_output_maxp3d
    (output : acc (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))) : Prop :=
    forall p nu i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ nu} |{ i0} |{ i1}).

  Theorem Maxpool3d_sem :
    forall (output : acc (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num)))) (rho : PCG.env),
      tmp_disjoint_from_output_maxp3d output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Maxpool3d filernum m1 m2 k input)) rho =
      eval (@Maxpool3d_comm filernum m1 m2 k input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Maxpool3d, Maxpool3d_comm.
    assert (Hrow_indep : forall nu,
      exp_independent_of_acc
        (mkvSeq (fun i0 : fin (m1/k) => mkvSeq (fun i1 : fin (m2/k) =>
          max (mkvSeq (fun j0 : fin k => max (mkvSeq (fun j1 : fin k =>
            input|[nu]|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))))
        output).
    { intro nu. apply exp_independent_of_acc_mkvSeq. intro i0.
      apply exp_independent_of_acc_mkvSeq. intro i1.
      apply exp_independent_of_acc_max. intro j0.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_max. intro j1.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      repeat apply exp_independent_of_acc_idx. apply Hinput_out. }
    rewrite eval_mkvSeq; [ | exact Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros nu eta HPeta. split.
    - (* Row equivalence reduces to the 2D instance at [input|[nu]]. *)
      assert (Hin2d : forall out2d : acc (ary '{m1/k} (ary '{m2/k} num)),
        exp_independent_of_acc (input|[nu]) out2d).
      { intros out2d p Hp. apply exp_independent_path_idx with (i := nu).
        apply Hinput_out with (output := V.mk_vec (fun _ : fin filernum => out2d)).
        exists (nat2fin Hf). unfold PCG.idxAcc at 1. rewrite V.v_idx_mk_vec. exact Hp. }
      assert (Hdisj2d : @tmp_disjoint_from_output_maxp2d m1 m2 k (output|{nu})).
      { intros p i0 i1 Hp. exact (Hdisj p nu i0 i1 Hp). }
      change (eval (A(output|{nu}, @Maxpool2d m1 m2 k (input|[nu]))) eta =
              eval (@Maxpool2d_comm m1 m2 k (input|[nu]) (output|{nu})) eta).
      apply (@Maxpool2d_sem m1 m2 k (input|[nu]) Hk).
      + apply exp_independent_of_acc_idx. exact Hinput_indep.
      + exact Hin2d.
      + exact Hdisj2d.
      + exact HPeta.
    - rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta tmp_path).
      + apply PCG.assign_not_in_acc.
        intros Hc. simpl in Hc. destruct Hc as [i0 Hc]. simpl in Hc. destruct Hc as [i1 Hc].
        exact (Hdisj tmp_path nu i0 i1 in_acc_tmp_scalar_acc Hc).
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End Maxpool3d_Sem.

(* ------------------------------------------------------------------------ *)
(* Maxpool4d semantic equivalence (reduced to [Maxpool3d_sem] per batch)     *)
(* ------------------------------------------------------------------------ *)

Section Maxpool4d_Sem.

  Variables (batch filernum m1 m2 k : nat)
            (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
            (Hb : batch > 0) (Hf : filernum > 0) (Hk : k > 0).

  Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
  Hypothesis Hinput_out : forall (output : acc (ary '{batch} (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num))))),
    exp_independent_of_acc input output.

  Definition tmp_disjoint_from_output_maxp4d
    (output : acc (ary '{batch} (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num))))) : Prop :=
    forall p b nu i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ b} |{ nu} |{ i0} |{ i1}).

  Theorem Maxpool4d_sem :
    forall (output : acc (ary '{batch} (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num))))) (rho : PCG.env),
      tmp_disjoint_from_output_maxp4d output ->
      @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
      eval (A(output, @Maxpool4d batch filernum m1 m2 k input)) rho =
      eval (@Maxpool4d_comm batch filernum m1 m2 k input output) rho.
  Proof.
    intros output rho Hdisj Hundef.
    unfold A, Maxpool4d, Maxpool4d_comm.
    assert (Hrow_indep : forall b,
      exp_independent_of_acc
        (mkvSeq (fun nu : fin filernum => mkvSeq (fun i0 : fin (m1/k) => mkvSeq (fun i1 : fin (m2/k) =>
          max (mkvSeq (fun j0 : fin k => max (mkvSeq (fun j1 : fin k =>
            input|[b]|[nu]|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))))))
        output).
    { intro b. apply exp_independent_of_acc_mkvSeq. intro nu.
      apply exp_independent_of_acc_mkvSeq. intro i0.
      apply exp_independent_of_acc_mkvSeq. intro i1.
      apply exp_independent_of_acc_max. intro j0.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      apply exp_independent_of_acc_max. intro j1.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      repeat apply exp_independent_of_acc_idx. apply Hinput_out. }
    rewrite eval_mkvSeq; [ | exact Hrow_indep ].
    rewrite !eval_seqfor.
    set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
    apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
    intros b eta HPeta. split.
    - (* Row equivalence reduces to the 3D instance at [input|[b]]. *)
      assert (Hin3d : forall out3d : acc (ary '{filernum} (ary '{m1/k} (ary '{m2/k} num))),
        exp_independent_of_acc (input|[b]) out3d).
      { intros out3d p Hp. apply exp_independent_path_idx with (i := b).
        apply Hinput_out with (output := V.mk_vec (fun _ : fin batch => out3d)).
        exists (nat2fin Hb). unfold PCG.idxAcc at 1. rewrite V.v_idx_mk_vec. exact Hp. }
      assert (Hdisj3d : @tmp_disjoint_from_output_maxp3d filernum m1 m2 k (output|{b})).
      { intros p nu i0 i1 Hp. exact (Hdisj p b nu i0 i1 Hp). }
      change (eval (A(output|{b}, @Maxpool3d filernum m1 m2 k (input|[b]))) eta =
              eval (@Maxpool3d_comm filernum m1 m2 k (input|[b]) (output|{b})) eta).
      apply (@Maxpool3d_sem filernum m1 m2 k (input|[b]) Hf Hk).
      + apply exp_independent_of_acc_idx. exact Hinput_indep.
      + exact Hin3d.
      + exact Hdisj3d.
      + exact HPeta.
    - rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta tmp_path).
      + apply PCG.assign_not_in_acc.
        intros Hc. simpl in Hc. destruct Hc as [nu Hc]. simpl in Hc. destruct Hc as [i0 Hc]. simpl in Hc. destruct Hc as [i1 Hc].
        exact (Hdisj tmp_path b nu i0 i1 in_acc_tmp_scalar_acc Hc).
      + apply PCG.StructUndefined_num in HPeta. exact HPeta.
  Qed.

End Maxpool4d_Sem.


(* ------------------------------------------------------------------------ *)
(* Conv3d semantic equivalence                                               *)
(* ------------------------------------------------------------------------ *)

Section Conv3d_Sem.

Variables (m1 m2 n1 n2 channel filernum p s : nat)
          (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
          (bias : exp (ary '{filernum} num))
          (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
          (Hm1 : m1 > 0) (Hm2 : m2 > 0)
          (Hn1 : n1 > 0) (Hn2 : n2 > 0)
          (Hc : channel > 0) (Hf : filernum > 0)
          (Hs : s > 0)
          (Hout_h : ((m1 - n1 + 2 * p) / s + 1) > 0)
          (Hout_w : ((m2 - n2 + 2 * p) / s + 1) > 0).

Let out_h := ((m1 - n1 + 2 * p) / s + 1).
Let out_w := ((m2 - n2 + 2 * p) / s + 1).

Hypothesis Hinput_indep : exp_independent_of_acc input tmp_scalar_acc.
Hypothesis Hw_indep : exp_independent_of_acc w tmp_scalar_acc.
Hypothesis Hb_indep : exp_independent_of_acc bias tmp_scalar_acc.
Hypothesis Hinput_out : forall (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num)))),
  exp_independent_of_acc input output.
Hypothesis Hw_out : forall (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num)))),
  exp_independent_of_acc w output.
Hypothesis Hb_out : forall (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num)))),
  exp_independent_of_acc bias output.

Definition tmp_disjoint_from_output_conv3d
  (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num)))) : Prop :=
  forall pth fnum i0 j0, @PCG.in_acc num pth tmp_scalar_acc ->
    ~ @PCG.in_acc num pth (output |{ fnum} |{ i0} |{ j0}).

(* Auxiliary lemma for [Padding2d] independence. *)
Lemma exp_independent_of_acc_match_ltb :
  forall d' (a : acc d') (i n : nat) (e1 e2 : exp d'),
    (i < n -> exp_independent_of_acc e1 a) ->
    (~ i < n -> exp_independent_of_acc e2 a) ->
    exp_independent_of_acc (match Nat.ltb_spec0 i n with ReflectT _ _ => e1 | ReflectF _ _ => e2 end) a.
Proof.
  intros d' a i n e1 e2 H1 H2.
  destruct (Nat.ltb_spec0 i n); auto.
Qed.

Lemma exp_independent_path_match_ltb :
  forall N d (pth : DE.path) (i : fin N) (n : nat) (e1 e2 : exp d),
    (i < n -> exp_independent_of_path e1 pth) ->
    (~ i < n -> exp_independent_of_path e2 pth) ->
    exp_independent_of_path (match Nat.ltb_spec0 i n with ReflectT _ _ => e1 | ReflectF _ _ => e2 end) pth.
Proof.
  intros N d pth i n e1 e2 H1 H2.
  destruct (Nat.ltb_spec0 i n); auto.
Qed.

Lemma exp_independent_path_mkvSeq :
  forall n d (f : fin n -> exp d) (pth : DE.path),
    (forall i, exp_independent_of_path (f i) pth) ->
    exp_independent_of_path (DE.mkvSeq f) pth.
Proof.
  intros n d f pth H.
  unfold DE.mkvSeq. simpl.
  intros i. rewrite V.v_nth_mk_vec with (x0 := DE.exp_default d) (H := fin_proof i).
  rewrite nat2fin_fin2nat. apply H.
Qed.

Lemma exp_default_independent_path :
  forall d (pth : DE.path), exp_independent_of_path (DE.exp_default d) pth.
Proof.
  induction d; intros pth; simpl.
  - exact I.
  - apply exp_independent_path_mkvSeq. intro i. apply IHd.
Qed.

Lemma Padding2d_independent :
  forall (n1 n2 : nat) (d d' : data) (p0 : nat),
  forall (e : exp (ary '{n1} (ary '{n2} d))) (a : acc d'),
    exp_independent_of_acc e a ->
    exp_independent_of_acc (Padding2d p0 e) a.
Proof.
  intros n1' n2' d d' p0 e a Hin.
  unfold Padding2d, exp_independent_of_acc.
  intros q Hq.
  apply exp_independent_path_mkvSeq; intro i.
  apply exp_independent_path_mkvSeq; intro j.
  cbv zeta.
  destruct (Nat.ltb_spec0 i p0) as [Hi | Hi];
    [ apply exp_default_independent_path
    | destruct (Nat.ltb_spec0 i (p0 + n1')) as [Hi' | Hi'];
      [ destruct (Nat.ltb_spec0 j p0) as [Hj | Hj];
        [ apply exp_default_independent_path
        | destruct (Nat.ltb_spec0 j (p0 + n2')) as [Hj' | Hj'];
          [ repeat apply exp_independent_path_idx; apply Hin; exact Hq
          | apply exp_default_independent_path ] ]
      | apply exp_default_independent_path ] ].
Qed.

Lemma Padding3d_independent :
  forall (d' : data) (a : acc d'),
    exp_independent_of_acc input a ->
    exp_independent_of_acc (Padding3d p input) a.
Proof.
  intros d' a Hin. unfold Padding3d.
  apply exp_independent_of_acc_mkvSeq; intro c.
  apply Padding2d_independent.
  apply exp_independent_of_acc_idx. exact Hin.
Qed.

(* Functional and flat cell expressions. *)
Definition Conv3d_idx_cell (fnum : fin filernum) (i0 : fin out_h) (j0 : fin out_w)
  (c : fin channel) (i1 : fin n1) (j1 : fin n2) : exp num :=
  mul (safe_idx_nat (safe_idx_nat ((Padding3d p input)|[c]) (fin2nat i0 * s + fin2nat i1))
                   (fin2nat j0 * s + fin2nat j1))
      w|[fnum]|[c]|[i1]|[j1].

Definition Conv3d_flat_cell (fnum : fin filernum) (i0 : fin out_h) (j0 : fin out_w)
  (k : fin (channel * n1 * n2)) : exp num :=
  let c := Nat.div (fin2nat k) (n1 * n2) in
  let i1 := Nat.div (Nat.modulo (fin2nat k) (n1 * n2)) n2 in
  let j1 := Nat.modulo (fin2nat k) n2 in
  mul (safe_idx_nat (safe_idx_nat (Padding3d p input)|[nat2fin (conv3d_flat_c_bound k)]
                     (fin2nat i0 * s + i1))
                   (fin2nat j0 * s + j1))
      w|[fnum]|[nat2fin (conv3d_flat_c_bound k)]|[nat2fin (conv3d_flat_i1_bound k)]|[nat2fin (conv3d_flat_j1_bound k)].

Lemma Conv3d_flat_cell_unfold :
  forall fnum i0 j0 k,
    Conv3d_flat_cell fnum i0 j0 k =
    Conv3d_idx_cell fnum i0 j0 (nat2fin (conv3d_flat_c_bound k))
                              (nat2fin (conv3d_flat_i1_bound k))
                              (nat2fin (conv3d_flat_j1_bound k)).
Proof.
  intros. unfold Conv3d_flat_cell, Conv3d_idx_cell.
  repeat f_equal;
    apply fin_eq; simpl; rewrite ?fin2nat_nat2fin; reflexivity.
Qed.

(* Bounds helpers for the sum-flattening proof. *)
Lemma conv3d_inner_i1_bound' : forall (k2 : nat), k2 < n1 * n2 -> Nat.div k2 n2 < n1.
Proof.
  intros k2 Hk2. apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm. exact Hk2.
Qed.

Lemma conv3d_inner_j1_bound' : forall (k2 : nat), k2 < n1 * n2 -> Nat.modulo k2 n2 < n2.
Proof.
  intros k2 Hk2. apply Nat.mod_upper_bound. lia.
Qed.

Lemma conv3d_outer_c_bound' : forall (k : nat), k < channel * n1 * n2 -> Nat.div k (n1 * n2) < channel.
Proof.
  intros k Hk. apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm, Nat.mul_assoc. exact Hk.
Qed.

Lemma conv3d_outer_k2_bound' : forall (k : nat), k < channel * n1 * n2 -> Nat.modulo k (n1 * n2) < n1 * n2.
Proof.
  intros k Hk. apply Nat.mod_upper_bound. lia.
Qed.

Lemma conv3d_outer_c_bound'' : forall (k : nat), k < channel * (n1 * n2) -> Nat.div k (n1 * n2) < channel.
Proof.
  intros k Hk. apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm. exact Hk.
Qed.

Lemma conv3d_outer_k2_bound'' : forall (k : nat), k < channel * (n1 * n2) -> Nat.modulo k (n1 * n2) < n1 * n2.
Proof.
  intros k Hk. apply Nat.mod_upper_bound. lia.
Qed.

Lemma mod_mul_r_mod_self : forall a b c, b > 0 -> c > 0 ->
  (a mod (b * c)) mod c = a mod c.
Proof.
  intros a b c Hb Hc'.
  rewrite (Nat.mul_comm b c).
  rewrite Nat.Div0.mod_mul_r with (b := c) (c := b).
  rewrite Nat.mul_comm.
  rewrite (Nat.Div0.mod_add (a mod c) ((a / c) mod b) c).
  rewrite Nat.Div0.mod_mod.
  reflexivity.
  all: lia.
Qed.

Lemma Conv3d_sum_flatten :
  forall (fnum : fin filernum) (i0 : fin out_h) (j0 : fin out_w) (rho : PCG.env),
    to_pcg_exp (sum (mkvSeq (fun c : fin channel => sum (mkvSeq (fun i1 : fin n1 => sum (mkvSeq (fun j1 : fin n2 =>
      Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) rho =
    to_pcg_exp (sum (mkvSeq (Conv3d_flat_cell fnum i0 j0))) rho.
Proof.
  intros fnum i0 j0 rho.
  set (idx_cell := fun (c : nat) (Hc : c < channel) (i1 : nat) (Hi1 : i1 < n1) (j1 : nat) (Hj1 : j1 < n2) =>
    to_pcg_exp (Conv3d_idx_cell fnum i0 j0 (nat2fin Hc) (nat2fin Hi1) (nat2fin Hj1)) rho).
  set (g_inner := fun (c : nat) (Hc : c < channel) (k2 : nat) (Hk2 : k2 < n1 * n2) =>
    to_pcg_exp (Conv3d_idx_cell fnum i0 j0 (nat2fin Hc)
      (nat2fin (conv3d_inner_i1_bound' Hk2))
      (nat2fin (conv3d_inner_j1_bound' Hk2))) rho).
  set (g_outer := fun (k : nat) (Hk : k < channel * n1 * n2) =>
    to_pcg_exp (Conv3d_flat_cell fnum i0 j0 (nat2fin Hk)) rho).
  assert (Heq_lhs : to_pcg_exp (sum (mkvSeq (fun c : fin channel => sum (mkvSeq (fun i1 : fin n1 => sum (mkvSeq (fun j1 : fin n2 =>
      Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) rho =
    sumR_nat_fin (fun c Hcc => sumR_nat_fin (fun i1 Hi1 => sumR_nat_fin (fun j1 Hj1 =>
      idx_cell c Hcc i1 Hi1 j1 Hj1)))).
  { rewrite to_pcg_exp_sum_nat by nia.
    apply sumR_nat_fin_eq; intros c Hcc.
    rewrite to_pcg_exp_sum_nat by nia.
    apply sumR_nat_fin_eq; intros i1 Hi1.
    rewrite to_pcg_exp_sum_nat by nia.
    apply sumR_nat_fin_eq; intros j1 Hj1.
    reflexivity. }
  assert (Heq_rhs : to_pcg_exp (sum (mkvSeq (Conv3d_flat_cell fnum i0 j0))) rho =
    sumR_nat_fin (fun k Hk => g_outer k Hk)).
  { rewrite to_pcg_exp_sum_nat by nia.
    apply sumR_nat_fin_eq; intros k Hk.
    reflexivity. }
  rewrite Heq_lhs, Heq_rhs.
  assert (Hinner :
    sumR_nat_fin (fun c Hcc => sumR_nat_fin (fun i1 Hi1 => sumR_nat_fin (fun j1 Hj1 =>
      idx_cell c Hcc i1 Hi1 j1 Hj1))) =
    sumR_nat_fin (fun c Hcc => sumR_nat_fin (fun k2 Hk2 => g_inner c Hcc k2 Hk2))).
  { apply sumR_nat_fin_eq; intros c Hcc.
    pose (lemma := @sumR_nat_fin_nested_flat' n1 n2 Hn1 Hn2
      (fun i1 j1 Hi1 Hj1 => idx_cell c Hcc i1 Hi1 j1 Hj1)
      (fun k2 Hk2 => g_inner c Hcc k2 Hk2)
      (fun k2 Hk2 => conj (conv3d_inner_i1_bound' Hk2) (conv3d_inner_j1_bound' Hk2))).
    apply lemma;
      [ intros i1 j1 Hi1 Hi1' Hj1 Hj1'; unfold idx_cell;
        repeat rewrite to_pcg_exp_idx; f_equal; apply fin_eq;
        rewrite !fin2nat_nat2fin; reflexivity
      | intros k2 Hk2; unfold g_inner, idx_cell; reflexivity ]. }
  assert (Houter :
    sumR_nat_fin (fun c Hc => sumR_nat_fin (fun k2 Hk2 => g_inner c Hc k2 Hk2)) =
    sumR_nat_fin (fun k Hk => g_outer k Hk)).
  { assert (Houter' :
      sumR_nat_fin (fun c Hc => sumR_nat_fin (fun k2 Hk2 => g_inner c Hc k2 Hk2)) =
      sumR_nat_fin (fun k Hk => g_outer k (eq_rect _ (fun x => k < x) Hk _ (Nat.mul_assoc channel n1 n2)))).
    { refine (@sumR_nat_fin_nested_flat' channel (n1 * n2) Hc (Nat.mul_pos_pos n1 n2 Hn1 Hn2)
        (fun c k2 Hc Hk2 =>
           to_pcg_exp (Conv3d_idx_cell fnum i0 j0 (nat2fin Hc)
             (nat2fin (conv3d_inner_i1_bound' Hk2))
             (nat2fin (conv3d_inner_j1_bound' Hk2))) rho)
        (fun k Hk =>
           to_pcg_exp (Conv3d_flat_cell fnum i0 j0
             (nat2fin (eq_rect _ (fun x => k < x) Hk _ (Nat.mul_assoc channel n1 n2)))) rho)
        (fun k Hk => conj (conv3d_outer_c_bound'' Hk) (conv3d_outer_k2_bound'' Hk)) _ _).
      - intros c k2 Hc1 Hc2 Hk1 Hk2.
        repeat rewrite to_pcg_exp_idx; f_equal; apply fin_eq;
        rewrite !fin2nat_nat2fin; reflexivity.
      - intros k Hk.
        rewrite Conv3d_flat_cell_unfold.
        assert (Hc_eq : nat2fin (conv3d_flat_c_bound
          (nat2fin (eq_rect _ (fun x => k < x) Hk _ (Nat.mul_assoc channel n1 n2)))) =
          nat2fin (conv3d_outer_c_bound'' Hk)).
        { apply fin_eq'; cbn; reflexivity. }
        assert (Hi1_eq : nat2fin (conv3d_flat_i1_bound
          (nat2fin (eq_rect _ (fun x => k < x) Hk _ (Nat.mul_assoc channel n1 n2)))) =
          nat2fin (conv3d_inner_i1_bound' (conv3d_outer_k2_bound'' Hk))).
        { apply fin_eq'; cbn; reflexivity. }
        assert (Hj1_eq : nat2fin (conv3d_flat_j1_bound
          (nat2fin (eq_rect _ (fun x => k < x) Hk _ (Nat.mul_assoc channel n1 n2)))) =
          nat2fin (conv3d_inner_j1_bound' (conv3d_outer_k2_bound'' Hk))).
        { apply fin_eq'; cbn; rewrite mod_mul_r_mod_self by lia; reflexivity. }
        rewrite Hc_eq, Hi1_eq, Hj1_eq.
        reflexivity. }
    rewrite Houter'.
    apply sumR_nat_fin_proof_irrelevance_bound.
    exact (Nat.mul_assoc channel n1 n2).
    intros k H1 H2. unfold g_outer.
    repeat f_equal; apply proof_irrelevance. }
  rewrite Hinner, Houter. reflexivity.
Qed.

Lemma Conv3d_cell_independent_of_output :
  forall (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num))))
         (fnum : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
    exp_independent_of_acc
      (add (sum (mkvSeq (fun c : fin channel => sum (mkvSeq (fun i1 : fin n1 => sum (mkvSeq (fun j1 : fin n2 =>
        Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) bias|[fnum])
      output.
Proof.
  intros output fnum i0 j0.
  apply exp_independent_of_acc_add.
  - apply exp_independent_of_acc_sum; intro c.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    apply exp_independent_of_acc_sum; intro i1.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    apply exp_independent_of_acc_sum; intro j1.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    unfold Conv3d_idx_cell.
    apply exp_independent_of_acc_mul.
    + repeat apply safe_idx_nat_independent.
      apply exp_independent_of_acc_idx.
      apply Padding3d_independent.
      apply Hinput_out.
    + repeat apply exp_independent_of_acc_idx.
      apply Hw_out.
  - apply exp_independent_of_acc_idx.
    apply Hb_out.
Qed.

Lemma Conv3d_cell_independent_of_tmp :
  forall (fnum : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
    exp_independent_of_acc
      (sum (mkvSeq (fun c : fin channel => sum (mkvSeq (fun i1 : fin n1 => sum (mkvSeq (fun j1 : fin n2 =>
        Conv3d_idx_cell fnum i0 j0 c i1 j1)))))))
      tmp_scalar_acc.
Proof.
  intros fnum i0 j0.
  apply exp_independent_of_acc_sum; intro c.
  unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
  apply exp_independent_of_acc_sum; intro i1.
  unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
  apply exp_independent_of_acc_sum; intro j1.
  unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
  unfold Conv3d_idx_cell.
  apply exp_independent_of_acc_mul.
  - repeat apply safe_idx_nat_independent.
    apply exp_independent_of_acc_idx.
    apply Padding3d_independent.
    exact Hinput_indep.
  - repeat apply exp_independent_of_acc_idx.
    exact Hw_indep.
Qed.

Lemma Conv3d_cell_continuation_ok :
  forall (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num))))
         (fnum : fin filernum) (i0 : fin out_h) (j0 : fin out_w),
    tmp_disjoint_from_output_conv3d output ->
    loopacc_continuation_ok
      (fun r : exp num => output|{fnum}|{i0}|{j0} |:= add r bias|[fnum])
      (sum (mkvSeq (Conv3d_flat_cell fnum i0 j0))).
Proof.
  intros output fnum i0 j0 Hdisj.
  apply scalar_assign_continuation_ok.
  - intros p0 Hp Hout. apply (Hdisj p0 fnum i0 j0 Hp). exact Hout.
  - apply exp_independent_of_acc_sum; intro k.
    unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
    unfold Conv3d_flat_cell.
    apply exp_independent_of_acc_mul.
    + repeat apply safe_idx_nat_independent.
      apply exp_independent_of_acc_idx.
      apply Padding3d_independent.
      exact Hinput_indep.
    + repeat apply exp_independent_of_acc_idx.
      exact Hw_indep.
  - apply exp_independent_of_acc_add.
    + apply exp_independent_of_acc_sum; intro k.
      unfold DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec.
      unfold Conv3d_flat_cell.
      apply exp_independent_of_acc_mul.
      * repeat apply safe_idx_nat_independent.
        apply exp_independent_of_acc_idx.
        apply Padding3d_independent.
        exact Hinput_indep.
      * repeat apply exp_independent_of_acc_idx.
        exact Hw_indep.
    + apply exp_independent_of_acc_idx.
      exact Hb_indep.
  - intros rho eta v Hv Heta.
    rewrite !to_pcg_exp_add; f_equal.
    + unfold CG.vrd. simpl. rewrite to_pcg_exp_REvar.
      rewrite PCG.update_eq by reflexivity.
      symmetry. exact Hv.
    + apply exp_independent_of_acc_eval with (a := tmp_scalar_acc).
      * apply exp_independent_of_acc_idx.
        exact Hb_indep.
      * intros q Hq. rewrite PCG.update_neq by (intro Hc0; apply Hq; simpl; auto).
        apply Heta. intro Hc0. apply Hq. simpl. auto.
Qed.

Theorem Conv3d_sem :
  forall (output : acc (ary '{filernum} (ary '{out_h} (ary '{out_w} num)))) (rho : PCG.env),
    tmp_disjoint_from_output_conv3d output ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Conv3d m1 m2 n1 n2 channel filernum p s bias w input)) rho =
    eval (@Conv3d_comm m1 m2 n1 n2 channel filernum p s bias w input output) rho.
Proof.
  intros output rho Hdisj Hundef.
  unfold A, Conv3d, let_binding, Conv3d_comm.
  set (row := fun fnum : fin filernum => mkvSeq (fun i0 : fin out_h => mkvSeq (fun j0 : fin out_w =>
    add (sum (mkvSeq (fun c : fin channel => sum (mkvSeq (fun i1 : fin n1 => sum (mkvSeq (fun j1 : fin n2 =>
      Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) bias|[fnum]))).
  assert (Hrow_indep : forall fnum, exp_independent_of_acc (row fnum) output).
  { intros fnum. unfold row. apply exp_independent_of_acc_mkvSeq; intro i0.
    apply exp_independent_of_acc_mkvSeq; intro j0.
    apply Conv3d_cell_independent_of_output. }
  rewrite eval_mkvSeq; [ | intros fnum; apply Hrow_indep ].
  rewrite !eval_seqfor.
  set (P := fun eta => @PCG.StructUndefined num (PCG.acc' tmp_path) eta).
  apply seqfor_pointwise_inv with (P := P); [exact Hundef |].
  intros fnum eta HPeta. split.
  - assert (Hcell_indep_fnum : forall i0 j0,
      exp_independent_of_acc
        (add (sum (mkvSeq (fun c => sum (mkvSeq (fun i1 => sum (mkvSeq (fun j1 =>
          Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) bias|[fnum])
        (output |{ fnum})).
    { intros i0 j0. intros p0 Hp.
      apply (@Conv3d_cell_independent_of_output output fnum i0 j0).
      apply in_acc_ary_inv with (i := fnum). exact Hp. }
    unfold row in |- *. rewrite eval_mkvSeq; [ | intros i0;
      apply exp_independent_of_acc_mkvSeq; intros j0; apply Hcell_indep_fnum ].
    rewrite !eval_seqfor.
    apply seqfor_pointwise_inv with (P := P); [exact HPeta |].
    intros i0 eta' HPeta'. split.
    + assert (Hcell_indep_i0 : forall j0,
        exp_independent_of_acc
          (add (sum (mkvSeq (fun c => sum (mkvSeq (fun i1 => sum (mkvSeq (fun j1 =>
            Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) bias|[fnum])
          (output |{ fnum} |{ i0})).
      { intros j0. intros p0 Hp.
        apply (@Conv3d_cell_independent_of_output output fnum i0 j0).
        apply in_acc_ary_inv with (i := fnum).
        apply in_acc_ary_inv with (i := i0).
        exact Hp. }
      unfold row in |- *. rewrite eval_mkvSeq; [ | intros j0; apply Hcell_indep_i0 ].
      rewrite !eval_seqfor.
      apply seqfor_pointwise_inv with (P := P); [exact HPeta' |].
      intros j0 eta'' HPeta''. split.
      * set (e := mkvSeq (Conv3d_flat_cell fnum i0 j0)).
        set (c := fun r : exp num => (output|{fnum}|{i0}|{j0}) |:= add r bias|[fnum]).
        rewrite (reduce_loopacc_named_sem _ _ (fun tmp : string =>
          let wtmp := vwt tmp in let v := vrd tmp in
          wtmp |:= zero '; seqfor (fun k : fin (channel * n1 * n2) =>
            wtmp |:= add e|[k] v) '; c v) eta'').
        2: { intros tmp. apply functional_extensionality. intro rho1.
             cbn beta zeta iota. repeat f_equal.
             all: try reflexivity.
             all: try (apply functional_extensionality; intro k; repeat f_equal;
               assert (Heq : mul (safe_idx_nat (safe_idx_nat (Padding3d p input)|[nat2fin (conv3d_flat_c_bound k)]
                                                 (fin2nat i0 * s + Nat.div (Nat.modulo (fin2nat k) (n1 * n2)) n2))
                                 (fin2nat j0 * s + Nat.modulo (fin2nat k) n2))
                            w|[fnum]|[nat2fin (conv3d_flat_c_bound k)]|[nat2fin (conv3d_flat_i1_bound k)]|[nat2fin (conv3d_flat_j1_bound k)] = e|[k])
               by (unfold e, DE.idx, DE.mkvSeq; rewrite v_idx_mk_vec; reflexivity);
               rewrite Heq; reflexivity). }
        rewrite eval_assign.
        rewrite <- (eval_assign_aux 1 num _ _ eta'').
        change (eval_aux (c (sum (mkvSeq (fun c : fin channel => sum (mkvSeq (fun i1 : fin n1 => sum (mkvSeq (fun j1 : fin n2 =>
          Conv3d_idx_cell fnum i0 j0 c i1 j1)))))))) 1 eta'' =
          eval (@loopacc num (fun tmp : string =>
            let wtmp := vwt tmp in let v := vrd tmp in
            wtmp |:= zero '; seqfor (fun k : fin (channel * n1 * n2) =>
              wtmp |:= add e|[k] v) '; c v)) eta'').
        assert (Hsum_eq : to_pcg_exp (sum (mkvSeq (fun c => sum (mkvSeq (fun i1 => sum (mkvSeq (fun j1 =>
          Conv3d_idx_cell fnum i0 j0 c i1 j1))))))) eta'' =
          to_pcg_exp (sum e) eta'').
        { unfold e. apply Conv3d_sum_flatten. }
        assert (Heq_aux : eval_aux (c (sum (mkvSeq (fun c => sum (mkvSeq (fun i1 => sum (mkvSeq (fun j1 =>
          Conv3d_idx_cell fnum i0 j0 c i1 j1)))))))) 1 eta'' =
          eval_aux (c (sum e)) 1 eta'').
        { unfold c. rewrite !eval_assign_aux. f_equal.
          rewrite !to_pcg_exp_add. f_equal.
          { exact Hsum_eq. } }
        rewrite Heq_aux.
        apply eval_csum_equiv.
        { exact HPeta''. }
        { unfold e. apply exp_independent_of_acc_mkvSeq; intro k.
          unfold Conv3d_flat_cell.
          apply exp_independent_of_acc_mul.
          { repeat apply safe_idx_nat_independent.
            apply exp_independent_of_acc_idx.
            apply Padding3d_independent.
            exact Hinput_indep. }
          { repeat apply exp_independent_of_acc_idx.
            exact Hw_indep. } }
        { apply Conv3d_cell_continuation_ok. exact Hdisj. }
      * rewrite eval_assign.
        apply assign_preserves_StructUndefined_tmp.
        -- intros pth Hp Hout. apply (Hdisj pth fnum i0 j0 Hp). exact Hout.
        -- exact HPeta''.
    + rewrite eval_assign.
      apply PCG.StructUndefined_num.
      apply eq_trans with (y := eta' tmp_path).
      * unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
        apply PCG.seqfor_pointwise. intros j0 rho'. apply PCG.assign_not_in_acc.
        intros Hin. apply (Hdisj tmp_path fnum i0 j0 in_acc_tmp_scalar_acc). exact Hin.
      * apply PCG.StructUndefined_num in HPeta'. exact HPeta'.
  - rewrite eval_assign.
    apply PCG.StructUndefined_num.
    apply eq_trans with (y := eta tmp_path).
    + unfold row in |- *. rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros i0 rho'.
      rewrite to_pcg_exp_mkvSeq. rewrite assign_mkvSeq.
      apply PCG.seqfor_pointwise. intros j0 rho''. apply PCG.assign_not_in_acc.
      intros Hin. apply (Hdisj tmp_path fnum i0 j0 in_acc_tmp_scalar_acc). exact Hin.
    + apply PCG.StructUndefined_num in HPeta. exact HPeta.
Qed.

End Conv3d_Sem.

(* Replacement for the former axiom [CNN_Examples_Base.Flatten4d_equiv].
   The syntactic Leibniz equality is restated as semantic equality under
   [eval], with the side conditions of [Flatten4d_sem] as explicit premises.
   It is stated here rather than in [CNN_Examples_Base.v] because this file
   imports [CNN_Examples_Base.v], not vice versa. *)
Lemma Flatten4d_equiv :
  forall (batch channel m1 m2 : nat)
         (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
         (output : acc (ary '{batch} (ary '{channel * m1 * m2} num)))
         (rho : PCG.env),
    channel > 0 -> m1 > 0 -> m2 > 0 ->
    (forall out : acc (ary '{batch} (ary '{channel * m1 * m2} num)),
      exp_independent_of_acc input out) ->
    tmp_disjoint_from_output2d batch (channel * m1 * m2) output ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Flatten4d batch channel m1 m2 input)) rho =
    eval (@Flatten4d_comm batch channel m1 m2 input output) rho.
Proof.
  intros batch channel m1 m2 input output rho Hc Hm1 Hm2 Hin Hdisj Hundef.
  apply Flatten4d_sem; assumption.
Qed.

(* Replacement for the former axiom
   [CNN_Examples_MiniAlexNet.Flatten4d_equiv_1_1_2_2]: the [Flatten4d_sem]
   instance at batch=1, channel=1, m1=2, m2=2. *)
Lemma Flatten4d_equiv_1_1_2_2 :
  forall (input : exp (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))))
         (output : acc (ary '{1} (ary '{4} num)))
         (rho : PCG.env),
    (forall out : acc (ary '{1} (ary '{4} num)),
      exp_independent_of_acc input out) ->
    tmp_disjoint_from_output2d 1 4 output ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Flatten4d 1 1 2 2 input)) rho =
    eval (@Flatten4d_comm 1 1 2 2 input output) rho.
Proof.
  intros input output rho Hin Hdisj Hundef.
  apply (@Flatten4d_sem 1 1 2 2 input); try assumption; lia.
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.Softmax1d_equiv_3]:
   the [Softmax1d_sem] instance at n=3. *)
Lemma Softmax1d_equiv_3 :
  forall (input : exp (ary '{3} num)) (output : acc (ary '{3} num))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{3} num), exp_independent_of_acc input out) ->
    (forall p j, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ j})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Softmax1d 3 input)) rho =
    eval (@Softmax1d_comm 3 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  apply Softmax1d_sem; try assumption; lia.
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.Linear1d_equiv_3_2]:
   the [Linear1d_sem] instance at m=3, outnum=2. *)
Lemma Linear1d_equiv_3_2 :
  forall (w : exp (ary '{2} (ary '{3} num))) (b : exp (ary '{2} num))
         (input : exp (ary '{3} num)) (output : acc (ary '{2} num))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    exp_independent_of_acc w tmp_scalar_acc ->
    exp_independent_of_acc b tmp_scalar_acc ->
    (forall out : acc (ary '{2} num), exp_independent_of_acc input out) ->
    (forall out : acc (ary '{2} num), exp_independent_of_acc w out) ->
    (forall out : acc (ary '{2} num), exp_independent_of_acc b out) ->
    tmp_disjoint_from_output 2 output ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Linear 3 2 w b input)) rho =
    eval (@Linear1d_comm 3 2 w b input output) rho.
Proof.
  intros w b input output rho Hi Hw Hb Hio Hwo Hbo Hdisj Hundef.
  apply Linear1d_sem; try assumption; lia.
Qed.

(* ------------------------------------------------------------------------ *)
(* Flatten3d semantic equivalence (derived from [Flatten4d_batch_sem] at     *)
(* batch = 1 with a constant batch row)                                      *)
(* ------------------------------------------------------------------------ *)

Lemma Flatten3d_sem :
  forall (channel m1 m2 : nat)
         (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
         (output : acc (ary '{channel * m1 * m2} num))
         (rho : PCG.env),
    channel > 0 -> m1 > 0 -> m2 > 0 ->
    (forall out : acc (ary '{channel * m1 * m2} num), exp_independent_of_acc input out) ->
    eval (A(output, @Flatten3d channel m1 m2 input)) rho =
    eval (@Flatten3d_comm channel m1 m2 input output) rho.
Proof.
  intros channel m1 m2 input output rho Hc Hm1 Hm2 Hinput_out.
  unfold A, Flatten3d, Flatten3d_comm.
  pose (input4d := DE.mkvSeq (fun _ : fin 1 => input)).
  assert (Hin4d : forall out4d : acc (ary '{1} (ary '{channel * m1 * m2} num)),
    exp_independent_of_acc input4d out4d).
  { intros out4d. unfold input4d. apply exp_independent_of_acc_mkvSeq. intro b.
    intros p Hp. simpl in Hp. destruct Hp as [b' Hb'].
    apply (Hinput_out (out4d|{b'})). exact Hb'. }
  pose (b0 := @nat2fin 1 0 (Nat.lt_0_succ 0)).
  assert (Hkey := @Flatten4d_batch_sem 1 channel m1 m2 input4d
    Hc Hm1 Hm2 Hin4d output b0 rho).
  unfold input4d in Hkey.
  unfold DE.idx, DE.mkvSeq in Hkey.
  rewrite V.v_idx_mk_vec in Hkey.
  cbv beta in Hkey.
  exact Hkey.
Qed.

(* ------------------------------------------------------------------------ *)
(* Replacements for the pool/flatten axioms: semantic instances              *)
(* ------------------------------------------------------------------------ *)

(* Replacement for the former axiom [CNN_Examples_Base.MaxPool2d_equiv_concrete_4x4]:
   the [Maxpool2d_sem] instance at m1=4, m2=4, k=2.  The imperative side is the
   generic loopacc-based [Maxpool2d_comm] from [CNN_Examples_Base_Ops.v]; see
   the comment at the former axiom site in [CNN_Examples_Base.v] for why the
   concrete [new]-based [maxpool2d_comm_4x4] is not used. *)
Lemma MaxPool2d_equiv_concrete_4x4 :
  forall (input : exp (ary '{4} (ary '{4} num)))
         (output : acc (ary '{2} (ary '{2} num)))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{2} (ary '{2} num)), exp_independent_of_acc input out) ->
    (forall p i0 j0, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ i0} |{ j0})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Maxpool2d 4 4 2 input)) rho =
    eval (@Maxpool2d_comm 4 4 2 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  exact (@Maxpool2d_sem 4 4 2 input (Nat.lt_0_succ 1) Hin Hout output rho Hdisj Hundef).
Qed.

(* Replacement for the former axiom [CNN_Examples_Base.AvgPool2d_equiv_concrete_4x4]:
   the [Avgpool2d_sem] instance at m1=4, m2=4, k=2. *)
Lemma AvgPool2d_equiv_concrete_4x4 :
  forall (input : exp (ary '{4} (ary '{4} num)))
         (output : acc (ary '{2} (ary '{2} num)))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{2} (ary '{2} num)), exp_independent_of_acc input out) ->
    (forall p i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Avgpool2d 4 4 2 input)) rho =
    eval (@Avgpool2d_comm 4 4 2 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  exact (@Avgpool2d_sem 4 4 2 input (Nat.lt_0_succ 1) Hin Hout output rho Hdisj Hundef).
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.MaxPool3d_equiv_concrete_1x4x4]:
   the [Maxpool3d_sem] instance at filernum=1, m1=4, m2=4, k=2. *)
Lemma MaxPool3d_equiv_concrete_1x4x4 :
  forall (input : exp (ary '{1} (ary '{4} (ary '{4} num))))
         (output : acc (ary '{1} (ary '{2} (ary '{2} num))))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{1} (ary '{2} (ary '{2} num))), exp_independent_of_acc input out) ->
    (forall p nu i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ nu} |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Maxpool3d 1 4 4 2 input)) rho =
    eval (@Maxpool3d_comm 1 4 4 2 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  exact (@Maxpool3d_sem 1 4 4 2 input (Nat.lt_0_succ 0) (Nat.lt_0_succ 1) Hin Hout output rho Hdisj Hundef).
Qed.

(* Replacement for the former axiom [CNN_Examples_MiniAlexNet.MaxPool4d_equiv_1_1_4_4]:
   the [Maxpool4d_sem] instance at batch=1, filernum=1, m1=4, m2=4, k=2. *)
Lemma MaxPool4d_equiv_1_1_4_4 :
  forall (input : exp (ary '{1} (ary '{1} (ary '{4} (ary '{4} num)))))
         (output : acc (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))), exp_independent_of_acc input out) ->
    (forall p b nu i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ b} |{ nu} |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Maxpool4d 1 1 4 4 2 input)) rho =
    eval (@Maxpool4d_comm 1 1 4 4 2 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  exact (@Maxpool4d_sem 1 1 4 4 2 input (Nat.lt_0_succ 0) (Nat.lt_0_succ 0) (Nat.lt_0_succ 1)
    Hin Hout output rho Hdisj Hundef).
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.Flatten3d_equiv_1_2_2]:
   the [Flatten3d_sem] instance at channel=1, m1=2, m2=2. *)
Lemma Flatten3d_equiv_1_2_2 :
  forall (input : exp (ary '{1} (ary '{2} (ary '{2} num))))
         (output : acc (ary '{4} num))
         (rho : PCG.env),
    (forall out : acc (ary '{4} num), exp_independent_of_acc input out) ->
    eval (A(output, @Flatten3d 1 2 2 input)) rho =
    eval (@Flatten3d_comm 1 2 2 input output) rho.
Proof.
  intros input output rho Hout.
  apply (@Flatten3d_sem 1 2 2 input output rho); try assumption; lia.
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.lenet5_pool1_equiv]:
   the [Maxpool3d_sem] instance at filernum=6, m1=28, m2=28, k=2.  The
   imperative side is the generic loopacc-based [Maxpool3d_comm] from
   [CNN_Examples_Base_Ops.v]; see the comment at the former axiom site in
   [CNN_Examples_LeNet5.v] for why the concrete [new]-based
   [lenet5_pool1_comm] is not used. *)
Lemma lenet5_pool1_equiv :
  forall (input : exp (ary '{6} (ary '{28} (ary '{28} num))))
         (output : acc (ary '{6} (ary '{14} (ary '{14} num))))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{6} (ary '{14} (ary '{14} num))), exp_independent_of_acc input out) ->
    (forall p nu i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ nu} |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Maxpool3d 6 28 28 2 input)) rho =
    eval (@Maxpool3d_comm 6 28 28 2 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  exact (@Maxpool3d_sem 6 28 28 2 input (Nat.lt_0_succ 5) (Nat.lt_0_succ 1) Hin Hout output rho Hdisj Hundef).
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.lenet5_pool2_equiv]:
   the [Maxpool3d_sem] instance at filernum=16, m1=10, m2=10, k=2. *)
Lemma lenet5_pool2_equiv :
  forall (input : exp (ary '{16} (ary '{10} (ary '{10} num))))
         (output : acc (ary '{16} (ary '{5} (ary '{5} num))))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    (forall out : acc (ary '{16} (ary '{5} (ary '{5} num))), exp_independent_of_acc input out) ->
    (forall p nu i0 i1, @PCG.in_acc num p tmp_scalar_acc ->
      ~ @PCG.in_acc num p (output |{ nu} |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Maxpool3d 16 10 10 2 input)) rho =
    eval (@Maxpool3d_comm 16 10 10 2 input output) rho.
Proof.
  intros input output rho Hin Hout Hdisj Hundef.
  exact (@Maxpool3d_sem 16 10 10 2 input (Nat.lt_0_succ 15) (Nat.lt_0_succ 1) Hin Hout output rho Hdisj Hundef).
Qed.

(* Replacement for the former axiom [CNN_Examples_LeNet5.lenet5_flatten_equiv]:
   the [Flatten3d_sem] instance at channel=16, m1=5, m2=5. *)
Lemma lenet5_flatten_equiv :
  forall (input : exp (ary '{16} (ary '{5} (ary '{5} num))))
         (output : acc (ary '{(16*5*5)} num))
         (rho : PCG.env),
    (forall out : acc (ary '{(16*5*5)} num), exp_independent_of_acc input out) ->
    eval (A(output, @Flatten3d 16 5 5 input)) rho =
    eval (@Flatten3d_comm 16 5 5 input output) rho.
Proof.
  intros input output rho Hout.
  apply (@Flatten3d_sem 16 5 5 input output rho); try assumption; lia.
Qed.
