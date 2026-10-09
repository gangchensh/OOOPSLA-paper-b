(* DPIA-style A/C rewrite rules on the semantic model comm := env -> env.

   This file re-establishes the core DPIA route inside Ionia_v2:
   - commands are environment transformations (Proof_CodeGen.comm);
   - A/C translators are functions that produce such commands;
   - every rewrite rule is a Leibniz equality that can be used with [rewrite].

   We keep the option-based environment model (env := path -> option (exp num))
   because it gives a precise account of uninitialised variables.
*)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Eqdep_dec.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

Require Ionia.Proof_CodeGen.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* A/C translators                                                            *)
(* -------------------------------------------------------------------------- *)

Definition A {d:data} (val : acc d * exp d) : comm :=
  let (a, e) := val in assign a e.

Definition C {d:data} (ec : exp d * (exp d -> comm)) : comm :=
  let (e, k) := ec in k e.

Notation "A( a , e )" := (A (a, e)) (at level 60).
Notation "C( e , k )" := (C (e, k)) (at level 60).

(* -------------------------------------------------------------------------- *)
(* Intermediate imperative combinators                                        *)
(* -------------------------------------------------------------------------- *)

Definition mkvSeql {n:nat} {d:data}
  (f : fin n -> acc d -> comm) (out : acc (ary '{n} d)) : comm :=
  seqfor (fun i => f i (out |{i})).

Definition mkvParl {n:nat} {d:data}
  (f : fin n -> acc d -> comm) (out : acc (ary '{n} d)) : comm :=
  parfor out f.

Definition Letl {s t : data}
  (e : exp s) (f : exp s -> acc t -> comm) (out : acc t) : comm :=
  f e out.

(* Reading an accumulator from the environment.  When the path is undefined
   we return the default expression; in well-formed programs this case is
   unreachable. *)
Fixpoint read_exp {d:data} (rho : env) (a : acc d) : exp d :=
  match access rho a with
  | Some e => e
  | None => exp_default d
  end.

(* Imperative reduction skeleton using a temporary accumulator.
   [out] is only used as the temporary path for the [new] block; the final
   result is passed to the continuation [cont]. *)
Definition reducel {n:nat} {s t:data}
  (op : exp s -> exp t -> exp t)
  (init : exp t)
  (xs : exp (ary '{n} s))
  (cont : exp t -> comm)
  (out : acc t) : comm :=
  new (fun tmp : acc t =>
    seq (tmp |:= init)
    (seq (seqfor (fun i : fin n => fun rho =>
             assign tmp (op (xs |[i]) (read_exp rho tmp)) rho))
         (fun rho => cont (read_exp rho tmp) rho))
  ) out.

Definition suml {n:nat}
  (xs : exp (ary '{n} num))
  (cont : exp num -> comm)
  (out : acc num) : comm :=
  reducel add zero xs cont out.

Definition max2 (x y : exp num) : exp num :=
  if gtExp x y then x else y.

Definition maxl {n:nat}
  (xs : exp (ary '{n} num))
  (cont : exp num -> comm)
  (out : acc num) : comm :=
  reducel max2 zero xs cont out.

(* -------------------------------------------------------------------------- *)
(* Basic A-rules for scalar arithmetic                                        *)
(* -------------------------------------------------------------------------- *)

Lemma A_num : forall (a : acc num) (e : exp num),
  A(a, e) = a |:= e.
Proof. reflexivity. Qed.

Lemma A_neg : forall (a : acc num) (e : exp num),
  A(a, negate e) = C(e, fun x => a |:= negate x).
Proof. reflexivity. Qed.

Lemma A_add : forall (a : acc num) (e1 e2 : exp num),
  A(a, add e1 e2) = C(e1, fun x => C(e2, fun y => a |:= add x y)).
Proof. reflexivity. Qed.

Lemma A_sub : forall (a : acc num) (e1 e2 : exp num),
  A(a, sub e1 e2) = C(e1, fun x => C(e2, fun y => a |:= sub x y)).
Proof. reflexivity. Qed.

Lemma A_mul : forall (a : acc num) (e1 e2 : exp num),
  A(a, mul e1 e2) = C(e1, fun x => C(e2, fun y => a |:= mul x y)).
Proof. reflexivity. Qed.

Lemma A_div : forall (a : acc num) (e1 e2 : exp num),
  A(a, div e1 e2) = C(e1, fun x => C(e2, fun y => a |:= div x y)).
Proof. reflexivity. Qed.

Lemma A_div_post : forall (a : acc num) (e1 e2 : exp num),
  A(a, div e1 e2) = C(e1, fun r => a |:= div r e2).
Proof. intros. rewrite A_div. simpl. reflexivity. Qed.

Lemma A_pExp : forall (a : acc num) (e : exp num),
  A(a, pExp e) = C(e, fun r => a |:= pExp r).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* A-rules for array constructors and conditionals                            *)
(* -------------------------------------------------------------------------- *)

Lemma AmkvSeq : forall (n:nat) (d:data) (f : fin n -> exp d) (a : acc (ary '{n} d)),
  A(a, mkvSeq f) = mkvSeql (fun i o => A(o, f i)) a.
Proof.
  intros. unfold A, mkvSeql.
  rewrite assign_ary.
  destruct n.
  - apply seqfor_extensionality. intros i. inversion i; lia.
  - apply seqfor_extensionality. intros i.
    rewrite idx_mkvSeq; auto. lia.
Qed.

(* [parfor] over an array accumulator coincides with [seqfor] over the
   accessor paths [a|{i}]: both are snoc-order folds, and indexing the snoc
   vector [(av, aa)] at [FS[i]] recurses into [av] (v_nth_fin2finS0) while
   the last index ['[n]] selects [aa] (v_nth_last). *)
Lemma parfor_seqfor : forall (n:nat) (d:data) (a : acc (ary '{n} d))
    (p : fin n -> acc d -> comm),
  parfor a p = seqfor (fun i => p i (a|{i})).
Proof.
  intros n; induction n as [| n IHn]; intros d a p.
  - reflexivity.
  - destruct a as [av aa].
    rewrite parfor_Sn, seqfor_Sn.
    change (fst (av, aa)) with av.
    change (snd (av, aa)) with aa.
    assert (HIH := IHn d av (fun i => p FS[i])).
    cbv beta in HIH.
    rewrite HIH. clear HIH.
    f_equal.
    + apply seqfor_extensionality. intros i. cbv beta. f_equal.
      unfold idxAcc, v_idx. cbn [fle2nat fle_self].
      rewrite v_nth_fin2finS0. reflexivity.
    + f_equal. unfold idxAcc, v_idx, ltS. cbn [fle2nat fle_self].
      rewrite v_nth_last. reflexivity.
Qed.

(* [AmkvPar] follows from [parfor_seqfor]: unfolding [mkvParl] exposes
   [parfor], which is rewritten into the [seqfor] over accessor paths; the
   same pointwise argument as [AmkvSeq] (via [idx_mkvPar]) then closes the
   goal. *)
Lemma AmkvPar : forall (n:nat) (d:data) (f : fin n -> exp d) (a : acc (ary '{n} d)),
  A(a, mkvPar f) = mkvParl (fun i o => A(o, f i)) a.
Proof.
  intros. unfold A, mkvParl.
  rewrite assign_ary.
  rewrite parfor_seqfor.
  destruct n.
  - apply seqfor_extensionality. intros i. inversion i; lia.
  - apply seqfor_extensionality. intros i.
    rewrite idx_mkvPar; auto. lia.
Qed.

Lemma Aif1 : forall (d:data) (a : acc d) (b : bool) (e1 e2 : exp d),
  A(a, if b then e1 else e2) = If b (A(a, e1)) (A(a, e2)).
Proof.
  intros. unfold A. simpl. unfold If.
  destruct b; reflexivity.
Qed.

Lemma Aif : forall (n:nat) (d:data) (a : acc (ary '{n} d)) (b : bool) (e1 e2 : exp d) (i : fin n),
  A(a |{i}, if b then e1 else e2) = If b (A(a |{i}, e1)) (A(a |{i}, e2)).
Proof.
  intros. apply Aif1.
Qed.

(* -------------------------------------------------------------------------- *)
(* C-rules                                                                    *)
(* -------------------------------------------------------------------------- *)

Lemma C_neg : forall (e : exp num) (c : exp num -> comm),
  C(negate e, c) = C(e, fun x => c (negate x)).
Proof. reflexivity. Qed.

Lemma C_add : forall (e1 e2 : exp num) (c : exp num -> comm),
  C(add e1 e2, c) = C(e1, fun x => C(e2, fun y => c (add x y))).
Proof. reflexivity. Qed.

Lemma C_sub : forall (e1 e2 : exp num) (c : exp num -> comm),
  C(sub e1 e2, c) = C(e1, fun x => C(e2, fun y => c (sub x y))).
Proof. reflexivity. Qed.

Lemma C_mul : forall (e1 e2 : exp num) (c : exp num -> comm),
  C(mul e1 e2, c) = C(e1, fun x => C(e2, fun y => c (mul x y))).
Proof. reflexivity. Qed.

Lemma C_div : forall (e1 e2 : exp num) (c : exp num -> comm),
  C(div e1 e2, c) = C(e1, fun x => C(e2, fun y => c (div x y))).
Proof. reflexivity. Qed.

Lemma Cif : forall (d:data) (b:bool) (e1 e2 : exp d) (c : exp d -> comm),
  C(if b then e1 else e2, c) = If b (C(e1, c)) (C(e2, c)).
Proof.
  intros. unfold C, If. destruct b; reflexivity.
Qed.

Lemma Clet : forall (s t:data) (e : exp s) (f : exp s -> exp t) (c : exp t -> comm),
  C(let_binding e f, c) = C(e, fun x => C(f x, c)).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Temporary-variable rule                                                    *)
(* -------------------------------------------------------------------------- *)

(* The classic DPIA [new] rule: allocate tmp, initialise it, and then continue
   using the initial value.  In the option model we require that the path used
   for tmp is undefined in the incoming environment.

   Because [new] no longer performs automatic cleanup (it is the plain
   Zonia-style [new f a = f a]), the continuation [c] must not observe the
   temporary path [a]: it must produce the same result on environments that
   only differ inside [a].  This is exactly the freshness condition that the
   generated code satisfies. *)

Definition not_using_a {d:data} (c : exp d -> comm) (a : acc d) : Prop :=
  forall (e : exp d) (rho rho' : env) (p : path),
    (forall q, ~ in_acc q a -> rho q = rho' q) ->
    c e rho p = c e rho' p.

(* Helper: after assigning to a scalar [acc'] path, reading it back yields the value. *)
Lemma read_exp_assign_num : forall (p : path) (e : exp num) (rho : env),
  read_exp ((acc' p |:= e) rho) (acc' p) = e.
Proof.
  intros. unfold read_exp. simpl.
  rewrite update_eq. reflexivity.
Qed.

(* Generalisation to arbitrary data types: after assigning [e] to [acc' p],
   reading [acc' p] back yields [e].  This follows from [access_assign_eq]. *)
Lemma read_exp_assign : forall (d:data) (p : path) (e : exp d) (rho : env),
  read_exp ((acc' p |:= e) rho) (acc' p) = e.
Proof.
  induction d as [| n m d1 IHd]; intros.
  - unfold read_exp. simpl. rewrite update_eq. reflexivity.
  - unfold read_exp.
    rewrite access_assign_eq by reflexivity.
    cbn. reflexivity.
Qed.

(* Assignments to a pure expression only depend on the expression, not on the
   incoming environment.  This is the key fact that lets us observe the final
   output path through an arbitrary sequence of temporary assignments. *)

(* A seqfor of individual assignments writes a value at [p] that does not depend
   on the incoming environment, provided every assignment that does touch [p]
   writes a pure expression. *)
Lemma seqfor_assign_at_path_independent :
  forall (n:nat) (d:data) (a : fin n -> acc d) (e : fin n -> exp d)
    (rho1 rho2 : env) (p : path),
  (exists i, in_acc p (a i)) ->
  (forall i rho1 rho2, in_acc p (a i) -> assign (a i) (e i) rho1 p = assign (a i) (e i) rho2 p) ->
  seqfor (fun i => assign (a i) (e i)) rho1 p = seqfor (fun i => assign (a i) (e i)) rho2 p.
Proof.
  induction n as [| n' IHn]; intros.
  - destruct H as [i _]. exfalso. apply (fin0_empty i).
  - rewrite !seqfor_Sn. unfold seq.
    destruct (classic (in_acc p (a (ltS n')))) as [Hlast | Hlast].
    + assert (Hgoal := H0 (ltS n')
        (seqfor (fun i : fin n' => assign (a (FS[i])) (e (FS[i]))) rho1)
        (seqfor (fun i : fin n' => assign (a (FS[i])) (e (FS[i]))) rho2)
        Hlast).
      exact Hgoal.
    + assert (Hskip : forall rho, assign (a (ltS n')) (e (ltS n')) rho p = rho p).
      { intros. apply assign_not_in_acc. auto. }
      rewrite Hskip, Hskip.
      apply IHn.
      * destruct H as [i Hi].
        destruct (fin_case i) as [[j Hj] | Hj].
        -- exists j. rewrite Hj in Hi. exact Hi.
        -- rewrite Hj in Hi. contradiction.
      * intros i rho1' rho2' Hi'. apply H0. exact Hi'.
Qed.

Lemma assign_pure_independent :
  forall (d:data) (a : acc d) (e : exp d) (rho1 rho2 : env) (p : path),
  in_acc p a ->
  assign a e rho1 p = assign a e rho2 p.
Proof.
  induction d as [| n m d1 IHd]; intros.
  - simpl in H. subst. simpl. rewrite !update_eq. reflexivity.
  - simpl. apply seqfor_assign_at_path_independent.
    + simpl in H. exact H.
    + intros i rho1' rho2' Hi. apply IHd with (rho1 := rho1') (rho2 := rho2'). exact Hi.
Qed.

Lemma new_equiv : forall (e : exp num) (c : exp num -> comm) (p : path) (rho : env),
  @StructUndefined num (acc' p) rho ->
  not_using_a c (acc' p) ->
  new (fun tmp : acc num =>
         seq (tmp |:= e)
         (fun rho' => c (read_exp rho' tmp) rho')
      ) (acc' p) rho = c e rho.
Proof.
  intros. apply functional_extensionality. intro q.
  unfold new, seq, read_exp.
  rewrite (access_assign num p p e rho). rewrite path_eqb_refl.
  apply H0. intro r. intro Hr.
  apply assign_not_in_acc. auto.
Qed.

(* Generalisation of [not_using_a] to arbitrary data types. *)
Definition not_using_acc {d:data} (c : exp d -> comm) (a : acc d) : Prop :=
  forall (e : exp d) (rho rho' : env) (p : path),
    (forall q, ~ in_acc q a -> rho q = rho' q) ->
    c e rho p = c e rho' p.

(* Generalised DPIA [new] rule for arbitrary data types. *)
Lemma new_equiv_gen : forall (d:data) (e : exp d) (c : exp d -> comm) (p : path) (rho : env),
  @StructUndefined d (acc' p) rho ->
  not_using_acc c (acc' p) ->
  new (fun tmp : acc d =>
         seq (tmp |:= e)
         (fun rho' => c (read_exp rho' tmp) rho')
      ) (acc' p) rho = c e rho.
Proof.
  intros. apply functional_extensionality. intro q.
  unfold new, seq.
  rewrite read_exp_assign.
  apply H0.
  intros r Hr. apply assign_not_in_acc. auto.
Qed.

(* Pointwise variant of [new_equiv_gen]: only the value at the observed path
   [p] matters.  This is useful when the continuation is allowed to read the
   temporary as long as the observation path [p] lies outside the temporary. *)
Lemma new_equiv_gen_at_path : forall (d:data) (e : exp d) (c : exp d -> comm)
  (p_tmp : path) (rho : env) (p : path),
  @StructUndefined d (acc' p_tmp) rho ->
  (forall e' rho1 rho2,
    (forall q, ~ @in_acc d q (acc' p_tmp) -> rho1 q = rho2 q) ->
    c e' rho1 p = c e' rho2 p) ->
  new (fun tmp : acc d =>
         seq (tmp |:= e)
         (fun rho' => c (read_exp rho' tmp) rho'))
      (acc' p_tmp) rho p =
  c e rho p.
Proof.
  intros. unfold new, seq.
  rewrite read_exp_assign.
  apply H0.
  intros r Hr. apply assign_not_in_acc. auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reduction rules (admitted for now; to be proved next)                      *)
(* -------------------------------------------------------------------------- *)

(* Sequential update of a scalar accumulator: first store [e1], then read it
   back and store [f] of the read value.  The result is just storing [f e1]. *)
Lemma assign_update_num : forall (p : path) (e1 : exp num) (f : exp num -> exp num),
  ((acc' p) |:= e1) '; (fun rho => ((acc' p) |:= f (read_exp rho (acc' p))) rho)
  = (acc' p) |:= f e1.
Proof.
  intros. apply functional_extensionality. intro rho.
  unfold seq. rewrite read_exp_assign_num.
  apply functional_extensionality. intro q.
  unfold read_exp. simpl.
  destruct (path_eqb p q) eqn:E.
  - apply path_eqb_eq in E. subst q. rewrite !update_eq. reflexivity.
  - apply path_eqb_neq in E. rewrite !update_neq by auto. reflexivity.
Qed.

Lemma reduce_Sn : forall {n:nat} {s t:data}
  (f : exp s -> exp t -> exp t) (init : exp t)
  (xs : vector (exp s) n) (x : exp s),
  reduce f init ((xs, x) : exp (ary '{S n} s)) = f x (reduce f init xs).
Proof.
  intros. unfold reduce. apply v_reduce_Sn.
Qed.

Lemma ary_idx_last : forall {n:nat} {s:data} (xs' : vector (exp s) n) (x : exp s),
  ((xs', x) : exp (ary '{S n} s))|['[n]] = x.
Proof.
  intros. unfold idx, v_idx. simpl. rewrite Nat.eqb_refl. reflexivity.
Qed.

(* Core reduction identity for scalar accumulators. *)
Lemma reduce_aux_num : forall (n:nat) (s:data)
  (op : exp s -> exp num -> exp num) (init : exp num)
  (xs : exp (ary '{n} s)) (p : path),
  ((acc' p) |:= init) '; seqfor (fun i : fin n => fun rho =>
    ((acc' p) |:= op (xs|[i]) (read_exp rho (acc' p))) rho)
  = (acc' p) |:= reduce op init xs.
Proof.
  induction n as [| n' IHn]; intros.
  - (* n = 0 *)
    apply functional_extensionality. intro rho.
    unfold seq, reduce. reflexivity.
  - (* n = S n' *)
    apply functional_extensionality. intro rho.
    destruct xs as [xs' x].
    rewrite seqfor_Sn.
    replace (seqfor (fun (i : fin n') (rho0 : env) =>
               ((acc' p) |:= op ((xs', x) : exp (ary '{S n'} s))|[FS[i]]
                          (read_exp rho0 (acc' p))) rho0))
      with (seqfor (fun (i : fin n') (rho0 : env) =>
               ((acc' p) |:= op (xs'|[i]) (read_exp rho0 (acc' p))) rho0)).
    + rewrite (seq_assoc ((acc' p) |:= init)
                (seqfor (fun (i : fin n') (rho0 : env) =>
                   ((acc' p) |:= op (xs'|[i]) (read_exp rho0 (acc' p))) rho0))
                (fun rho0 : env =>
                   ((acc' p) |:= op ((xs', x) : exp (ary '{S n'} s))|['[n']]
                              (read_exp rho0 (acc' p))) rho0)).
      rewrite (IHn s op init xs' p).
      rewrite assign_update_num.
      rewrite ary_idx_last. rewrite reduce_Sn. reflexivity.
    + apply seqfor_extensionality. intro i.
      apply functional_extensionality. intro rho0.
      unfold idx, v_idx. simpl.
      assert (Hneq : (i =? n')%nat = false).
      { pose proof (fin_proof i) as Hlt.
        destruct (i =? n')%nat eqn:E; auto.
        exfalso. apply Nat.eqb_eq in E. lia. }
      rewrite Hneq. reflexivity.
Qed.

Lemma A_reduce_num : forall (n:nat) (s:data)
  (op : exp s -> exp num -> exp num) (init : exp num)
  (xs : exp (ary '{n} s)) (p : path),
  A(acc' p, reduce op init xs) =
  reducel op init xs (fun r => A(acc' p, r)) (acc' p).
Proof.
  intros. unfold A, reducel, new.
  rewrite (seq_assoc ((acc' p) |:= init)
                     (seqfor (fun i : fin n => fun rho =>
                        ((acc' p) |:= op (xs|[i]) (read_exp rho (acc' p))) rho))
                     (fun rho => ((acc' p) |:= (read_exp rho (acc' p))) rho)).
  rewrite reduce_aux_num.
  replace (fun rho : env => ((acc' p) |:= read_exp rho (acc' p)) rho)
    with (fun rho : env => ((acc' p) |:= (fun old : exp num => old) (read_exp rho (acc' p))) rho).
  - rewrite (assign_update_num p (reduce op init xs) (fun old : exp num => old)). reflexivity.
  - apply functional_extensionality. intro rho. reflexivity.
Qed.

Lemma A_sum : forall (n:nat) (xs : exp (ary '{n} num)) (p : path),
  A(acc' p, sum xs) = suml xs (fun r => A(acc' p, r)) (acc' p).
Proof.
  unfold sum, suml. intros. apply A_reduce_num.
Qed.

(* [C(sum xs, fun r => a |:= k r)] can be implemented by the same reduction
   skeleton, because the final assignment overwrites the accumulator [a]. *)
Lemma C_sum_post : forall (n:nat) (xs : exp (ary '{n} num)) (p : path)
  (k : exp num -> exp num),
  C(sum xs, fun r => (acc' p) |:= k r) =
  suml xs (fun r => (acc' p) |:= k r) (acc' p).
Proof.
  intros. unfold C, suml, reducel, new.
  rewrite (seq_assoc ((acc' p) |:= zero)
                     (seqfor (fun i : fin n => fun rho =>
                        ((acc' p) |:= add (xs|[i]) (read_exp rho (acc' p))) rho))
                     (fun rho : env =>
                        ((acc' p) |:= k (read_exp rho (acc' p))) rho)).
  rewrite reduce_aux_num.
  rewrite <- assign_update_num.
  reflexivity.
Qed.

Corollary A_sum_acc : forall (n:nat) (xs : exp (ary '{n} num)) (a : acc num),
  A(a, sum xs) = suml xs (fun r => A(a, r)) a.
Proof.
  intros.
  assert (Ha: acc' a = a) by (apply acc'_num).
  rewrite <- Ha. rewrite A_sum.
  rewrite Ha. reflexivity.
Qed.

Corollary C_sum_post_acc : forall (n:nat) (xs : exp (ary '{n} num)) (a : acc num)
  (k : exp num -> exp num),
  C(sum xs, fun r => a |:= k r) =
  suml xs (fun r => a |:= k r) a.
Proof.
  intros.
  assert (Ha: acc' a = a) by (apply acc'_num).
  rewrite <- Ha. rewrite C_sum_post.
  rewrite Ha. reflexivity.
Qed.

(* Variant of [A_add] where the second summand is already computed. *)
Lemma A_add_post : forall (a : acc num) (e1 e2 : exp num),
  A(a, add e1 e2) = C(e1, fun r => a |:= add r e2).
Proof.
  intros. rewrite A_add. simpl. reflexivity.
Qed.

(* [A] is a special case of [C] where the continuation immediately assigns. *)
Lemma A_C : forall (d:data) (a : acc d) (e : exp d),
  A(a, e) = C(e, fun x => A(a, x)).
Proof. reflexivity. Qed.

Lemma max_reduce : forall (n:nat) (xs : exp (ary '{n} num)),
  max xs = reduce max2 zero xs.
Proof.
  intros. unfold max, reduce, max2. induction n as [| n' IHn]; intros.
  - reflexivity.
  - destruct xs as [xs' x]. simpl. rewrite IHn. reflexivity.
Qed.

Lemma A_max : forall (n:nat) (xs : exp (ary '{n} num)) (p : path),
  A(acc' p, max xs) = maxl xs (fun r => A(acc' p, r)) (acc' p).
Proof.
  intros. rewrite max_reduce. unfold maxl. apply A_reduce_num.
Qed.

Corollary A_max_acc : forall (n:nat) (xs : exp (ary '{n} num)) (a : acc num),
  A(a, max xs) = maxl xs (fun r => A(a, r)) a.
Proof.
  intros.
  assert (Ha: acc' a = a) by (apply acc'_num).
  rewrite <- Ha. rewrite A_max.
  rewrite Ha. reflexivity.
Qed.

(* [C(max xs)] implemented by the [maxl] reduction skeleton. *)
Lemma C_max_post : forall (n:nat) (xs : exp (ary '{n} num)) (p : path),
  C(max xs, fun r => (acc' p) |:= r) =
  maxl xs (fun r => (acc' p) |:= r) (acc' p).
Proof.
  intros. rewrite max_reduce. unfold C, maxl, reducel, new.
  rewrite (seq_assoc ((acc' p) |:= zero)
                     (seqfor (fun i : fin n => fun rho =>
                        ((acc' p) |:= max2 (xs|[i]) (read_exp rho (acc' p))) rho))
                     (fun rho : env =>
                        ((acc' p) |:= read_exp rho (acc' p)) rho)).
  rewrite (reduce_aux_num n num max2 zero xs p).
  rewrite (assign_update_num p (reduce max2 zero xs) (fun old : exp num => old)).
  unfold C. reflexivity.
Qed.
