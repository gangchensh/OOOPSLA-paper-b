(* Reusable tactics and lemmas for CNN structural fusion proofs.

   The semantic proofs in Fusion_*.v all follow the same recipe, carried out
   under [eval]/[eval_aux] with the semantic combinator rules:

   1. Unfold the functional operators and the fused imperative kernel.
   2. Strip the outer mkvSeq dimensions with AmkvSeq_sem / strip_mkvSeq_sem.
   3. Pull indices out of mkvSeq with idx_mkvSeq.
   4. For each nested sum, package it as [sum e] with a continuation [c] and
      turn it into a loopacc using csum_equiv_sem (via csum_route_sem /
      sum_to_loopacc_sem).
   5. Descend through the resulting seqfor bodies and close the leaf with
      idx_mkvSeq.
   6. Eliminate intermediate buffers with new_equiv_sem / eliminate_new_sem.

   The former AST-level tactic layer (fusion_setup, strip_mkvSeq,
   sum_to_loopacc, eliminate_new, ...) has been removed together with the
   AST-level Leibniz axioms it relied on; the remaining AST-level "golden
   test" theorems that used it now live in [Ionia.legacy.CG_golden_tests]
   (outside the main build).

   This file captures the mechanical parts of that recipe as lemmas. *)

From Stdlib Require Import Reals String Nat List Bool Arith Lra Lia.
From Stdlib Require Import Extraction.
Require Export Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_CodeGen_Semantics.
From Stdlib Require Import Logic.FunctionalExtensionality.
Import ListNotations.
Set Implicit Arguments.
Open Scope string_scope.

(* Keep [bexp2bool] folded so that ReLU conditionals remain in the form
   expected by the assignment-level code generator. *)
Arguments bexp2bool : simpl never.

(* ------------------------------------------------------------------------ *)
(* Small automation lemmas                                                  *)
(* ------------------------------------------------------------------------ *)

Lemma seqfor_extensionality : forall n (f g : fin n -> comm),
  (forall i, f i = g i) -> seqfor f = seqfor g.
Proof.
  intros. f_equal. apply functional_extensionality. auto.
Qed.

(* ------------------------------------------------------------------------ *)
(* Semantic versions of the former AST-level tactics.                        *)
(*                                                                            *)
(* These lemmas rewrite under [eval] rather than on the raw AST.  The old    *)
(* AST-level tactics (fusion_setup, strip_mkvSeq, csum_route, sum_to_loopacc, *)
(* reduce_loopacc_named, reduce_under_seqfor, finish_leaf, repeat_new_equiv,  *)
(* eliminate_new) and the dead helper lemmas [pair_equal_fst]/[pair_equal_snd] *)
(* were removed: their only callers were the AST-level fusion proofs, which   *)
(* have all been migrated to the semantic versions below or moved to          *)
(* [Ionia.legacy.CG_golden_tests].                                            *)
(* ------------------------------------------------------------------------ *)

Module PCG := Ionia.Proof_CodeGen.
Module DE := Ionia.DataExp.

Lemma seqfor_extensionality_sem :
  forall n (f g : fin n -> comm) (rho : PCG.env),
    (forall i eta, eval (f i) eta = eval (g i) eta) ->
    eval (seqfor f) rho = eval (seqfor g) rho.
Proof.
  intros. rewrite !eval_seqfor. apply seqfor_congr. intros i eta. apply H.
Qed.

Lemma simplify_indices_sem :
  forall n d (f : fin n -> exp d) (a : acc (ary '{n} d)) (i : fin n) (rho : PCG.env),
    n > 0 ->
    eval (a|{i} |:= (mkvSeq f)|[i]) rho = eval (a|{i} |:= f i) rho.
Proof.
  intros n d f a i rho H.
  rewrite (DE.idx_mkvSeq _ _ _ H). reflexivity.
Qed.

(* Strip one outer [mkvSeq] dimension under [eval].  Requires the element
   expressions to be independent of the output acceptor. *)
Lemma strip_mkvSeq_sem :
  forall n (d : data) (f : fin n -> exp d) (a : acc (ary '{n} d)) (rho : PCG.env),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (A(a, mkvSeq f)) rho = eval (seqfor (fun i : fin n => a|{i} |:= f i)) rho.
Proof.
  intros. rewrite AmkvSeq_sem by assumption. unfold mkvSeql. simpl. reflexivity.
Qed.

(* [assign] is insensitive to the naming depth used by [eval_aux]. *)
Lemma eval_assign_depth_independent :
  forall depth d (a : acc d) (e : exp d) (rho : PCG.env),
    eval_aux (a |:= e) depth rho = eval (a |:= e) rho.
Proof. reflexivity. Qed.

(* Convert [c (sum e)] into the corresponding [loopacc] under [eval_aux] at
   depth 1.  The side conditions are exactly those of [csum_equiv_sem]. *)
Lemma csum_route_sem :
  forall n (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (sum e) ->
    eval_aux (c (sum e)) 1 rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      (w |:= zero) ';
      seqfor (fun i : fin n => w |:= add e |[i] v) ';
      c v)) rho.
Proof.
  intros. apply csum_equiv_sem; assumption.
Qed.

(* Same route, expressed through the [C]/[suml] translator corollary. *)
Lemma sum_Csum_route_sem :
  forall n (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (sum e) ->
    eval_aux (c (sum e)) 1 rho =
    eval (C(e, fun x => suml x (fun x1 o => A(o, x1)) c)) rho.
Proof.
  intros. apply Csum_sem; assumption.
Qed.

(* Convert [c (sum e)] under plain [eval]; useful when [c (sum e)] is a
   scalar assignment (and therefore depth-independent). *)
Lemma sum_to_loopacc_sem :
  forall n (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    eval (c (sum e)) rho = eval_aux (c (sum e)) 1 rho ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (sum e) ->
    eval (c (sum e)) rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      (w |:= zero) ';
      seqfor (fun i : fin n => w |:= add e |[i] v) ';
      c v)) rho.
Proof.
  intros. rewrite H. apply csum_route_sem; assumption.
Qed.

(* Descend one [loopacc] level when the goal is an [eval] equality.  Equality
   of the bodies is required at naming depth 1 (inside the [loopacc] binder). *)
Lemma reduce_loopacc_named_sem :
  forall d (f g : string -> comm) (rho : PCG.env),
    (forall tmp, eval_aux (f tmp) 1 rho = eval_aux (g tmp) 1 rho) ->
    eval (@loopacc d f) rho = eval (@loopacc d g) rho.
Proof.
  intros. unfold eval. rewrite !eval_loopacc_aux. unfold PCG.seq.
  apply (f_equal (fun e => @PCG.vrm d (CG.vwt (tmp_name 0)) e)). apply H.
Qed.

(* Shorthand for the default accumulator name [tmp]. *)
Lemma reduce_under_seqfor_sem :
  forall d (f g : string -> comm) (rho : PCG.env),
    (forall tmp, eval_aux (f tmp) 1 rho = eval_aux (g tmp) 1 rho) ->
    eval (@loopacc d f) rho = eval (@loopacc d g) rho.
Proof. apply reduce_loopacc_named_sem. Qed.

(* Close the innermost seqfor body after a sum has been introduced, using the
   index-pull lemma [idx_mkvSeq] to turn [(mkvSeq f)|[i]] into [f i]. *)
Lemma finish_leaf_sem :
  forall n (f : fin n -> exp num) (w : acc num) (v : exp num) (rho : PCG.env),
    n > 0 ->
    eval (seqfor (fun i : fin n => w |:= add (mkvSeq f)|[i] v)) rho =
    eval (seqfor (fun i : fin n => w |:= add (f i) v)) rho.
Proof.
  intros. rewrite !eval_seqfor. apply seqfor_congr. intros i eta.
  rewrite (DE.idx_mkvSeq _ _ _ H). reflexivity.
Qed.

(* Eliminate a single intermediate [new] buffer in a semantic goal.  The body
   must have the canonical shape [w |:= e1 '; c v]. *)
Lemma eliminate_new_sem :
  forall d (e1 : exp d) (c : exp d -> comm) (rho : PCG.env),
    new_continuation_ok c e1 ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined d wtmp rho ->
    eval (new (fun tmp => let (w, v) := tmp in w |:= e1 '; c v)) rho =
    eval_aux (c e1) 1 rho.
Proof.
  intros. apply new_equiv_sem; assumption.
Qed.

(* Variant for array-typed [new] buffers whose initial assignment is written
   with [A]. *)
Lemma eliminate_new_array_sem :
  forall n d (f : fin n -> exp d) (c : exp (ary '{n} d) -> comm) (rho : PCG.env),
    new_continuation_ok c (mkvSeq f) ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined (ary '{n} d) wtmp rho ->
    eval (new (fun tmp => let (w, v) := tmp in A(w, mkvSeq f) '; c v)) rho =
    eval_aux (c (mkvSeq f)) 1 rho.
Proof.
  intros. unfold A. apply eliminate_new_sem; assumption.
Qed.
