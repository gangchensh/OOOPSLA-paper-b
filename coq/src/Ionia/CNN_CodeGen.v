From Stdlib Require Import Reals String Nat List Bool Arith Morphisms.
Require Import Logic.FunctionalExtensionality.
Require Export Ionia.CNN_CodeGen_Core.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.CNN_CodeGen_Combinators.
Import ListNotations.
Set Implicit Arguments.

(***************************** Generating C Code **************************)

(* NOTE: The definitions of [comm], [A], [C], and the basic combinators now
   live in [Ionia.CNN_CodeGen_Core.v].  This file imports the semantic
   combinators from [Ionia.CNN_CodeGen_Combinators.v] so that the five
   foundational axioms can be stated and proved as semantic theorems. *)

(* ------------------------------------------------------------------------ *)
(* Legacy AST-level equalities for code-generation proofs.                  *)
(*                                                                            *)
(* The AST-level Leibniz axioms [mkvSeq_equiv_ast], [If_equiv_ast] and        *)
(* [If1_equiv_ast] (and the rule theorems [AmkvSeq], [Aif], [Aif1], [Amax],   *)
(* [Asum] derived from them) have been removed from the main build.  The      *)
(* golden-test theorems that used them ([convert1_CG], [padl1d_CG], [sum_CG], *)
(* [ReLU1d_equiv], ...) now live in [Ionia.legacy.CG_golden_tests], which     *)
(* re-declares the axioms locally and is not part of [_CoqProject].           *)
(* ------------------------------------------------------------------------ *)

(* ------------------------------------------------------------------------ *)
(* Semantic versions of the five foundational combinators.                  *)
(* ------------------------------------------------------------------------ *)

Section Semantic_RewriteRules.

Theorem mkvSeq_equiv_sem:
  forall (n : nat) (d : data) (f : fin n -> exp d) (a : acc (ary '{n} d)) (rho : PCG.env),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (a |:= mkvSeq f) rho = eval (seqfor (fun i : fin n => a |{ i} |:= f i)) rho.
Proof.
  intros n d f a rho H.
  rewrite (Ionia.CNN_CodeGen_Combinators.mkvSeq_equiv_sem f H). reflexivity.
Qed.

Theorem mkvPar_equiv_sem:
  forall (n : nat) (d : data) (f : fin n -> exp d) (a : acc (ary '{n} d)) (rho : PCG.env),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (a |:= mkvPar f) rho = eval (parfor a (fun (i : fin n) (o : acc d) => o |:= f i)) rho.
Proof.
  intros n d f a rho H.
  rewrite (Ionia.CNN_CodeGen_Combinators.mkvPar_equiv_sem f H). reflexivity.
Qed.

Theorem If_equiv_sem:
  forall (n : nat) (d : data) (a : acc (ary '{n} d)) (b : bexp)
         (e1 e2 : exp d) (i : fin n) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (a |{ i} |:= (if bexp2bool b then e1 else e2)) rho =
    eval (If b (a |{ i} |:= e1, a |{ i} |:= e2)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.If_equiv_sem; assumption.
Qed.

Theorem If1_equiv_sem:
  forall (d : data) (a : acc d) (b : bexp) (e1 e2 : exp d) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (a |:= (if bexp2bool b then e1 else e2)) rho =
    eval (If b (a |:= e1, a |:= e2)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.If1_equiv_sem; assumption.
Qed.

Theorem cIf_equiv_sem:
  forall (d : data) (b : bexp) (e1 e2 : exp d) (c : exp d -> comm) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (c (if bexp2bool b then e1 else e2)) rho =
    eval (If b (c e1, c e2)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.cIf_equiv_sem; assumption.
Qed.

Theorem AmkvSeq_sem: forall (n:nat) (d:data) (f:fin n -> exp d) a rho,
  (forall i, exp_independent_of_acc (f i) a) ->
  eval (A(a, mkvSeq f)) rho = eval (mkvSeql (fun i o => A(o, f i)) a) rho.
Proof.
  intros. unfold mkvSeql, A. apply mkvSeq_equiv_sem; assumption.
Qed.

Theorem AmkvPar_sem: forall (n:nat) (d:data) (f:fin n -> exp d) a rho,
  (forall i, exp_independent_of_acc (f i) a) ->
  eval (A(a, mkvPar f)) rho = eval (mkvParl (fun i o => A(o, f i)) a) rho.
Proof.
  intros. unfold mkvParl, A. apply mkvPar_equiv_sem; assumption.
Qed.

Theorem Aif_sem: forall (n:nat) (d:data) (a:acc(ary '{n} d)) (b:bexp) e1 e2 i rho,
  DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
  eval (A(a|{i},if bexp2bool b then e1 else e2)) rho = eval (If b (A(a|{i},e1),A(a|{i},e2))) rho.
Proof.
  intros. unfold A. apply If_equiv_sem; assumption.
Qed.

Theorem Aif1_sem: forall(d:data) (a:acc d) (b:bexp) e1 e2 rho,
  DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
  eval (a|:= if bexp2bool b then e1 else e2) rho = eval (If b (a|:= e1,a|:=e2)) rho.
Proof.
  intros. apply If1_equiv_sem; assumption.
Qed.

Theorem Cif_sem: forall (d:data)(b:bexp) e1 e2 (c:exp d -> comm) rho,
  DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
  eval (C(if bexp2bool b then e1 else e2, c)) rho = eval (If b (C(e1,c),C(e2,c))) rho.
Proof.
  intros. unfold C. apply cIf_equiv_sem; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(* Semantic versions of the seven remaining AST axioms.                     *)
(* These are restatements of the theorems proved in                         *)
(* [Ionia.CNN_CodeGen_Combinators.v].                                       *)
(* ------------------------------------------------------------------------ *)

Theorem new_equiv_sem:
  forall d (e1 : exp d) (c : exp d -> comm) (rho : PCG.env),
    new_continuation_ok c e1 ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined d wtmp rho ->
    eval (new (fun tmp => let (w,v) := tmp in w |:= e1 '; c v)) rho =
    eval_aux (c e1) 1 rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.new_equiv_sem; assumption.
Qed.

Theorem reduce_equiv_sem:
  forall (n : nat) (d1 : data) (f : exp d1 -> exp num -> exp num)
         (i : exp num) (e : exp (ary '{n} d1)) (a : acc num) (rho : PCG.env),
    reduce_op_proper f ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp ->
    a <> wtmp ->
    eval (a |:= reduce f i e) rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; a |:= v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.reduce_equiv_sem; assumption.
Qed.

(* Generalized [reduce_equiv_sem] for an arbitrary accumulator type [d2]. *)
Theorem reduce_equiv_sem_gen:
  forall (n : nat) (d1 d2 : data) (f : exp d1 -> exp d2 -> exp d2)
         (i : exp d2) (e : exp (ary '{n} d1)) (a : acc d2) (rho : PCG.env),
    reduce_op_proper f ->
    let wtmp := (@vwt d2 "__tmp") in
    @PCG.StructUndefined d2 wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e wtmp ->
    (forall p, @PCG.in_acc d2 p wtmp -> ~ @PCG.in_acc d2 p a) ->
    eval (a |:= reduce f i e) rho =
    eval (@loopacc d2 (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; a |:= v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.reduce_equiv_sem_gen; assumption.
Qed.

Theorem max_equiv_sem:
  forall (n : nat) (e : exp (ary '{n} num)) (a : acc num) (rho : PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    a <> wtmp ->
    eval (a |:= max e) rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= zero ';
      seqfor (fun i0 : fin n => If (gtExp e |[ i0] v) (w |:= e |[ i0], w |:= v)) '; a |:= v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.max_equiv_sem; assumption.
Qed.

Theorem sum_equiv_sem:
  forall (n : nat) (e : exp (ary '{n} num)) (a : acc num) (rho : PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    a <> wtmp ->
    eval (a |:= sum e) rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= zero '; seqfor (fun i0 : fin n => w |:= add e |[ i0] v) '; a |:= v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.sum_equiv_sem; assumption.
Qed.

Theorem creduce_equiv_sem:
  forall (n : nat) (d1 : data) (f : exp d1 -> exp num -> exp num)
         (i : exp num) (e : exp (ary '{n} d1)) (c : exp num -> comm) (rho : PCG.env),
    reduce_op_proper f ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp ->
    loopacc_continuation_ok c (reduce f i e) ->
    eval_aux (c (reduce f i e)) 1 rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; c v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.creduce_equiv_sem; assumption.
Qed.

Theorem cmax_equiv_sem:
  forall (n : nat) (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (max e) ->
    eval_aux (c (max e)) 1 rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= zero ';
      seqfor (fun i0 : fin n => If (gtExp e |[ i0] v) (w |:= e |[ i0], w |:= v)) '; c v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.cmax_equiv_sem; assumption.
Qed.

Theorem csum_equiv_sem:
  forall (n : nat) (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (sum e) ->
    eval_aux (c (sum e)) 1 rho =
    eval (@loopacc num (fun tmp =>
      let w := vwt tmp in let v := vrd tmp in
      w |:= zero '; seqfor (fun i0 : fin n => w |:= add e |[ i0] v) '; c v)) rho.
Proof.
  intros. apply Ionia.CNN_CodeGen_Combinators.csum_equiv_sem; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(* A/C translator corollaries of the semantic rules above.                  *)
(* ------------------------------------------------------------------------ *)

Theorem Areduce_sem:
  forall (n:nat) (d1:data) (f:exp d1 -> exp num -> exp num) (i:exp num)
         (e:exp (ary '{n} d1)) (a:acc num) (rho:PCG.env),
    reduce_op_proper f ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp ->
    a <> wtmp ->
    eval (A(a, reduce f i e)) rho =
    eval (C(e, fun x => C(i, fun y => reducel (fun x' y' o => A(o, f x' y')) y x (fun r => A(a,r))))) rho.
Proof.
  intros. unfold A, C, reducel. apply reduce_equiv_sem; assumption.
Qed.

(* Generalized [Areduce_sem] for an arbitrary accumulator type [d2]. *)
Theorem Areduce_sem_gen:
  forall (n:nat) (d1 d2:data) (f:exp d1 -> exp d2 -> exp d2) (i:exp d2)
         (e:exp (ary '{n} d1)) (a:acc d2) (rho:PCG.env),
    reduce_op_proper f ->
    let wtmp := (@vwt d2 "__tmp") in
    @PCG.StructUndefined d2 wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e wtmp ->
    (forall p, @PCG.in_acc d2 p wtmp -> ~ @PCG.in_acc d2 p a) ->
    eval (A(a, reduce f i e)) rho =
    eval (C(e, fun x => C(i, fun y => reducel (fun x' y' o => A(o, f x' y')) y x (fun r => A(a,r))))) rho.
Proof.
  intros. unfold A, C, reducel. apply reduce_equiv_sem_gen; assumption.
Qed.

Theorem Amax_sem:
  forall (n:nat) (e:exp (ary '{n} num)) (a:acc num) (rho:PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    a <> wtmp ->
    eval (A(a, max e)) rho =
    eval (C(e, fun x => maxl x (fun x1:exp num => (fun tmp:acc num => A(tmp,x1))) (fun r => A(a,r)))) rho.
Proof.
  intros. unfold A, C, maxl. apply max_equiv_sem; assumption.
Qed.

Theorem Asum_sem:
  forall (n:nat) (e:exp (ary '{n} num)) (a:acc num) (rho:PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    a <> wtmp ->
    eval (A(a, sum e)) rho =
    eval (C(e, fun x => suml x (fun x1:exp num => (fun tmp:acc num => A(tmp,x1))) (fun r => A(a,r)))) rho.
Proof.
  intros. unfold A, C, suml. apply sum_equiv_sem; assumption.
Qed.

Theorem Creduce_sem:
  forall (n:nat) (d1:data) (f:exp d1 -> exp num -> exp num) (i:exp num)
         (e:exp (ary '{n} d1)) (c:exp num -> comm) (rho:PCG.env),
    reduce_op_proper f ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp ->
    loopacc_continuation_ok c (reduce f i e) ->
    eval_aux (c (reduce f i e)) 1 rho =
    eval (C(e, fun x => C(i, fun y => reducel (fun x' y' o => A(o, f x' y')) y x c))) rho.
Proof.
  intros. unfold A, C, reducel. apply creduce_equiv_sem; assumption.
Qed.

(* Generalized [Creduce_sem] for an arbitrary accumulator type [d2]. *)
Theorem Creduce_sem_gen:
  forall (n:nat) (d1 d2:data) (f:exp d1 -> exp d2 -> exp d2) (i:exp d2)
         (e:exp (ary '{n} d1)) (c:exp d2 -> comm) (rho:PCG.env),
    reduce_op_proper f ->
    let wtmp := (@vwt d2 "__tmp") in
    @PCG.StructUndefined d2 wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e wtmp ->
    loopacc_continuation_ok c (reduce f i e) ->
    eval_aux (c (reduce f i e)) 1 rho =
    eval (C(e, fun x => C(i, fun y => reducel (fun x' y' o => A(o, f x' y')) y x c))) rho.
Proof.
  intros. unfold A, C, reducel. apply creduce_equiv_sem_gen; assumption.
Qed.

Theorem Cmax_sem:
  forall (n:nat) (e:exp (ary '{n} num)) (c:exp num -> comm) (rho:PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (max e) ->
    eval_aux (c (max e)) 1 rho =
    eval (C(e, fun x => maxl x (fun x' o' => A(o',x')) c)) rho.
Proof.
  intros. unfold A, C, maxl. apply cmax_equiv_sem; assumption.
Qed.

Theorem Csum_sem:
  forall (n:nat) (e:exp (ary '{n} num)) (c:exp num -> comm) (rho:PCG.env),
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (sum e) ->
    eval_aux (c (sum e)) 1 rho =
    eval (C(e, fun x => suml x (fun x' o' => A(o',x')) c)) rho.
Proof.
  intros. unfold A, C, suml. apply csum_equiv_sem; assumption.
Qed.

(* The [new]-based C-rules are direct corollaries of [new_equiv_sem].
   The LHS uses [eval_aux ... 1] because the continuation is evaluated
   inside the [new] binder at naming depth 1. *)

Theorem CmkvSeq_sem:
  forall (n:nat)(d:data) (f:fin n -> exp d) (c:exp (ary '{n} d) -> comm) (rho:PCG.env),
    new_continuation_ok c (mkvSeq f) ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined (ary '{n} d) wtmp rho ->
    eval_aux (c (mkvSeq f)) 1 rho =
    eval (new (fun tmp => let (w,v) := tmp in A(w, mkvSeq f) '; c v)) rho.
Proof.
  intros. unfold A. symmetry. apply new_equiv_sem; assumption.
Qed.

Theorem CmkvPar_sem:
  forall (n:nat)(d:data) (f:fin n -> exp d) (c:exp (ary '{n} d) -> comm) (rho:PCG.env),
    new_continuation_ok c (mkvPar f) ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined (ary '{n} d) wtmp rho ->
    eval_aux (c (mkvPar f)) 1 rho =
    eval (new (fun tmp => let (w,v) := tmp in A(w, mkvPar f) '; c v)) rho.
Proof.
  intros. unfold A. symmetry. apply new_equiv_sem; assumption.
Qed.

Theorem Clet_sem:
  forall {s t} (e:exp s)(f: exp s -> exp t)(c : exp t -> comm) (rho:PCG.env),
    new_continuation_ok c (let_binding e f) ->
    let wtmp := PCG.acc' (DE.Var "__tmp") in
    @PCG.StructUndefined t wtmp rho ->
    eval_aux (c (let_binding e f)) 1 rho =
    eval (new (fun tmp => let (w,v) := tmp in A(w, let_binding e f) '; c v)) rho.
Proof.
  intros. unfold A. symmetry. apply new_equiv_sem; assumption.
Qed.

End Semantic_RewriteRules.


(* ===================== Rewrite Rules from Functional to Imperative ====================== *)

Section RewriteRules.

Theorem Avar_num: forall (a:acc num) (e: exp num),
  A(a, e) = a|:= e.
Proof. simpl. reflexivity. Qed.

Theorem Aneg : forall (a:acc num) (e:exp num),
  A(a, negate e) = C(e, fun (x:exp num) => a |:= negate x).
Proof. simpl. reflexivity. Qed.

Theorem Aadd : forall (a:acc num) (e1 e2:exp num) ,
  A(a, add e1 e2) = C(e1 , fun x => C(e2 , fun y => a|:= add x y)).
Proof. simpl. reflexivity. Qed.

Theorem Asub : forall (a:acc num) (e1 e2:exp num) ,
  A(a, sub e1 e2) = C(e1 , fun x => C(e2 , fun y => a|:= sub x y)).
Proof. simpl. reflexivity. Qed.

Theorem Amul : forall (a:acc num) (e1 e2:exp num) ,
  A(a, mul e1 e2) = C(e1 , fun x => C(e2 , fun y => a|:= mul x y)).
Proof. simpl. reflexivity. Qed.

Theorem Adiv : forall (a:acc num) (e1 e2:exp num) ,
  A(a, div e1 e2) = C(e1 , fun x => C(e2 , fun y => a|:= div x y)).
Proof. simpl. reflexivity. Qed.

Theorem Adiv_n : forall (a:acc num) (e1 :exp num)(e2:nat) ,
  A(a, div_n e1 e2) = C(e1 , fun x => a|:= div_n x e2).
Proof. simpl. reflexivity. Qed.

Theorem Ascal : forall (a:acc num) (e1:R)( e2:exp num) ,
  A(a, scal e1 e2) = C(e2, fun x => a|:= scal e1 x).
Proof. simpl. reflexivity. Qed.

Theorem Alog : forall (a:acc num) (e:exp num),
  A(a, log e) = C(e, fun (x:exp num) => a |:= log x).
Proof. simpl. reflexivity. Qed.

Theorem Alet: forall {s t} (e:exp s)(f:exp s -> exp t)(a:acc t),
  A(a,let_binding e f ) =  C(e,fun x => letl x (fun x1:exp s => (fun o:acc t => A(o,f x1))) a).
Proof. 
  simpl. unfold letl,let_binding. auto. 
Qed.

(* Proper instances for setoid_rewrite to descend into seqfor/mkvSeql lambdas *)
#[export] Instance Proper_seqfor : forall n, Proper (respectful (pointwise_relation _ eq) eq) (fun p => @seqfor n p).
Proof.
  intros n f g H. simpl. f_equal. apply functional_extensionality. auto.
Qed.

#[export] Instance Proper_mkvSeql : forall n d, Proper (respectful (pointwise_relation _ (pointwise_relation _ eq)) (respectful eq eq)) (fun f a => @mkvSeql n d f a).
Proof.
  intros n d f g H a b Hab. unfold mkvSeql. f_equal; auto.
  apply functional_extensionality. intros i.
  unfold pointwise_relation in H. specialize (H i).
  rewrite Hab. apply H.
Qed.

Theorem Cvar: forall (d:data) (e: exp d) (c: exp d -> comm)  ,
  C(e, c) = c e.
Proof. simpl. reflexivity. Qed.

Theorem Cneg: forall (e:exp num) (c : exp num -> comm) ,
  C(negate e, c) = C(e, fun x => c (negate x)).
Proof. unfold C. auto. Qed.

Theorem Cadd: forall (e1 e2 : exp num) (c : exp num -> comm) ,
  C(add e1 e2, c) = 
  C(e1, fun x => C(e2, fun y => c (add x y))).
Proof. simpl. reflexivity. Qed.

Theorem Csub: forall (e1 e2 : exp num) (c : exp num -> comm) ,
  C(sub e1 e2, c) = 
  C(e1, fun x => C(e2, fun y => c (sub x y))).
Proof. simpl. reflexivity. Qed.

Theorem Cmul: forall (e1 e2 : exp num) (c : exp num -> comm) ,
  C(mul e1 e2, c) = 
  C(e1, fun x => C(e2, fun y => c (mul x y))).
Proof. simpl. reflexivity. Qed.

Theorem Cdiv: forall (e1 e2 : exp num) (c : exp num -> comm) ,
  C(div e1 e2, c) = 
  C(e1, fun x => C(e2, fun y => c (div x y))).
Proof. simpl. reflexivity. Qed.

Theorem Cdiv_n: forall (e1: exp num)(e2:nat) (c : exp num -> comm) ,
  C(div_n e1 e2, c) = 
  C(e1, fun x => c (div_n x e2)).
Proof. simpl. reflexivity. Qed.

Theorem Cscal: forall (e1 :R) (e2 : exp num) (c : exp num -> comm) ,
  C(scal e1 e2, c) = C(e2, fun y => c (scal e1 y)).
Proof. simpl. reflexivity. Qed.

Theorem Clog: forall (e:exp num) (c : exp num -> comm) ,
  C(log e, c) = C(e, fun x => c (log x)).
Proof. simpl. reflexivity. Qed.

End RewriteRules.


(* ==================== Rewrite Rules from Imperative to C ======================== *)

Section CodeGen_OpenMP.

Open Scope string_scope.

(* generate C type declaration. *)
Fixpoint CG_data (d:data) s: string :=
  match d with
   | num => "float "++ s
   | ary n d => (CG_data d (s++"["++(writeNat n)++"]") )
  end.

Inductive Vpath := Aidx (i:nat).

Definition pslist := list Vpath.

Fixpoint applyps (v:string) (ps:pslist) : string :=
  match ps with
   | nil => v
   | (Aidx i)::tl => applyps (v ++"["++(writeNat i)++"]") tl 
  end.

Lemma applyps_nil: forall v,
  applyps v nil = v.
Proof. simpl. reflexivity. Qed.

Lemma applyps_Aidx: forall v tl i,
  applyps v ((Aidx i)::tl) = applyps (v ++"["++(writeNat i)++"]") tl.
Proof. simpl. reflexivity. Qed.

Parameter writeR: R -> string.

(* Code generation for acceptor paths.  The array branch is unreachable in
   well-formed use because idxAcc pushes the index onto [ps] before recursing. *)
Fixpoint applyps_path (p : path) (ps : pslist) : string :=
  match p with
  | Var s => applyps s ps
  | @AryIdx n i p' => applyps_path p' (Aidx (fin2nat i) :: ps)
  end.

Fixpoint CG_acc {d:data} (ps : pslist) (a : acc d) {struct d} : string :=
  match d return acc d -> string with
  | num => fun p => applyps_path p ps
  | ary n d' => fun v =>
      match ps with
      | nil => "/* CG_acc: array acceptor without index */"
      | Aidx i :: ps' => CG_acc ps' (v_nth (acc_default d') v i)
      end
  end a.

Arguments CG_acc : simpl never.
Arguments idxAcc : simpl never.
Arguments idx : simpl never.

(* Code generation for scalar real expressions and boolean expressions.
   These two functions are mutually recursive because [REif] carries a boolean
   expression and [BLe]/[BGt] carry real sub-expressions. *)
Fixpoint CG_rexp (e : rexp) : string :=
  match e with
  | REvar x => x
  | REconst r s => s
  | REopp e' => "(- " ++ CG_rexp e' ++ ")"
  | REadd e1 e2 => "(" ++ CG_rexp e1 ++ " + " ++ CG_rexp e2 ++ ")"
  | REsub e1 e2 => "(" ++ CG_rexp e1 ++ " - " ++ CG_rexp e2 ++ ")"
  | REmul e1 e2 => "(" ++ CG_rexp e1 ++ " * " ++ CG_rexp e2 ++ ")"
  | REdiv e1 e2 => "(" ++ CG_rexp e1 ++ ") / (" ++ CG_rexp e2 ++ ")"
  | REdiv_n e' n => "((" ++ CG_rexp e' ++ ") / (" ++ writeNat n ++ "))"
  | REscal r e' => "(" ++ writeR r ++ " * " ++ CG_rexp e' ++ ")"
  | REpow e' n => "(pow(" ++ CG_rexp e' ++ ", " ++ writeNat n ++ "))"
  | REexp e' => "exp(" ++ CG_rexp e' ++ ")"
  | REln e' => "(log(" ++ CG_rexp e' ++ "))"
  | REsqrt e' => "sqrt(" ++ CG_rexp e' ++ ")"
  | REif b e1 e2 => "(" ++ writeBexp b ++ " ? " ++ CG_rexp e1 ++ " : " ++ CG_rexp e2 ++ ")"
  end
with writeBexp (b : bexp) : string :=
  match b with
  | BTrue => "true"
  | BFalse => "false"
  | BLe e1 e2 => (CG_rexp e1) ++ " <= " ++ (CG_rexp e2)
  | BGt e1 e2 => (CG_rexp e1) ++ " > " ++ (CG_rexp e2)
  | BLt i n => (writeNat i) ++ " < " ++ (writeNat n)
  | BEq i n => (writeNat i) ++ " == " ++ (writeNat n)
  | BLeb i n => (writeNat i) ++ " <= " ++ (writeNat n)
  | BAnd b1 b2 => (writeBexp b1) ++ " && " ++ (writeBexp b2)
  | BNot b => "!(" ++ (writeBexp b) ++ ")"
  end.

(* Code generation for expressions.  When an array expression is reached
   with no pending index, we emit a placeholder; in well-formed code,
   indexing pushes the index onto [ps] before recursion. *)
Fixpoint CG_exp {d:data} (ps : pslist) (e : exp d) {struct d} : string :=
  match d return exp d -> string with
  | num => fun e => CG_rexp e
  | ary n d' => fun v =>
      match ps with
      | nil => "/* CG_exp: array expression without index */"
      | Aidx i :: ps' => CG_exp ps' (v_nth (exp_default d') v i)
      end
  end e.

Arguments CG_exp : simpl never.

Arguments CG_exp : simpl never.

Definition vstr (cnt:nat) : string := "v"++(writeNat cnt ).
Definition istr (cnt:nat) : string := "i"++(writeNat cnt ).

Parameter str2fin : forall (n:nat), string -> fin n.

Fixpoint cnt_var (c:comm):nat.
Proof.
  refine (match c with
  | skip => 0
  | If b (c1,c2) => cnt_var c1 + cnt_var c2
  | seq (c1,c2) => cnt_var c1 + cnt_var c2
  | assign ac => 0
  | @new t p => 1+ cnt_var(p (vwt "",vrd ""))
  | @loopacc d p => 1 + cnt_var (p "")
  | @seqfor n p => _
  | @parfor n t a p => _
   end).
  - destruct n.
    + exact 1.
    + exact (1 + cnt_var (p (@nat2fin (S n) 0 (Nat.lt_0_succ n)))).
  - destruct n.
    + exact 1.
    + exact (1 + cnt_var (p (@nat2fin (S n) 0 (Nat.lt_0_succ n)) (vwt ""))).
Defined.

Definition cnt_var_seqfor_val (n:nat) : (fin n -> comm) -> nat.
Proof.
  refine (match n as m return (fin m -> comm) -> nat with
  | 0 => fun _ => 1
  | S n' => fun p => 1 + cnt_var (p (@nat2fin (S n') 0 (Nat.lt_0_succ n')))
  end).
Defined.

Definition cnt_var_parfor_val (n:nat) : forall (t:data), (acc (ary '{n} t)) -> (fin n -> acc t -> comm) -> nat.
Proof.
  refine (match n as m return forall (t:data), (acc (ary '{m} t)) -> (fin m -> acc t -> comm) -> nat with
  | 0 => fun _ _ _ => 1
  | S n' => fun t a p => 1 + cnt_var (p (@nat2fin (S n') 0 (Nat.lt_0_succ n')) (vwt ""))
  end).
Defined.

Lemma cnt_skip : cnt_var skip = 0.
Proof. intros; simpl; reflexivity. Qed.

Lemma cnt_If: forall b (c1 c2:comm), 
  cnt_var (If b (c1, c2)) = cnt_var c1 + cnt_var c2.
Proof. intros. simpl. auto. Qed.

Lemma cnt_seq: forall (c1 c2:comm), 
  cnt_var (c1 '; c2) = cnt_var c1 + cnt_var c2.
Proof. intros. simpl. auto. Qed.

Lemma cnt_assign: forall (d:data) a,
   cnt_var (@assign d a) = 0.
Proof. intros; simpl; reflexivity. Qed.

Lemma cnt_new : forall (t:data) p,
  cnt_var (@new t p) =1+ cnt_var(p (vwt "",vrd "")).
Proof. simpl. reflexivity. Qed.

Lemma cnt_loopacc : forall (t:data) p,
  cnt_var (@loopacc t p) = 1 + cnt_var (p "").
Proof. simpl. reflexivity. Qed.

Lemma cnt_seqfor: forall (n:nat) p,
  cnt_var(@seqfor n p) = @cnt_var_seqfor_val n p.
Proof.
  intros. unfold cnt_var_seqfor_val.
  destruct n; reflexivity.
Qed.

Lemma cnt_parfor: forall (n:nat) (t:data) a p,
  cnt_var (@parfor n t a p) = @cnt_var_parfor_val n t a p.
Proof.
  intros. unfold cnt_var_parfor_val.
  destruct n; reflexivity.
Qed.

(* ============================================================
   Parameterized code generation support lemmas
   These lemmas allow cnt_var to reduce when n is a variable
   but we have n > 0.
   ============================================================ *)

Lemma cnt_var_seqfor_n_pos : forall n (Hn : n > 0) (p : fin n -> comm),
  cnt_var (seqfor p) = 1 + cnt_var (p (nat2fin Hn)).
Proof.
  intros n Hn p.
  destruct n.
  - lia.
  - simpl.
    assert (Heq : nat2fin Hn = nat2fin (Nat.lt_0_succ n)).
    { apply fin2nat_inj. rewrite ?fin2nat_nat2fin. reflexivity. }
    rewrite Heq. reflexivity.
Qed.

Lemma cnt_var_parfor_n_pos : forall n (Hn : n > 0) t (a : acc (ary '{n} t)) (p : fin n -> acc t -> comm),
  cnt_var (parfor a p) = 1 + cnt_var (p (nat2fin Hn) (vwt "")).
Proof.
  intros n Hn t a p.
  destruct n.
  - lia.
  - simpl.
    assert (Heq : nat2fin Hn = nat2fin (Nat.lt_0_succ n)).
    { apply fin2nat_inj. rewrite ?fin2nat_nat2fin. reflexivity. }
    rewrite Heq. reflexivity.
Qed.

Fixpoint CG_comm (c:comm) (cnt:nat) : string :=
  match c with
  | skip => "/* skip */"
  | If b (c1,c2) => "if ("++ writeBexp b++")\n  { " ++ CG_comm c1 cnt ++ "}\nelse\n  { " ++ CG_comm c2 cnt ++ "}"
  | seq (c1,c2) => (CG_comm c1 cnt)++"\n"++(CG_comm c2 (cnt_var c1 + cnt))
  | assign (a,e) => (CG_acc [] a) ++" = " ++ (CG_exp [] e)++" ;"
  | @new d p => (CG_data d) (vstr cnt) ++";\n" ++ (CG_comm (p(vwt (vstr cnt),vrd (vstr cnt))) (cnt+1))
  | @loopacc d p => (CG_data d) (vstr cnt) ++";\n" ++ (CG_comm (p (vstr cnt)) (cnt+1))
  | @seqfor n p => "for(int "++(istr cnt)++"=0; "++(istr cnt)++"<"++(writeNat n)++"; "++(istr cnt)++" += 1) \n  { " ++ (CG_comm (p (str2fin n(istr cnt))) (cnt+1)) ++ "}"
  | @parfor n d a p => "#pragma omp parallel for\nfor (int "++(istr cnt)++"=0; "++(istr cnt)++" < "++(writeNat n)++"; "++(istr cnt)++" += 1) \n  { " ++ (CG_comm (p (str2fin n (istr cnt)) (a|{(str2fin n (istr cnt))})) (cnt+1)) ++ "}"
  end.

(** Flat string-builder version: accumulate string fragments into a list.
    This avoids building deeply nested [String.append] trees that blow up
    memory during extraction or pretty-printing. **)
Fixpoint CG_comm_list_aux (c:comm) (cnt:nat) (acc:list string) {struct c} : list string :=
  match c with
  | skip => "/* skip */" :: acc
  | If b (c1,c2) =>
      "if (" :: writeBexp b :: ")\n  { " :: CG_comm_list_aux c1 cnt (
        "}\nelse\n  { " :: CG_comm_list_aux c2 cnt ("}" :: acc))
  | seq (c1,c2) =>
      CG_comm_list_aux c1 cnt ("\n" :: CG_comm_list_aux c2 (cnt_var c1 + cnt) acc)
  | assign (a,e) =>
      CG_acc [] a :: " = " :: CG_exp [] e :: " ;" :: acc
  | @new d p =>
      (CG_data d) (vstr cnt) :: ";\n" ::
      CG_comm_list_aux (p(vwt (vstr cnt),vrd (vstr cnt))) (cnt+1) acc
  | @loopacc d p =>
      (CG_data d) (vstr cnt) :: ";\n" ::
      CG_comm_list_aux (p (vstr cnt)) (cnt+1) acc
  | @seqfor n p =>
      "for(int " :: istr cnt :: "=0; " :: istr cnt :: "<" :: writeNat n :: "; " ::
      istr cnt :: " += 1) \n  { " ::
      CG_comm_list_aux (p (str2fin n(istr cnt))) (cnt+1) ("}" :: acc)
  | @parfor n d a p =>
      "#pragma omp parallel for\nfor (int " :: istr cnt :: "=0; " :: istr cnt ::
      " < " :: writeNat n :: "; " :: istr cnt :: " += 1) \n  { " ::
      CG_comm_list_aux (p (str2fin n (istr cnt)) (a|{(str2fin n (istr cnt))})) (cnt+1) ("}" :: acc)
  end.

Definition CG_comm_list (c:comm) (cnt:nat) : list string :=
  CG_comm_list_aux c cnt nil.

Definition CG_comm_fast (c:comm) (cnt:nat) : string :=
  String.concat "" (CG_comm_list c cnt).

(* Lemmas for backward-compatible rewriting tactics *)
Lemma CGskip : forall (cnt:nat), 
  CG_comm skip cnt = "/* skip */".
Proof. intros; simpl; reflexivity. Qed.

Lemma CGif: forall b c1 c2 cnt,
  CG_comm (If b (c1,c2)) cnt = 
  "if ("++ writeBexp b++")\n  { " ++ CG_comm c1 cnt ++ "}\nelse\n  { " ++ CG_comm c2 cnt ++ "}".
Proof. intros; simpl; reflexivity. Qed.

Lemma CGseq  : forall (p1 p2:comm) (cnt:nat),
   CG_comm (p1 '; p2) cnt  = 
  (CG_comm p1 cnt)++"\n"++(CG_comm p2 (cnt_var p1 + cnt)).
Proof. intros; simpl; reflexivity. Qed.

Lemma CGassign : forall (a:acc num) (e:exp num) (cnt:nat), 
   CG_comm (a |:= e) cnt = 
   (CG_acc [] a) ++" = " ++ (CG_exp [] e)++" ;".
Proof. intros; simpl; reflexivity. Qed.

Lemma CGnew : forall (d:data) (p:acc d * exp d -> comm) (cnt:nat), 
  CG_comm (new p) cnt =
  (CG_data d) (vstr cnt) ++";\n" ++ (CG_comm (p(vwt (vstr cnt),vrd (vstr cnt))) (cnt+1)).
Proof. intros; simpl; reflexivity. Qed.

Lemma CGloopacc : forall (d:data) (p:string -> comm) (cnt:nat),
  CG_comm (@loopacc d p) cnt =
  (CG_data d) (vstr cnt) ++";\n" ++ (CG_comm (p (vstr cnt)) (cnt+1)).
Proof. intros; simpl; reflexivity. Qed.

Lemma CGfor : forall (n:nat) (p:fin n -> comm) (cnt:nat),
  CG_comm (seqfor p) cnt =
  "for(int "++(istr cnt)++"=0; "++(istr cnt)++"<"++(writeNat n)++"; "++(istr cnt)++" += 1) \n  { " ++ (CG_comm (p (str2fin n(istr cnt))) (cnt+1)) ++ "}".
Proof. intros; simpl; reflexivity. Qed.

Lemma CGparfor : forall (n:nat) (d:data) (a:acc (ary '{n} d))
   (p:fin n -> acc d -> comm) (cnt:nat),
  CG_comm (parfor a p) cnt =
  "#pragma omp parallel for\nfor (int "++(istr cnt)++"=0; "++(istr cnt)++" < "++(writeNat n)++"; "++(istr cnt)++" += 1) \n  { " ++ (CG_comm (p (str2fin n (istr cnt)) (a|{(str2fin n (istr cnt))})) (cnt+1)) ++ "}".
Proof. intros; simpl; reflexivity. Qed.





(* Code-generation support lemmas.  Many old axioms are now definitional
   equalities because CG_acc/CG_exp/vrd/vwt are Fixpoints. *)

Lemma CGaccvar : forall (a:string) (ps:pslist),
   @CG_acc num ps (vwt a) = applyps a ps.
Proof. reflexivity. Qed.

Lemma CGidxAcc : forall (d:data) (n:nat) (a:acc (ary '{n} d)) (i:fin n) (ps:pslist),
  CG_acc ps (a |{i}) = CG_acc (Aidx i :: ps) a.
Proof. reflexivity. Qed.

(* r-values. *)

Lemma CGconst_R0 : forall (ps:pslist),
  @CG_exp num ps (REconst R0 "0") = "0".
Proof. reflexivity. Qed.

Lemma CGconst_R1 : forall (ps:pslist),
  @CG_exp num ps (REconst R1 "1") = "1".
Proof. reflexivity. Qed.

Lemma CGexpvar_num : forall (x:string),
   @CG_exp num [] (vrd x) = x.
Proof.
  intro x. cbv [CG_exp vrd CG_rexp].
  destruct (String.eqb x "0") eqn:E0.
  - apply String.eqb_eq in E0. rewrite E0. reflexivity.
  - destruct (String.eqb x "1") eqn:E1.
    + apply String.eqb_eq in E1. rewrite E1. reflexivity.
    + reflexivity.
Qed.

Lemma CGexpvar : forall (x:string) (ps:pslist),
   @CG_exp num ps (vrd x) = x.
Proof.
  intros x ps. cbv [CG_exp vrd CG_rexp].
  destruct (String.eqb x "0") eqn:E0.
  - apply String.eqb_eq in E0. rewrite E0. reflexivity.
  - destruct (String.eqb x "1") eqn:E1.
    + apply String.eqb_eq in E1. rewrite E1. reflexivity.
    + reflexivity.
Qed.

(* Well-formedness side conditions for the general variable code-generation
   lemmas: every array layer of the data type must be matched by an in-bounds
   index on the pending path.  [ps_in_bounds] tolerates leftover indices at
   the scalar leaf (acceptors still print them via [applyps]); [ps_exact]
   requires the path to end exactly at the scalar leaf, because [CG_exp] on
   [num] discards the remaining path. *)
Fixpoint ps_in_bounds (d:data) (ps:pslist) : Prop :=
  match d with
  | num => True
  | ary n d' =>
      match ps with
      | nil => False
      | Aidx i :: ps' => (i < n)%nat /\ ps_in_bounds d' ps'
      end
  end.

Fixpoint ps_exact (d:data) (ps:pslist) : Prop :=
  match d with
  | num =>
      match ps with
      | nil => True
      | _ :: _ => False
      end
  | ary n d' =>
      match ps with
      | nil => False
      | Aidx i :: ps' => (i < n)%nat /\ ps_exact d' ps'
      end
  end.

(* One-step unfolding equations; [CG_acc]/[CG_exp]/[vwt]/[vrd] are marked
   [simpl never], so these are stated explicitly for rewriting. *)
Lemma CG_acc_ary : forall (m:nat) (f:fle m) (d':data) (i:nat) (ps':pslist)
  (v : acc (ary f d')),
  CG_acc (Aidx i :: ps') v = CG_acc ps' (v_nth (acc_default d') v i).
Proof. reflexivity. Qed.

Lemma vwt_ary : forall (m:nat) (f:fle m) (d':data) (a:string),
  @vwt (ary f d') a
  = mk_vec (fun j : fin f => vwt (a ++ "[" ++ writeNat (fin2nat j) ++ "]")).
Proof. reflexivity. Qed.

Lemma CG_exp_ary : forall (m:nat) (f:fle m) (d':data) (i:nat) (ps':pslist)
  (v : exp (ary f d')),
  CG_exp (Aidx i :: ps') v = CG_exp ps' (v_nth (exp_default d') v i).
Proof. reflexivity. Qed.

Lemma vrd_ary : forall (m:nat) (f:fle m) (d':data) (s:string),
  @vrd (ary f d') s
  = mk_vec (fun j : fin f => vrd (s ++ "[" ++ writeNat (fin2nat j) ++ "]")).
Proof. reflexivity. Qed.

Lemma CGaccvar_gen : forall (d:data) (a:string) (ps:pslist),
  ps_in_bounds d ps -> @CG_acc d ps (vwt a) = applyps a ps.
Proof.
  induction d as [| m f d' IHd']; intros a ps Hps.
  - reflexivity.
  - destruct ps as [| [i] ps']; [destruct Hps |].
    destruct Hps as [Hi Hps'].
    rewrite CG_acc_ary, vwt_ary.
    rewrite v_nth_mk_vec with (H := Hi).
    cbv beta.
    rewrite fin2nat_nat2fin.
    rewrite (IHd' _ _ Hps').
    rewrite applyps_Aidx.
    reflexivity.
Qed.

Lemma CGexpvar_gen : forall (d:data) (x:string) (ps:pslist),
  ps_exact d ps -> @CG_exp d ps (vrd x) = applyps x ps.
Proof.
  induction d as [| m f d' IHd']; intros x ps Hps.
  - destruct ps as [| [i] ps']; [| destruct Hps].
    rewrite CGexpvar. rewrite applyps_nil. reflexivity.
  - destruct ps as [| [i] ps']; [destruct Hps |].
    destruct Hps as [Hi Hps'].
    rewrite CG_exp_ary, vrd_ary.
    rewrite v_nth_mk_vec with (H := Hi).
    cbv beta.
    rewrite fin2nat_nat2fin.
    rewrite (IHd' _ _ Hps').
    rewrite applyps_Aidx.
    reflexivity.
Qed.

(* Compatibility axiom for guard-dependent index sites.  Codegen for
   operators like [padr] prints e.g. "input[i0]" where [i0 : fin 3] indexes
   a 2-element array; the C branch guard ([i0 < 2]) makes the access safe at
   runtime, but as a string equality the instance is not provable (when the
   index is out of bounds, [CG_exp] prints the default expression instead of
   the subscripted name).  Use [CGexpvar_gen] (proved) wherever the index is
   statically in bounds; this axiom remains only for those guarded sites and
   is expected to disappear with the str2nat/str2fin definitionalization. *)
Axiom CGexpvar_gen_oob : forall (d:data) (x:string) (ps:pslist),
  @CG_exp d ps (vrd x) = applyps x ps.

Lemma CGneg : forall (e:exp num),
  CG_exp [] (negate e) = "(- "++(CG_exp [] e)++")".
Proof. reflexivity. Qed.

Lemma CGadd : forall (e1 e2 : exp num),
  CG_exp [] (add e1 e2) =
  "("++(CG_exp [] e1)++" + "++(CG_exp [] e2)++")".
Proof. reflexivity. Qed.

Lemma CGsub : forall (e1 e2 : exp num),
  CG_exp [] (sub e1 e2) =
  "("++(CG_exp [] e1)++" - "++(CG_exp [] e2)++")".
Proof. reflexivity. Qed.

Lemma CGmul : forall (e1 e2 : exp num),
  CG_exp [] (mul e1 e2) =
  "("++(CG_exp [] e1)++" * "++(CG_exp [] e2)++")".
Proof. reflexivity. Qed.

Lemma CGdiv : forall (e1 e2 : exp num),
  CG_exp [] (div e1 e2) =
  "("++(CG_exp [] e1)++") / ("++(CG_exp [] e2)++")".
Proof. reflexivity. Qed.

Lemma CGdiv_n : forall (e1 : exp num)(e2:nat),
  CG_exp [] (div_n e1 e2) =
  "(("++(CG_exp [] e1)++") / ("++(writeNat e2)++"))".
Proof. reflexivity. Qed.

Lemma CGscal : forall (e1:R)(e2 : exp num),
  CG_exp [] (scal e1 e2) =
  "("++ (writeR e1) ++" * "++(CG_exp [] e2)++")".
Proof. reflexivity. Qed.

Lemma CGlog : forall (e:exp num),
  CG_exp [] (log e) = "(log("++(CG_exp [] e)++"))".
Proof. reflexivity. Qed.

Lemma CGidx : forall (d:data) (n:nat) (e:exp (ary '{n} d)) 
  (i: fin n) (ps:pslist),
  CG_exp ps (idx e i) = CG_exp (Aidx i::ps) e.
Proof.
  intros d n e i ps.
  destruct n; [inversion i; lia | reflexivity].
Qed.

(* [writeBexp] now calls [CG_rexp] directly on the sub-expressions of
   [BLe]/[BGt], so we need a direct indexing lemma for [CG_rexp]. *)
Lemma CGidx_rexp : forall (n:nat) (e:exp (ary '{n} num)) (i:fin n),
  CG_rexp (idx e i) = CG_exp (Aidx i :: []) e.
Proof.
  intros n e i. unfold CG_exp. simpl. reflexivity.
Qed.

(* [v_nth] returns the default element when the natural index is out of bounds. *)
Lemma v_nth_out_of_bounds {A} : forall n (v : vector A n) x0 i,
  i >= n -> v_nth x0 v i = x0.
Proof.
  induction n as [| n' IHn']; intros v x0 i Hi.
  - destruct v. reflexivity.
  - destruct v as [v' a]. simpl. destruct (Nat.eqb i n') eqn:E.
    + apply Nat.eqb_eq in E. subst i. exfalso.
      apply (Nat.lt_irrefl n'). apply Nat.lt_le_trans with (S n');
        [apply le_n_S, le_n | apply Hi].
    + apply IHn' with (v := v').
      eapply Nat.le_trans; [apply le_S; apply le_n | apply Hi].
Qed.

(* Out-of-bounds [v_nth] inside [CG_exp] also yields the default expression. *)
Lemma CG_exp_v_nth_out_of_bounds :
  forall n t (e : exp (ary '{n} t)) i ps,
    i >= n -> CG_exp ps (v_nth (exp_default t) e i) = CG_exp ps (exp_default t).
Proof.
  intros n t e i ps Hi.
  induction ps as [| [j] ps' IHps'].
  - destruct t as [| m Hf t'];
      [ cbv [CG_exp]; f_equal;
        apply (@v_nth_out_of_bounds _ n e (exp_default num) i Hi)
      | cbv [CG_exp]; reflexivity ].
  - destruct t as [| m Hf t'].
    + cbv [CG_exp]. f_equal.
      apply (@v_nth_out_of_bounds _ n e (exp_default num) i Hi).
    + cbv [CG_exp]. fold (@CG_exp (ary '{m} t')). f_equal.
      setoid_rewrite (@v_nth_out_of_bounds _ n e (exp_default (ary Hf t')) i Hi).
      reflexivity.
Qed.

(* safe_idx_nat compiles to plain array indexing.
   Rationale: [v_nth] already returns the default expression when the natural
   index is out of bounds, so both the guarded and the unguarded forms produce
   the same generated C code. *)
(* safe_idx_nat compiles to plain array indexing.
   Rationale: [v_nth] already returns the default expression when the natural
   index is out of bounds, so both the guarded and the unguarded forms produce
   the same generated C code. *)
Theorem CGsafe_idx_nat : forall {n t} (e: exp (ary '{n} t)) (i: nat) (ps: pslist),
  CG_exp ps (safe_idx_nat e i) = CG_exp (Aidx i :: ps) e.
Proof.
  intros n t e i ps.
  unfold safe_idx_nat.
  destruct (Nat.ltb_spec0 i n) as [Hlt | Hnlt].
  - (* In-bounds: both sides reduce to indexing at [i]. *)
    rewrite <- (fin2nat_nat2fin Hlt) at 2.
    unfold CG_exp. fold (@CG_exp t). reflexivity.
  - (* Out-of-bounds: [safe_idx_nat] returns the default, and [v_nth] also
       returns the default by definition. *)
    symmetry. apply CG_exp_v_nth_out_of_bounds.
    apply (proj1 (Nat.nlt_ge i n) Hnlt).
Qed.

Lemma exp_default_simpl1: exp_default num = vrd "0".
Proof. reflexivity. Qed.

Lemma exp_zero : zero = vrd "0".
Proof. reflexivity. Qed.

Lemma exp_one : one = vrd "1".
Proof. reflexivity. Qed.

Lemma exp_default_simpl2: forall n d, 
  exp_default (ary '{n} d) = mkvSeq (fun i => exp_default d).
Proof.  auto. Qed.

Lemma CGleExp : forall (e1 e2 : exp num),
  writeBexp (leExp e1 e2) =
  (CG_exp [] e1)++" <= "++(CG_exp [] e2).
Proof. reflexivity. Qed.

Lemma CGgtExp : forall (e1 e2 : exp num),
  writeBexp (gtExp e1 e2) =
  (CG_exp [] e1)++" > "++(CG_exp [] e2).
Proof. reflexivity. Qed.

Lemma CG_REif : forall (b : bexp) (e1 e2 : exp num),
  CG_exp ([] : pslist) (REif b e1 e2 : exp num) =
  "(" ++ writeBexp b ++ " ? " ++ CG_exp ([] : pslist) (e1 : exp num) ++ " : " ++ CG_exp ([] : pslist) (e2 : exp num) ++ ")".
Proof. reflexivity. Qed.

Lemma CGpExp : forall(e : exp num),
 CG_exp [] (pExp e) = "exp("++(CG_exp [] e)++")".
Proof. reflexivity. Qed.

End CodeGen_OpenMP.

(* Discharges the [ps_in_bounds]/[ps_exact] side conditions generated by
   rewriting with [CGaccvar_gen]/[CGexpvar_gen].  Defined outside the
   section above because [Ltac] definitions are section-local.  The last
   fallback collects [fin_proof] bounds for opaque [fin] terms (such as
   [str2fin] results) so that [lia] can discharge arithmetic indices like
   [str2fin 3 "i0" - 1 < 2]. *)
Ltac CGvar_side :=
  cbn [ps_in_bounds ps_exact fle2nat fle_self];
  (* Loop bounds like [fin (4/2)] reach the side conditions with [Nat.div]
     unreduced (it is marked [simpl never] to protect [writeNat_div]
     rewriting), and zify cannot evaluate them; normalise literal
     div/mod chains explicitly so [lia] sees plain numerals. *)
  cbv [Nat.div Nat.modulo Nat.divmod fst snd];
  repeat split;
  try exact I;
  try apply fin_proof;
  try lia;
  try (repeat match goal with
       | |- context [fin2nat ?x] =>
           lazymatch goal with
           | H : fin2nat x < _ |- _ => fail
           | _ => pose proof (fin_proof x)
           end
       end; lia).

(* =============================Rewriting Tactics=================================== *)

Open Scope string_scope.
Open Scope nat_scope.

(* Prevent simpl from expanding Nat.div/Nat.modulo so that writeNat_div/writeNat_mod
   can match and rewrite them to C syntax. *)
Arguments Nat.div : simpl never.
Arguments Nat.modulo : simpl never.

Lemma writeBexp_leb: forall n i, writeBexp (BLeb i n) =  writeNat i ++ " <= " ++ writeNat n.
Proof. reflexivity. Qed.

Lemma writeBexp_lt: forall n i, writeBexp (BLt i n) =  writeNat i ++ " < " ++ writeNat n.
Proof. reflexivity. Qed.

Lemma writeBexp_eq: forall n i, writeBexp (BEq i n) =  writeNat i ++ " == " ++ writeNat n.
Proof. reflexivity. Qed.

Lemma writeBexp_andb: forall b1 b2, writeBexp (BAnd b1 b2) =  writeBexp b1 ++ " && " ++ writeBexp b2.
Proof. reflexivity. Qed.

Theorem writeNat_nat2fin: forall n m (H: m < n), writeNat (F[m|n] H) = writeNat m.
Proof. intros. unfold writeNat. simpl. reflexivity. Qed.

Axiom writeNat_str2fin: forall n (s:string), writeNat (str2fin n s) = s.
Axiom writeNat_fin2nat_str2fin: forall n s, writeNat (fin2nat (str2fin n s)) = s.

(* NOTE: [writeNat_add]/[writeNat_sub]/[writeNat_mul]/[writeNat_div]/
   [writeNat_mod] are NOT provable as string equalities: [writeNat] prints
   the decimal digits of a numeral (e.g. [writeNat (1+1) = "2"]), while the
   right-hand sides contain C operator syntax (e.g. ["(1) + (1)"]), so the
   two sides differ for every [m] and [n]; no hypothesis can repair them.
   They encode a code-generation convention (symbolic index arithmetic in
   the emitted C syntax) rather than a fact about [writeNat]; eliminating
   them requires reifying index arithmetic instead of printing numerals
   (see docs/proof_axiom_elimination_plan.md).  They are therefore kept as
   axioms on purpose. *)
Axiom writeNat_add: forall (m n:nat),writeNat (m+n) 
  = "(" ++ writeNat m ++ ") + (" ++ writeNat n ++")".

Axiom writeNat_sub: forall (m n:nat),writeNat (m-n) 
  = writeNat m ++ "-" ++ writeNat n.

Axiom writeNat_mul: forall (m n:nat),writeNat (m*n) 
  = "(" ++ writeNat m ++ ") * (" ++ writeNat n ++ ")".

Axiom writeNat_div: forall (m n:nat),writeNat (m/n) 
  ="(" ++ writeNat m ++ ") / (" ++ writeNat n ++ ")".

Axiom writeNat_mod: forall (m n:nat),writeNat (m mod n) 
  ="(" ++ writeNat m ++ ") % (" ++ writeNat n ++ ")".

Ltac hypUnfold :=
  match goal with
  | [ H:= vrd _ |- _] => (unfold H;clear H)
  end.
  
Ltac hypRewrite :=
  match goal with 
  | [ H: writeNat _ = _ |- _] => rewrite ?H ;clear H
  | [ H: writeR _ = _ |- _] => rewrite ?H ;clear H
  end.

Ltac cnt_simpl:=
  rewrite ?cnt_seq,?cnt_skip,?cnt_assign,?cnt_new,?cnt_seqfor,?cnt_parfor,?cnt_If.

Lemma idx_if: forall (b:bool) n d (e1 e2:exp (ary '{n} d)) i,
  (if b then e1 else e2)|[i] = 
  if b then e1|[i] else e2|[i].
Proof. destruct b; auto. Qed.

Lemma add_ifl: forall (b:bool) e1 e2 e3,
  add (if b then e1 else e2) e3 = 
  if b then add e1 e3 else add e2 e3.
Proof. destruct b;auto. Qed.

Lemma add_ifr: forall (b:bool) e1 e2 e3,
  add e1 (if b then e2 else e3) = 
  if b then add e1 e2 else add e1 e3.
Proof. destruct b;auto. Qed.

Ltac CGrw' := rewrite ?CGskip,?cnt_skip,?CGif,?cnt_If,
  ?CGseq,?cnt_seq,?CGassign,?cnt_assign,
  ?CGnew,?cnt_new,?CGloopacc,?cnt_loopacc,
  ?CGfor,?cnt_seqfor,?CGparfor,?cnt_parfor;unfold CG_data.
  
Ltac Accrw:=
  rewrite ?CGidxAcc;
  repeat (rewrite CGaccvar_gen by CGvar_side).

Ltac Exprw:=
  repeat (progress (rewrite ?exp_default_simpl1,?exp_zero,?exp_one,?CGadd,?CGsub,?CGmul,?CGdiv,?CGdiv_n,?CGleExp,?CGgtExp,?CG_REif));
  repeat (progress (rewrite CGidx_rexp; repeat rewrite CGidx; repeat (rewrite CGexpvar_gen by CGvar_side)));
  repeat (progress (rewrite ?CGconst_R0,?CGconst_R1,?CGsafe_idx_nat)).

Lemma add_sub: forall i n k, k<=n -> 
  i + n - k = i + (n-k).
Proof. induction n;lia. Qed.

Lemma add_n_sub_nk: forall i n k, k<=n->
  i + n - (n - k) = i+k.
Proof. intros. rewrite add_sub;try lia. Qed.

Ltac strnat_simpl:=
  repeat (
    try rewrite add_n_sub_nk;
    try rewrite writeNat_nat2fin;
    try rewrite writeNat_str2fin;
    try rewrite writeNat_fin2nat_str2fin;
    try rewrite writeNat_add;
    try rewrite writeNat_sub;
    try rewrite writeNat_mul;
    try rewrite writeNat_div;
    try rewrite writeNat_mod;
    try rewrite writeBexp_lt;
    try rewrite writeBexp_eq;
    try rewrite writeBexp_leb;
    try rewrite writeBexp_andb;
    try rewrite CGconst_R0;
    try rewrite CGconst_R1;
    try rewrite exp_default_simpl1;
    try rewrite exp_zero;
    try rewrite exp_one;
    try (rewrite CGexpvar_gen by CGvar_side);
    try rewrite CGidx;
    try (rewrite CGaccvar_gen by CGvar_side);
    try rewrite CGidxAcc;
    try rewrite CGadd;
    try rewrite CGmul;
    try rewrite CGdiv;
    try rewrite CGdiv_n;
    try rewrite CGgtExp;
    try rewrite CGsafe_idx_nat;
    try rewrite applyps_nil;
    try rewrite applyps_Aidx;
    try simpl
  ). 

Ltac strSimpl:=
  rewrite ?applyps_Aidx,?applyps_nil;
  repeat strnat_simpl;
  repeat hypRewrite;
  unfold vstr,istr;
  unfold writeNat;simpl.

Ltac str_simpl:=
  repeat rewrite exp_default_simpl1;
  repeat rewrite exp_zero;
  repeat rewrite exp_one;
  repeat hypUnfold;
  repeat rewrite CGidx;repeat rewrite CGidxAcc;
  repeat (rewrite CGexpvar_gen by CGvar_side);
  repeat (rewrite CGaccvar_gen by CGvar_side);
  unfold CG_data;strSimpl.

Ltac before_rw:=
  autounfold;
  rewrite ?exp_default_simpl2;
  rewrite ?Nat.sub_add;try lia.

Ltac rw_simpl:=
  rewrite ?idx_mkvSeq;f_simpl.
































(* ===================== Concrete C-Code Generation Example ===================== *)


(* ===================== Concrete C-Code Generation Example ===================== *)

Opaque CG_acc CG_exp.

Section Example.

(* Simple vector addition with a temporary variable:
     float v0;
     v0 = (x + y) ;
     z = v0 ;
*)
Definition vec_add_comm : comm :=
  new (fun tmp => let (w,v) := tmp in
    @assign num (w, add (vrd "x") (vrd "y")) '; 
    @assign num (vwt "z", v)).

(* Theorem showing the generated C code string *)
Theorem vec_add_CG :
  CG_comm vec_add_comm 0 = "float v0;\nv0 = (x + y) ;\nz = v0 ;".
Proof.
  unfold vec_add_comm. simpl. reflexivity.
Qed.

(* A sequential loop for vector copy:
   for(int i0=0; i0<3; i0 += 1) 
   { out[i0] = in[i0] ; }
*)
Definition vec_copy_comm (n:nat) : comm :=
  seqfor (fun i : fin n => 
    @assign num ((vwt "out")|{i}, (vrd "in")|[i])).

(* Theorem showing the generated C loop for n=3 *)
Theorem vec_copy_CG_3 :
  CG_comm (vec_copy_comm 3) 0 =
  "for(int i0=0; i0<3; i0 += 1) \n  { out[i0] = in[i0] ;}".
Proof.
  unfold vec_copy_comm.
  repeat (CGrw'; Accrw; Exprw).
  repeat (rewrite CGaccvar_gen by CGvar_side);
  repeat (rewrite CGexpvar_gen by CGvar_side).
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== Sum/Max Reduction Code Generation ===================== *)
(* The AST-level golden tests [sum_CG] and [max_CG] (together with the
   [sum_input]/[sum_output]/[max_input]/[max_output] scaffolding and the
   [max_debug] sanity check formerly in [max_debug.v]) have been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); they rewrite with
   [Asum]/[Amax], which depend on the AST axioms [sum_equiv_ast]/
   [max_equiv_ast]. *)

End Example.



(* ============================================================
   Custom induction scheme for comm, tailored to cnt_var's recursion
   
   Problem: standard comm_ind gives (forall i:fin n, P (p i)) for seqfor,
   but cnt_var only recurses on ONE specific index when n > 0.
   
   Solution: define a well_formed predicate that mirrors cnt_var's call
   graph, then prove induction only for well_formed commands.
   ============================================================ *)

Inductive cntvar_wf : comm -> Type :=
  | wf_skip : cntvar_wf skip
  | wf_If : forall b c1 c2,
      cntvar_wf c1 -> cntvar_wf c2 -> cntvar_wf (If b (c1,c2))
  | wf_seq : forall c1 c2,
      cntvar_wf c1 -> cntvar_wf c2 -> cntvar_wf (seq (c1,c2))
  | wf_assign : forall (d:data) (a:acc d) (e:exp d), cntvar_wf (assign (a,e))
  | wf_new : forall (d:data) p,
      cntvar_wf (p (@vwt d "", @vrd d "")) -> cntvar_wf (new p)
  | wf_seqfor : forall n' (p : fin (S n') -> comm),
      cntvar_wf (p (nat2fin (Nat.lt_0_succ n'))) -> cntvar_wf (seqfor p)
  | wf_parfor : forall n' d (a : acc (ary '{S n'} d)) (p : fin (S n') -> acc d -> comm),
      cntvar_wf (p (nat2fin (Nat.lt_0_succ n')) (vwt "")) -> cntvar_wf (parfor a p).

(* The custom induction principle: only requires the IH at indices
   where cnt_var actually recurses. *)
Lemma comm_ind_cntvar
  (P : comm -> Prop) :
  P skip ->
  (forall b c1 c2, P c1 -> P c2 -> P (If b (c1,c2))) ->
  (forall c1 c2, P c1 -> P c2 -> P (seq (c1,c2))) ->
  (forall (d:data) (a:acc d) (e:exp d), P (assign (a,e))) ->
  (forall (d:data) p, P (p (@vwt d "", @vrd d "")) -> P (new p)) ->
  (forall n' (p : fin (S n') -> comm),
    P (p (nat2fin (Nat.lt_0_succ n'))) -> P (seqfor p)) ->
  (forall n' d (a : acc (ary '{S n'} d)) (p : fin (S n') -> acc d -> comm),
    P (p (nat2fin (Nat.lt_0_succ n')) (vwt "")) -> P (parfor a p)) ->
  forall c, cntvar_wf c -> P c.
Proof.
  intros Hskip HIf Hseq Hassign Hnew Hseqfor Hparfor c Hwf.
  exact (cntvar_wf_ind (fun c _ => P c) Hskip
    (fun b c1 c2 _ IH1 _ IH2 => HIf b c1 c2 IH1 IH2)
    (fun c1 c2 _ IH1 _ IH2 => Hseq c1 c2 IH1 IH2)
    (fun d a e => Hassign d a e)
    (fun d p _ IH => Hnew d p IH)
    (fun n' p _ IH => Hseqfor n' p IH)
    (fun n' d a p _ IH => Hparfor n' d a p IH)
    Hwf).
Qed.

(* A command built only from seqfor/parfor with n > 0 is cntvar_wf. *)
Lemma cntvar_wf_seqfor : forall n (Hn : n > 0) (p : fin n -> comm),
  cntvar_wf (p (nat2fin Hn)) -> cntvar_wf (seqfor p).
Proof.
  intros n Hn p H. destruct n. lia.
  assert (Heq : nat2fin Hn = nat2fin (Nat.lt_0_succ n))
    by (apply fin2nat_inj; rewrite ?fin2nat_nat2fin; reflexivity).
  rewrite Heq in H. constructor. auto.
Qed.

Lemma cntvar_wf_parfor : forall n (Hn : n > 0) d (a : acc (ary '{n} d)) (p : fin n -> acc d -> comm),
  cntvar_wf (p (nat2fin Hn) (vwt "")) -> cntvar_wf (parfor a p).
Proof.
  intros n Hn d a p H. destruct n. lia.
  assert (Heq : nat2fin Hn = nat2fin (Nat.lt_0_succ n))
    by (apply fin2nat_inj; rewrite ?fin2nat_nat2fin; reflexivity).
  rewrite Heq in H. constructor. auto.
Qed.
