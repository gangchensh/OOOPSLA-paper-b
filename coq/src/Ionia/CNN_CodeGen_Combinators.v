(* Semantic versions of the functional->imperative combinators.

   The 12 combinators in [Ionia/CNN_CodeGen.v] were originally stated as
   Leibniz equalities on the [comm] AST.  The five basic combinators
   ([mkvSeq], [mkvPar], [If], [If1], [cIf]) are now semantic theorems in
   [Ionia.CNN_CodeGen.v]; the remaining seven live as Leibniz axioms in
   [Ionia.CNN_CodeGen_Core.v].  Because some of
   them equate structurally different AST constructors (in particular the
   [loopacc]-based reductions), they cannot all be proved as Leibniz
   equalities without changing the definition of [comm] (e.g. to a quotient
   or to [env -> env]).

   This file collects the *semantic* versions of those combinators, proved
   using the [eval] interpreter from [Ionia/CNN_CodeGen_Semantics.v].  They
   are the intended replacement equalities for a migration from AST rewriting
   to semantic rewriting.

   Status of the 12 combinators:
   - mkvSeq, mkvPar: proved as semantic equalities under an
     [exp_independent_of_acc] side condition.
   - If, If1, cIf: proved as unconditional semantic equalities.
   - new: proved as a semantic equality under the [new_continuation_ok]
     side conditions defined in [CNN_CodeGen_Semantics.v].
   - sum: proved as a semantic equality under the same independence/disjointness
     side conditions as [eval_sum_equiv] in [CNN_CodeGen_Semantics.v].
   - csum: proved as a semantic equality under the [loopacc_continuation_ok]
     side condition in addition to the [eval_sum_equiv] conditions.
   - reduce (scalar accumulator): proved as a semantic equality under
     [reduce_op_proper f], [exp_independent_of_acc] for the input array, and
     disjointness of the output acceptor.
   - reduce_gen (arbitrary accumulator type [d2]): proved as a semantic
     equality under [reduce_op_proper f], [exp_independent_of_acc] for the
     input array, and path-level disjointness of the output acceptor from the
     temporary region.
   - max, sum: proved as semantic equalities under the same
     independence/disjointness side conditions as in [CNN_CodeGen_Semantics.v].
   - creduce (scalar accumulator): proved as a semantic equality under
     [reduce_op_proper f], [exp_independent_of_acc] for the input array, and
     [loopacc_continuation_ok c (CD.reduce f i e)].
   - creduce_gen (arbitrary accumulator type [d2]): stated as a semantic
     equality under the same generic side conditions as [creduce_equiv_sem];
     the proof is currently admitted pending a helper about temporary-region
     idempotence.
   - cmax: proved as a semantic equality under [exp_independent_of_acc] for
     the input array and [loopacc_continuation_ok c (CD.max e)].

   Migration strategy:
   1. Keep this file as the canonical statement of all 12 semantic rules.
   2. Refactor [CNN_CodeGen.v] to stop exporting the Leibniz Axioms; instead
      callers import this file when they need the combinators.
   3. Update callers ([Fusion*.v], [CNN_Examples*.v], etc.) to rewrite under
      [eval] rather than on the raw AST.
   4. Once all callers are migrated, delete the remaining seven [Axiom]s from
      [CNN_CodeGen_Core.v]. *)

From Stdlib Require Import Reals String Nat List Bool Arith.
Require Import Ionia.DataExp.
Require Import Ionia.CNN_Defs.
Require Ionia.Proof_CodeGen.
Require Import Ionia.CNN_CodeGen_Core.
Require Import Ionia.CNN_CodeGen_Semantics.

Set Implicit Arguments.

Module DE := Ionia.DataExp.
Module CD := Ionia.CNN_Defs.
Module PCG := Ionia.Proof_CodeGen.
Module CG := Ionia.CNN_CodeGen_Core.

(* ------------------------------------------------------------------------ *)
(* Array constructors                                                       *)
(* ------------------------------------------------------------------------ *)

Theorem mkvSeq_equiv_sem :
  forall (n : nat) (d : data) (f : fin n -> exp d) (a : acc (ary '{n} d)),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (a |:= mkvSeq f) = eval (seqfor (fun i : fin n => a |{ i} |:= f i)).
Proof.
  intros. apply eval_mkvSeq. assumption.
Qed.

Theorem mkvPar_equiv_sem :
  forall (n : nat) (d : data) (f : fin n -> exp d) (a : acc (ary '{n} d)),
    (forall i, exp_independent_of_acc (f i) a) ->
    eval (a |:= mkvPar f) = eval (parfor a (fun (i : fin n) (o : acc d) => o |:= f i)).
Proof.
  intros. apply eval_mkvPar. assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(* Conditionals                                                             *)
(* ------------------------------------------------------------------------ *)

Theorem If_equiv_sem :
  forall (n : nat) (d : data) (a : acc (ary '{n} d)) (b : bexp)
         (e1 e2 : exp d) (i : fin n) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (a |{ i} |:= (if bexp2bool b then e1 else e2)) rho =
    eval (If b (a |{ i} |:= e1, a |{ i} |:= e2)) rho.
Proof.
  intros. apply eval_If. assumption.
Qed.

Theorem If1_equiv_sem :
  forall (d : data) (a : acc d) (b : bexp) (e1 e2 : exp d) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (a |:= (if bexp2bool b then e1 else e2)) rho =
    eval (If b (a |:= e1, a |:= e2)) rho.
Proof.
  intros. apply eval_If1. assumption.
Qed.

Theorem cIf_equiv_sem :
  forall (d : data) (b : bexp) (e1 e2 : exp d) (c : exp d -> comm) (rho : PCG.env),
    DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end) b = DE.bexp2bool b ->
    eval (c (if bexp2bool b then e1 else e2)) rho =
    eval (If b (c e1, c e2)) rho.
Proof.
  intros. apply eval_cIf. assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(* [new] binder                                                             *)
(* ------------------------------------------------------------------------ *)

Theorem new_equiv_sem :
  forall d (e1 : exp d) (c : exp d -> comm),
    new_continuation_ok c e1 ->
    forall rho,
      @PCG.StructUndefined d (PCG.acc' (DE.Var "__tmp")) rho ->
      eval (new (fun tmp => let (w,v) := tmp in w |:= e1 '; c v)) rho =
      eval_aux (c e1) 1 rho.
Proof.
  intros. apply eval_new_equiv; assumption.
Qed.

(* ------------------------------------------------------------------------ *)
(* Reductions                                                               *)
(* ------------------------------------------------------------------------ *)
(* [reduce_equiv_sem] is now a theorem; the remaining five continuation/If
   variants are still Axioms in [CNN_CodeGen_Semantics.v].  They are gathered
   here so that callers can refer to a single module and so that the
   [CNN_CodeGen.v] Leibniz Axioms can be removed once callers are migrated. *)

Theorem reduce_equiv_sem :
  forall (n : nat) (d1 : data) (f : exp d1 -> exp num -> exp num)
         (i : exp num) (e : exp (ary '{n} d1)) (a : acc num) (rho : PCG.env),
    reduce_op_proper f ->
    let wtmp := (@PCG.acc' num (DE.Var "__tmp") : acc num) in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp ->
    a <> wtmp ->
    eval (a |:= CD.reduce f i e) rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; a |:= v)) rho.
Proof.
  intros n d1 f i e a rho Hf wtmp Hundef Hindep Hneq. subst wtmp.
  apply eval_reduce_equiv; assumption.
Qed.

(* Generalized [reduce_equiv_sem] for an arbitrary accumulator type [d2].
   The disjointness side condition is path-level: the temporary region and the
   output acceptor must not share any leaf path. *)
Theorem reduce_equiv_sem_gen :
  forall (n : nat) (d1 d2 : data) (f : exp d1 -> exp d2 -> exp d2)
         (i : exp d2) (e : exp (ary '{n} d1)) (a : acc d2) (rho : PCG.env),
    reduce_op_proper f ->
    let wtmp := (@CG.vwt d2 "__tmp") in
    @PCG.StructUndefined d2 wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e wtmp ->
    (forall p, @PCG.in_acc d2 p wtmp -> ~ @PCG.in_acc d2 p a) ->
    eval (a |:= CD.reduce f i e) rho =
    eval (@CG.loopacc d2 (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; a |:= v)) rho.
Proof.
  intros n d1 d2 f i e a rho Hf wtmp Hundef Hindep Hdisj. subst wtmp.
  apply eval_reduce_equiv_gen; assumption.
Qed.

Theorem max_equiv_sem :
  forall (n : nat) (e : exp (ary '{n} num)) (a : acc num) (rho : PCG.env),
    let wtmp := (@PCG.acc' num (DE.Var "__tmp") : acc num) in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    a <> wtmp ->
    eval (a |:= CD.max e) rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= CD.zero '; 
      seqfor (fun i0 : fin n =>
        If (CD.gtExp e |[ i0] v) (w |:= e |[ i0], w |:= v)) '; a |:= v)) rho.
Proof.
  intros n e a rho wtmp Hundef Hindep Hneq. subst wtmp.
  apply eval_max_equiv; assumption.
Qed.

Theorem sum_equiv_sem :
  forall (n : nat) (e : exp (ary '{n} num)) (a : acc num) (rho : PCG.env),
    let wtmp := (@PCG.acc' num (DE.Var "__tmp") : acc num) in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    a <> wtmp ->
    eval (a |:= CD.sum e) rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= CD.zero '; seqfor (fun i0 : fin n => w |:= CD.add e |[ i0] v) '; a |:= v)) rho.
Proof.
  intros n e a rho wtmp Hundef Hindep Hneq. subst wtmp.
  apply eval_sum_equiv; assumption.
Qed.

Theorem creduce_equiv_sem :
  forall (n : nat) (d1 : data) (f : exp d1 -> exp num -> exp num)
         (i : exp num) (e : exp (ary '{n} d1)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := (@PCG.acc' num (DE.Var "__tmp") : acc num) in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) num e wtmp ->
    reduce_op_proper f ->
    loopacc_continuation_ok c (CD.reduce f i e) ->
    eval_aux (c (CD.reduce f i e)) 1 rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; c v)) rho.
Proof.
  intros n d1 f i e c rho wtmp Hundef Hindep Hf Hok. subst wtmp.
  apply eval_creduce_equiv; assumption.
Qed.

(* Generalized [creduce_equiv_sem] for an arbitrary accumulator type [d2]. *)
Theorem creduce_equiv_sem_gen :
  forall (n : nat) (d1 d2 : data) (f : exp d1 -> exp d2 -> exp d2)
         (i : exp d2) (e : exp (ary '{n} d1)) (c : exp d2 -> comm) (rho : PCG.env),
    let wtmp := (@CG.vwt d2 "__tmp") in
    reduce_op_proper f ->
    @PCG.StructUndefined d2 wtmp rho ->
    @exp_independent_of_acc (ary '{n} d1) d2 e wtmp ->
    loopacc_continuation_ok c (CD.reduce f i e) ->
    eval_aux (c (CD.reduce f i e)) 1 rho =
    eval (@CG.loopacc d2 (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= i '; seqfor (fun i0 : fin n => w |:= f e |[ i0] v) '; c v)) rho.
Proof.
  intros n d1 d2 f i e c rho wtmp Hf Hundef Hindep Hok. subst wtmp.
  apply eval_creduce_equiv_gen; assumption.
Qed.

Theorem cmax_equiv_sem :
  forall (n : nat) (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := (@PCG.acc' num (DE.Var "__tmp") : acc num) in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (CD.max e) ->
    eval_aux (c (CD.max e)) 1 rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= CD.zero '; 
      seqfor (fun i0 : fin n =>
        If (CD.gtExp e |[ i0] v) (w |:= e |[ i0], w |:= v)) '; c v)) rho.
Proof.
  intros n e c rho wtmp Hundef Hindep Hok. subst wtmp.
  apply eval_cmax_equiv; assumption.
Qed.

Theorem csum_equiv_sem :
  forall (n : nat) (e : exp (ary '{n} num)) (c : exp num -> comm) (rho : PCG.env),
    let wtmp := (@PCG.acc' num (DE.Var "__tmp") : acc num) in
    @PCG.StructUndefined num wtmp rho ->
    @exp_independent_of_acc (ary '{n} num) num e wtmp ->
    loopacc_continuation_ok c (CD.sum e) ->
    eval_aux (c (CD.sum e)) 1 rho =
    eval (@CG.loopacc num (fun tmp =>
      let w := CG.vwt tmp in
      let v := CG.vrd tmp in
      w |:= CD.zero '; seqfor (fun i0 : fin n => w |:= CD.add e |[ i0] v) '; c v)) rho.
Proof.
  intros n e c rho wtmp Hundef Hindep Hok. subst wtmp.
  apply eval_csum_equiv; assumption.
Qed.
