From Stdlib Require Import Reals String Nat List Bool Arith Morphisms.
Require Import Logic.FunctionalExtensionality.
Require Export CNN_Defs.
Import ListNotations.
Set Implicit Arguments.

(***************************** Generating C Code **************************)

(* Note: data, path, acc, exp are defined in DataExp.v (via CNN_Defs)
   and are reused here without redefinition to avoid type incompatibilities. *)

(* Variable read: for scalar data it is a real-expression variable;
   for array data it is a vector of variable reads, to be indexed later.
   Array elements are distinguished by embedding the index in the variable
   name, e.g. [vrd "v0" : exp (ary 2 num)] has leaves [REvar "v0[0]"] and
   [REvar "v0[1]"], matching the C subscription syntax they print to. *)
Fixpoint vrd {d:data} (s:string) : exp d :=
  match d return exp d with
  | num =>
      if String.eqb s "0" then REconst R0 "0"
      else if String.eqb s "1" then REconst R1 "1"
      else REvar s
  | ary n d' => mk_vec (fun i : fin n => vrd (s ++ "[" ++ writeNat (fin2nat i) ++ "]")%string)
  end.
Arguments vrd : simpl never.

(* Variable write target: for scalar data it is a path;
   for array data it is a vector of acceptors, to be indexed later.
   As for [vrd], array elements are distinguished by indexed names such as
   [Var "v0[0]"], so different elements never alias in the environment. *)
Fixpoint vwt {d:data} (s:string) : acc d :=
  match d return acc d with
  | num => Var s
  | ary n d' => mk_vec (fun i : fin n => vwt (s ++ "[" ++ writeNat (fin2nat i) ++ "]")%string)
  end.
Arguments vwt : simpl never.

Definition mkvAcc {d} {n:nat} (f:fin n -> acc d) 
  : acc(ary '{n} d) := mk_vec f.

Fixpoint acc_default (d:data) : acc d :=
 match d with
 | num => vwt "none"
 | ary n d => mkvAcc (fun i => acc_default d)
 end.

(* Primitives for Dual Acceptor *)
Definition idxAcc {n:nat} {t:data} (v:acc (ary '{n} t)) (i: fin n) 
  : acc t := v_idx (acc_default t) v i.
  
Notation " a |{ i } " := (idxAcc a i) (at level 2).

(* ======================== Primitives for command ======================= *)

Inductive comm : Type := 
 | skip    : comm
 | If      : bexp -> comm * comm -> comm
 | seq     : comm * comm -> comm
 | assign  : forall {d:data}, (acc d) * (exp d) -> comm
 | new     : forall {d:data}, ((acc d) * (exp d) -> comm) -> comm
 | loopacc : forall {d:data}, (string -> comm) -> comm
 | seqfor  : forall {n:nat}, (fin n -> comm) -> comm
 | parfor  : forall {n:nat} {d:data}, (acc (ary '{n} d)) ->
    (fin n -> acc d -> comm) -> comm.

Notation " p1 '; p2 " := (seq (p1,p2)) (right associativity,at level 65).
Notation " a |:= e " := (assign (a,e)) (at level 60).


(* ====================== Intermediate Imperative Combinators ============= *)

Definition mkvSeql {n:nat} {d:data} (f:fin n -> acc d -> comm) 
  (out:acc(ary '{n} d)):=
  seqfor (fun i  => f i out|{i}).

Definition mkvParl {n:nat} {d: data} (f:fin n -> acc d -> comm) 
 (out:acc(ary '{n} d)):=
  parfor out (fun i o => f i o).

Definition letl{s t}(e:exp s)(f:exp s -> acc t -> comm)(out:acc t) :=
  f e out.

Definition maxl {n:nat}
  (xs : exp (ary '{n} num))(f:exp num -> acc num -> comm) (c : exp num -> comm) :=
  @loopacc num (fun tmp =>
    let w := vwt tmp in
    let v := vrd tmp in
    (w |:= zero) '; 
    (seqfor (fun i => If (gtExp xs |[i] v) (f (xs|[i]) w , f v w)) '; 
     c v)).

Definition reducel {n:nat} {d1 d2:data}
   (f : exp d1 -> exp d2 -> acc d2 -> comm) (init : exp d2)
   (xs : exp (ary '{n} d1)) (c : exp d2 -> comm) :=
  @loopacc d2 (fun tmp =>
    let w := vwt tmp in
    let v := vrd tmp in
    (w |:= init) '; 
    (seqfor (fun i => f (xs |[i]) v w)) ';
     c v).

Definition suml {n:nat} (xs : exp (ary '{n} num))
  (f:exp num -> acc num -> comm) (c : exp num -> comm) :=
  @loopacc num (fun tmp =>
    let w := vwt tmp in
    let v := vrd tmp in
    (w |:= zero) '; 
    (seqfor (fun i: fin n => f (add (xs |[i]) v) w)) ';
     c v).


(* ==================== Translators from Functional to Imperative ====================== *)

Definition A {d:data} (val:(acc d)*(exp d)) : comm := 
  assign val.
Definition C {d:data} (ec:(exp d)*(exp d -> comm)): comm := 
  let (e,c):= ec in c e.


(* ==================== Auxiliary Axioms from Functional to Imperative ================== *)

(* NOTE (2026-08-13): The five Leibniz axioms for [mkvSeq], [mkvPar], [If],
   [If1], and [cIf] have been migrated to semantic theorems in
   [Ionia.CNN_CodeGen.v].
   NOTE (2026-08-14): All remaining AST-level Leibniz axioms
   ([reduce_equiv_ast], [creduce_equiv_ast], [cmax_equiv_ast],
   [new_equiv_ast], [csum_equiv_ast], [max_equiv_ast], [sum_equiv_ast],
   [mkvSeq_equiv_ast], [If_equiv_ast], [If1_equiv_ast]) have been removed
   from the main build: their only callers were dead AST-level rewrite
   rules/tactics and the AST-level golden tests, which now live in
   [Ionia.legacy.CG_golden_tests] (outside [_CoqProject]; that file
   re-declares the axioms it needs locally).  This file is now axiom-free. *)
