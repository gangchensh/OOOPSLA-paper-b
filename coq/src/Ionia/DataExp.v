(* -*- coding: utf-8 -*- *)
Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra.
Require Export finType vector.
Import ListNotations.


Set Implicit Arguments.

Inductive data : Set := 
  | num   : data
  | ary   : forall (n:nat), fle n-> data -> data.

Inductive path := 
  | Var : string -> path
  | AryIdx (n:nat) (i:fin n)  : path -> path. 

Fixpoint path_eqb (p1 p2: path) : bool :=
  match p1,p2 with
  | Var p3 , Var p4 => String.eqb p3 p4
  | @AryIdx n1 i1 p3 , @AryIdx n2 i2 p4 => 
    andb (Nat.eqb n1 n2) (andb (Nat.eqb i1 i2) (path_eqb p3 p4))
  | _ , _ => false
  end.

Declare Scope path_scope.
Infix "=?" := path_eqb : path_scope.
Open Scope path_scope.

Lemma path_eqb_refl : forall (p: path),
  p =? p = true.
Proof.
  induction p. simpl. auto.
  - apply String.eqb_refl. 
  - simpl. rewrite ?Nat.eqb_refl. auto.
Qed.

Lemma AryIdx_eq_l: forall (n1 n2:nat) (i1: fin n1) (i2:fin n2)
  (p1 p2: path), n1 = n2 ->
  Nat.eq i1 i2 -> p1 = p2 ->
  @AryIdx n1 i1 p1 = @AryIdx n2 i2 p2.
Proof.
  intros. subst. f_equal. apply fin_eq. auto.
Qed.

Lemma AryIdx_eq_l2: forall (n:nat) (i1: fin n) (i2:fin n)
  (p1 p2: path), i1 = i2 -> p1 = p2 ->
  @AryIdx n i1 p1 = @AryIdx n i2 p2.
Proof.  intros. subst. f_equal. Qed.

Lemma path_eqb_eq: forall (p1 p2:path),
  p1 = p2 <-> p1 =? p2 = true.
Proof.
  intros. split;intros.
  - subst. apply path_eqb_refl.
  - generalize dependent p2. generalize dependent p1.
    induction p1,p2;intros H;inversion H.
    + (* Var s = Var s0 *)
      apply String.eqb_eq in H1. rewrite H1. auto.
    + (* AryIdx i p1 = AryIdx i0 p2 *)
      apply Bool.andb_true_iff in H. inversion H. clear H.
      apply Bool.andb_true_iff in H2.  inversion H2. clear H2. 
      apply AryIdx_eq_l. try apply Nat.eqb_eq;auto.
      apply Nat.eqb_eq. auto. rewrite (IHp1 p2). auto.
      apply H3.
Qed.

Lemma AryIdx_eq_r: forall (n1 n2:nat) (i1: fin n1) (i2:fin n2)
  (p1 p2: path), 
  @AryIdx n1 i1 p1 = @AryIdx n2 i2 p2 ->
  (n1 = n2 /\ fin2nat i1 = fin2nat i2 /\ p1 = p2).
Proof.
  intros. inversion H. split. auto. split. auto. auto.
Qed.

Lemma AryIdx_eq: forall (n1 n2:nat) (i1: fin n1) (i2:fin n2)
  (p1 p2: path), 
  @AryIdx n1 i1 p1 = @AryIdx n2 i2 p2 <->
  (n1 = n2 /\ fin2nat i1 = fin2nat i2 /\ p1 = p2).
Proof. split. apply AryIdx_eq_r. intros. 
  apply AryIdx_eq_l;destruct H,H0;auto.
Qed.

Lemma path_eqb_neq : forall (p1 p2:path),
  p1 <> p2 <-> p1 =? p2 = false.
Proof.
  induction p1. 
  - induction p2; simpl. rewrite eqb_neq.
    split. intros. unfold not. intros. subst. destruct H. auto.
    intros. unfold not. intros. inv H0. contradiction.
    split; auto. intros. unfold not. intros. inv H0.
  - induction p2. split;auto;intros. unfold not. intros. inv H0.
    split. intros. unfold not in H. simpl.
    destruct (n =? n0)%nat eqn:E. destruct (i =? i0)%nat eqn:E1. 
    destruct (path_eqb p1 p2) eqn:E2;auto. apply Nat.eqb_eq in E,E1. apply path_eqb_eq in E2.
    rewrite AryIdx_eq with (n2:=n0) (i2:=i0) (p2:=p2) in H;auto. assert(False).
    apply H. auto. inv H0. auto. auto.
    simpl; intros. unfold not. intros. apply AryIdx_eq in H0. inv H0.
    inv H2. replace (i =? i0)%nat with true in H. rewrite H1,H4 in H. 
    rewrite Nat.eqb_refl,path_eqb_refl in H. simpl in H. inv H. rewrite H3.
    rewrite Nat.eqb_refl. auto.
Qed.

Lemma path_eqb_sym : forall (p1 p2: path) (b:bool),
  p1 =? p2 = b -> p2 =? p1 = b.
Proof.
  induction b;intros. apply path_eqb_eq in H. rewrite H. apply path_eqb_refl.
  apply path_eqb_neq in H. apply path_eqb_neq. auto.
Qed. 

Notation " '{ n } " := (fle_self n) (at level 2).

(* Boolean expressions used both for functional conditional expressions and for
   imperative [If] commands.  Keeping them as an explicit AST lets code
   generation print them directly, while [bexp2bool] gives their static
   semantics and [eval_bexp] gives their runtime semantics in an environment. *)
Inductive bexp : Set :=
  | BTrue
  | BFalse
  | BLe (e1 e2 : rexp)
  | BGt (e1 e2 : rexp)
  | BLt (i n : nat)
  | BEq (i n : nat)
  | BLeb (i n : nat)
  | BAnd (b1 b2 : bexp)
  | BNot (b : bexp)
(* Inductive real-expression AST.  Replacing [exp num = R] with this AST
   makes [CG_exp] a true structural Fixpoint and allows [vm_compute] to
   reduce generated C code strings inside Coq. *)
with rexp : Set :=
| REvar   : string -> rexp
| REconst : R -> string -> rexp
| REopp   : rexp -> rexp
| REadd   : rexp -> rexp -> rexp
| REsub   : rexp -> rexp -> rexp
| REmul   : rexp -> rexp -> rexp
| REdiv   : rexp -> rexp -> rexp
| REdiv_n : rexp -> nat -> rexp
| REscal  : R -> rexp -> rexp
| REpow   : rexp -> nat -> rexp
| REexp   : rexp -> rexp
| REln    : rexp -> rexp
| REsqrt  : rexp -> rexp
| REif    : bexp -> rexp -> rexp -> rexp.

Fixpoint exp (d:data) : Set :=
  match d with
  | num => rexp
  | ary n d => vector (exp d) n
  end.

Fixpoint acc (d:data) : Set :=
  match d with
  | num => path 
  | ary n d => vector (acc d) n
  end.

(* boolean equality over R (kept for denotational use). *)
Definition R_beq (x y : R) : bool :=  
  match Req_dec_T x y with  
  | left _ => true  
  | right _ => false  
  end.

Lemma R_beq_refl : forall x, R_beq x x = true.
Proof. intros x; unfold R_beq; destruct (Req_dec_T x x); auto. Qed.

Lemma R_beq_eq : forall x y, R_beq x y = true -> x = y.
Proof. intros x y; unfold R_beq; destruct (Req_dec_T x y); auto; discriminate. Qed.

Lemma R_beq_sym : forall x y, R_beq x y = R_beq y x.
Proof.
  intros x y; unfold R_beq;
  destruct (Req_dec_T x y) as [H | H];
  destruct (Req_dec_T y x) as [H' | H']; auto;
  try (exfalso; apply H'; symmetry; auto);
  try (exfalso; apply H; symmetry; auto).
Qed.

Lemma R_beq_trans : forall x y z,
  R_beq x y = true -> R_beq y z = true -> R_beq x z = true.
Proof.
  intros x y z H1 H2.
  apply R_beq_eq in H1; apply R_beq_eq in H2; subst.
  apply R_beq_refl.
Qed.

(* Decidable equality over bexp and rexp (mutual). *)
Lemma bexp_eq_dec : forall b1 b2 : bexp, {b1 = b2} + {b1 <> b2}
with rexp_eq_dec : forall e1 e2 : rexp, {e1 = e2} + {e1 <> e2}.
Proof.
  - decide equality; try apply rexp_eq_dec; try apply string_dec; try apply Nat.eq_dec; apply Req_dec_T.
  - decide equality; try apply bexp_eq_dec; try apply string_dec; try apply Nat.eq_dec; apply Req_dec_T.
Defined.

(* boolean equality over rexp (structural). *)
Definition rexp_beq (e1 e2 : rexp) : bool :=
  if rexp_eq_dec e1 e2 then true else false.

(* boolean value equality over exp. *)
Fixpoint exp_beq {d:data} : exp d -> exp d -> bool :=
  match d with
   | num => fun (a1 a2: exp num) => rexp_beq a1 a2
   | ary n d0 => fun (a1 a2: exp (ary n d0)) =>
       vector_eqb (@exp_beq d0) n a1 a2
  end.

(** properties of rexp_beq and exp_beq. **)

Lemma exp_beq_num : forall (a1 a2: exp num), 
  exp_beq a1 a2 = rexp_beq a1 a2.
Proof. intros; reflexivity. Qed.

Lemma exp_beq_ary : forall {d:data} {m:nat} (n:fle m) 
  (a1 a2: exp (@ary m n d)),
  exp_beq a1 a2 = vector_eqb (@exp_beq d) n a1 a2.
Proof. intros; reflexivity. Qed.

(* Properties of rexp_beq *)
Lemma rexp_beq_refl : forall e : rexp, rexp_beq e e = true.
Proof. intros e; unfold rexp_beq; destruct (rexp_eq_dec e e); auto; contradiction. Qed.

Lemma rexp_beq_eq : forall e1 e2, rexp_beq e1 e2 = true -> e1 = e2.
Proof. intros e1 e2; unfold rexp_beq; destruct (rexp_eq_dec e1 e2); auto; discriminate. Qed.

Lemma rexp_beq_sym : forall e1 e2, rexp_beq e1 e2 = rexp_beq e2 e1.
Proof.
  intros e1 e2; unfold rexp_beq;
  destruct (rexp_eq_dec e1 e2) as [H1 | H1];
  destruct (rexp_eq_dec e2 e1) as [H2 | H2]; try auto;
  try (contradiction H2; symmetry; auto);
  try (contradiction H1; symmetry; auto).
Qed.

Lemma rexp_beq_trans : forall e1 e2 e3,
  rexp_beq e1 e2 = true -> rexp_beq e2 e3 = true -> rexp_beq e1 e3 = true.
Proof.
  intros e1 e2 e3 H1 H2.
  apply rexp_beq_eq in H1; apply rexp_beq_eq in H2; subst.
  apply rexp_beq_refl.
Qed.

Lemma rexp_beq_dec : forall e1 e2 : rexp,
  {rexp_beq e1 e2 = true} + {rexp_beq e1 e2 = false}.
Proof.
  intros e1 e2; unfold rexp_beq;
  destruct (rexp_eq_dec e1 e2); [left | right]; auto.
Qed.

(* Reflexivity of exp_beq *)  
Lemma exp_beq_refl :   
  forall (d : data) (x : exp d), exp_beq x x = true.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x. apply rexp_beq_refl.  

  - (* Inductive case: ary *)  
    intros x.  rewrite exp_beq_ary.
    apply vector_eqb_refl.  apply IHIHd'.  
Qed.  

(* Symmetry of exp_beq *)  
Lemma exp_beq_sym :   
  forall (d : data) (x y : exp d), exp_beq x y = exp_beq y x.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x y. apply rexp_beq_sym.  

  - (* Inductive case: ary *)  
    intros x y.  rewrite ?exp_beq_ary.
    apply vector_eqb_sym.  
    exact IHIHd'.  
Qed.  

(* Transitivity of exp_beq *)  
Lemma exp_beq_trans : forall (d : data) (x y z : exp d),   
  exp_beq x y = true -> exp_beq y z = true -> exp_beq x z = true.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x y z Hxy Hyz. eapply rexp_beq_trans; eauto.  

  - (* Inductive case: ary *)  
    intros x y z Hxy Hyz.  rewrite ?exp_beq_ary in *.
    eapply vector_eqb_trans.  
    + exact IHIHd'.  
    + exact Hxy.  
    + exact Hyz.  
Qed. 

(* Decidability of exp_beq *)  
Lemma exp_beq_dec :   
  forall (d : data) (x y : exp d),   
  {exp_beq x y = true} + {exp_beq x y = false}.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x y.  
    apply rexp_beq_dec.  

  - (* Inductive case: ary *)  
    intros x y. rewrite ?exp_beq_ary.
    apply vector_eqb_dec.  
Qed.

Definition mkvSeq {d} {n:nat} (f:fin n -> exp d) 
  : exp(ary '{n} d) := mk_vec f.

Definition mkvPar {d} {n:nat} (f:fin n -> exp d) 
  : exp(ary '{n} d) := mk_vec f.

Fixpoint exp_default (d:data) : exp d :=
 match d with
 | num => REconst R0 "0"
 | ary n d => mkvSeq (fun i:fin n => exp_default d)
 end.

Definition make_nonnegreal (x : R) : nonnegreal :=
  match (Rle_dec 0 x) with
  | left p => mknonnegreal x p
  | right _ => mknonnegreal 0 (Rle_refl 0)
  end.

(* Runtime denotation of boolean expressions.  The [val] argument gives the
   real value of each variable name, so conditions can be evaluated in the
   current execution environment. *)
Fixpoint eval_bexp (val : string -> R) (b : bexp) {struct b} : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | BLe e1 e2 =>
      match Rle_dec (eval_rexp val e1) (eval_rexp val e2) with
      | left _ => true | right _ => false
      end
  | BGt e1 e2 =>
      match Rgt_dec (eval_rexp val e1) (eval_rexp val e2) with
      | left _ => true | right _ => false
      end
  | BLt i n => Nat.ltb i n
  | BEq i n => Nat.eqb i n
  | BLeb i n => Nat.leb i n
  | BAnd b1 b2 => andb (eval_bexp val b1) (eval_bexp val b2)
  | BNot b => negb (eval_bexp val b)
  end
(* Denotation of a real-expression AST.  The [val] argument gives the
   real value of each variable name. *)
with eval_rexp (val : string -> R) (e : rexp) {struct e} : R :=
  match e with
  | REvar s => val s
  | REconst r _ => r
  | REopp e' => Ropp (eval_rexp val e')
  | REadd e1 e2 => Rplus (eval_rexp val e1) (eval_rexp val e2)
  | REsub e1 e2 => Rminus (eval_rexp val e1) (eval_rexp val e2)
  | REmul e1 e2 => Rmult (eval_rexp val e1) (eval_rexp val e2)
  | REdiv e1 e2 => Rdiv (eval_rexp val e1) (eval_rexp val e2)
  | REdiv_n e' n => Rdiv (eval_rexp val e') (INR n)
  | REscal r e' => Rmult r (eval_rexp val e')
  | REpow e' n => pow (eval_rexp val e') n
  | REexp e' => Reals.Rtrigo_def.exp (eval_rexp val e')
  | REln e' => ln (eval_rexp val e')
  | REsqrt e' => Rsqrt (make_nonnegreal (eval_rexp val e'))
  | REif b e1 e2 => if eval_bexp val b then eval_rexp val e1 else eval_rexp val e2
  end.

Definition default_val (s : string) : R := R0.

(* Static boolean evaluator: every variable is replaced by [default_val].
   This is the old semantics, retained for purely static conditions such as
   padding-index tests. *)
Definition bexp2bool (b : bexp) : bool := eval_bexp default_val b.

Fixpoint acc_default (d:data) : acc d :=
 match d with
 | num => Var "none"
 | ary n d => mk_vec (fun i => acc_default d)
 end.

Definition idxAcc {n:nat} {t:data} (v:acc (ary '{n} t)) (i: fin n) 
  : acc t := v_idx (acc_default t) v i.

Notation " a |{ i } " := (idxAcc a i) (at level 2).

Definition idx {n:nat} {t:data} (v:exp (ary '{n} t)) (i: fin n) 
  : exp t := v_idx (exp_default t) v i.

Notation " a |[ i ] " := (idx a i) (at level 2).

Lemma idx_mkvSeq : forall d n (f: fin n -> exp d) i,
  n>0 -> (mkvSeq f)|[i] = f i.
Proof. intros. apply v_idx_mk_vec;auto. Qed.

Lemma idx_mkvPar : forall d n (f: fin n -> exp d) i,
  n>0 -> (mkvPar f)|[i] = f i.
Proof. intros. apply v_idx_mk_vec;auto. Qed.

Notation "FS[ i ]" := (fin2finS i).

Notation "'[ i ]" := (ltS i).


Definition idx_opt {n : nat} {t : data} 
   (v : option (exp (ary '{n} t))) (i : fin n) : option (exp t) :=
  match v with
  | None => None
  | Some v' => Some (idx v' i)
  end. 

Lemma idx_opt_None : forall {n:nat} {t:data} (i : fin n),
  @idx_opt n t None i = None.
Proof. reflexivity. Qed.

Lemma idx_opt_Some : forall n t (v' : exp (ary '{n} t)) (i : fin n),
  @idx_opt n t (Some v') i = Some (idx v' i).
Proof. reflexivity. Qed.

Lemma idx_opt_dependence : forall n t (v1 v2 : option (exp (ary '{n} t))) 
 (i : fin n), v1 = v2 ->  idx_opt v1 i = idx_opt v2 i.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma vector_cons_injective :
  forall (n : nat) (t : data) (v1 v2 : exp (ary '{ S n} t)),
    v1 = v2 <-> (fst v1 = fst v2 /\ snd v1 = snd v2).
Proof.
  intros n t v1 v2.
  split.
  - (* Forward direction: v1 = v2 -> fst v1 = fst v2 /\ snd v1 = snd v2 *)
    intros H.
    rewrite H.
    split; reflexivity.
  - (* Backward direction: fst v1 = fst v2 /\ snd v1 = snd v2 -> v1 = v2 *)
    intros [H_head H_last].
    destruct v1 as [v1_head v1_last], v2 as [v2_head v2_last].
    simpl in H_head, H_last.
    rewrite H_head, H_last.
    reflexivity.
Qed.

Lemma idx_opt_dependence_inv : forall n t (v1 v2 : option (exp (ary '{S n} t))),
  (forall i : fin (S n), idx_opt v1 i = idx_opt v2 i) -> v1 = v2.
Proof.
  intros n t v1 v2 H.
  destruct v1 as [v1 |], v2 as [v2 |]; try reflexivity. 
  - apply f_equal.
(*
    induction n as [| n IHn].
    + (* Base case: n = 0 *)
      destruct v1, v2. destruct e,e0. reflexivity.
      
    + (* Inductive case: n = S n *)
*) 
     rewrite (@vector_eq_v_nth (exp t) (S n) v1 v2 (exp_default t)).
      intro i.
      specialize (H i).
      unfold idx_opt in H. inversion H. unfold idx,v_idx in H1.
      exact H1.
  - (* Some v1 = None *)
    specialize(H (fin0n n)). inversion H. 
  - (* None = Some v1 *)
    specialize(H (fin0n n)). inversion H. 
Qed.

Theorem idx_opt_ary_equiv : forall n t (v1 v2 : option (exp (ary '{S n} t))),
  (forall i : fin (S n), idx_opt v1 i = idx_opt v2 i) <-> v1 = v2.
Proof. split. 
+ apply idx_opt_dependence_inv.
+ intros. apply (@idx_opt_dependence (S n) t v1 v2 i). exact H.
Qed.

(* appear not provable:
Lemma idx_opt_dependence_inv0 : 
  forall t (v1 v2 : option (exp (ary '{0} t))),
    (forall i : fin 0, idx_opt v1 i = idx_opt v2 i) -> v1 = v2.
*)
Lemma idx_opt_dependence_inv0_counterexample :
  exists t (v1 v2 : option (exp (ary '{0} t))),
    (forall i : fin 0, idx_opt v1 i = idx_opt v2 i) /\ v1 <> v2.
Proof.
  (* Choose an arbitrary type t *)
  exists num. (* Example: t = num *)
  (* Define v1 and v2 *)
  exists (Some tt), None.
  split.
  - (* Prove the hypothesis holds vacuously *)
    intros i.
    destruct i as [i Hi].
    (* Since i : fin 0, we have i < 0, which is impossible *)
    inversion Hi.
  - (* Prove v1 <> v2 *)
    discriminate.
Qed.

(* access the last element. *)
Lemma idx_opt_last :
  forall (n : nat) (d : data) (v : (exp (ary '{n} d))) (e':exp d) (K:n<S n),
  @idx_opt (S n) d (Some (v,e')) (exist _ n K) = Some e'.
Proof. intros.  (* idx_opt (Some (v, e')) [ | n] = Some e' *)
 unfold idx_opt.  unfold idx. unfold v_idx. simpl.
assert(H: (n=?n)%nat = true) by apply Nat.eqb_refl. rewrite H. reflexivity.
Qed.

(* access elements before the last: idx (v,e) i = idx v i for i<n. *)
Lemma idx_opt_before_last :
  forall (n : nat) (d : data) (v : exp (ary '{n} d)) 
     (e' : exp d) (i : nat) (Hi : i < n),
  @idx_opt (S n) d (Some (v, e')) (exist _ i (Nat.lt_lt_succ_r i n Hi)) = 
  @idx_opt n d (Some v) (exist _ i Hi).
Proof.
  intros n d v e' i Hi. (* Introduce variables *)
  (* idx_opt (Some (v, e')) [ | i] = idx_opt (Some v) [ | i] *)
  unfold idx_opt. (* Unfold idx_opt *)
  simpl. (* Simplify the match expression *)
  unfold idx_opt.  unfold idx. unfold v_idx. simpl.
  assert((i=?n)%nat = false) by (apply Nat.eqb_neq;lia).
  rewrite H. reflexivity. 
Qed.

Lemma fin_0_no_exists {d:data} : forall (f : fin 0 -> option (exp d)),
   ~ (exists i : fin 0, f i = None).  
Proof.  
  intros f H.  
  (* Destruct the existential hypothesis *)  
  destruct H as [i _].  
  (* This will fail because there are no elements of fin 0 *)  
  destruct i. lia.  
Qed.


(** mkoption **)

(** 
 * 判断数据类型d及其嵌套结构中是否包含长度为0的数组(ary) 
 * 如果包含，返回None；否则返回Some d
 * 用于在编译期检查数据类型的有效性
 *)
Fixpoint optdata (d : data) : option data :=
  match d with
  | num => Some d  (* 基础类型num总是有效 *)
  | ary n d' =>    (* 数组类型需要检查长度和元素类型 *)
    match (fle2nat n) with  (* 检查数组长度 *)
    | 0 => None    (* 长度为0的数组无效 *)
    | _ =>         (* 非零长度需要递归检查元素类型 *)
      match (optdata d') with
      | Some _ => Some d  (* 元素类型有效则整体有效 *)
      | None => None      (* 元素类型无效则整体无效 *)
      end
    end
  end.


(* 有效数据示例 *)
Example valid_data := ary (nat2fle 2 2) (ary (nat2fle 1 1) num).
Fact valid_data_some : 
  optdata valid_data = Some (ary (nat2fle 2 2) (ary (nat2fle 1 1) num)).
Proof. reflexivity. Qed.

(* 无效数据示例 *)
Example invalid_data := ary (nat2fle 0 0) num.
Fact invalid_data_none : optdata invalid_data = None.
Proof. reflexivity. Qed.

(**
 * 根据数据类型检查结果包装表达式
 * 如果数据类型有效(optdata返回Some)，则包装表达式
 * 否则返回None
 *)
Definition optexp {d : data} (e : exp d) : option (exp d) :=
  match (optdata d) with
  | Some _ => Some e  (* 类型有效则保留表达式 *)
  | None => None      (* 类型无效则丢弃 *)
  end.


(**
 * 将部分定义的数组(fin m -> option A)转换为完全定义的数组(option (vector A m))
 * 递归构造向量：
 * - 如果所有元素都是Some，则返回Some vector
 * - 如果任一元素是None，则返回None
 *)
Fixpoint mkoption {m} {A : Set} {struct m} : (fin m -> option A) -> option (vector A m) :=
  match m with
  | 0 => fun _ => Some (tt : vector A 0)  (* 空向量总是有效 *)
  | S m' => fun (u : fin (S m') -> option A) =>
    match u (nat2fin (Nat.lt_succ_diag_r m')) with  (* 检查最后一个元素 *)
    | Some e => 
      match mkoption (fun (i:fin m') => u (fin2finS i)) with  (* 递归检查前m'个元素 *)
      | Some e' => Some (e', e)  (* 构造向量 *)
      | None => None
      end
    | None => None
    end
  end.

(* two test examples for mkoption. *)
Example mkoption_some_ex : fin 3 -> option nat :=
  fun (i:fin 3) =>
    match proj1_sig i with
    | 0 => Some 10
    | 1 => Some 20
    | 2 => Some 30
    | _ => None
    end.

Fact mkoption_some_ex_ok : 
   mkoption mkoption_some_ex = Some [10, 20, 30]. auto. Qed. 

Definition mkoption_none_ex : fin 3 -> option nat :=
  fun (i:fin 3) =>
    match proj1_sig i with
    | 0 => Some 10
    | 1 => None
    | 2 => Some 30
    | _ => None
    end.

Definition from_option {A} (x0 : A) (o : option A) : A :=
  match o with
  | Some a => a
  | None => x0
  end.


Definition mkoptvec_helper {m d} (u : fin (S m) -> option (exp d))
  f : option (exp (ary '{S m} d)) :=
  match f (fun i => u (fin2finS i)), u (nat2fin (Nat.lt_succ_diag_r m)) with
  | Some e, Some e' => Some (e, e')
  | _, _ => None
  end.

Fixpoint mkoptvec4 {m d} : (fin m -> option (exp d)) -> option (exp (ary '{m} d)) :=
  match m with
  | 0 => fun _ => Some tt (* Return Some for the empty vector *)
  | S m' => fun u =>
      match mkoptvec4 (fun i => u (fin2finS i)), u (nat2fin (Nat.lt_succ_diag_r m')) with
      | Some v, Some e' => Some (v, e')
      | _, _ => None
      end
  end.

Definition m_reduce {d:data} {n:nat} (f:fin n ->  exp d -> exp d) 
  (a:exp d) : exp d := @i_reduce (exp d) n f a .

(* alternative definition of i_forall using n_forall. *)
Definition m_forall {n:nat} (f : fin n -> bool) : bool :=
    @i_forall n (finf2natf1 f true).

Definition opt_exp_beq {d : data} (x y : option (exp d)) : bool :=
  match x, y with
  | Some a, Some b => exp_beq a b
  | None, None => true
  | _, _ => false
  end.

(* return true if the function does not return None for i in [0..n-1]. *)
Definition validf {d:data} (n:nat) (f:fin n -> option (exp d)) : bool :=
   @i_forall n (fun (i:fin n) => negb (opt_exp_beq (f i) None)).

Lemma  negb_opt_exp_beq : forall {d:data} (a : option (exp d)),
 negb (opt_exp_beq a None) = true <-> a <> None.
Proof. intros a. split. 
- intros H.   unfold negb, opt_exp_beq in H.
  destruct a0.
  + intro H0. inversion H0.
  + inversion H.
- intro H. destruct a0.
  +  unfold negb, opt_exp_beq. reflexivity.
  + contradiction.
Qed.


Lemma mkoptvec4_None : forall d (u : fin 0 -> option (exp d)),
  mkoptvec4 u = Some tt.
Proof. intros. simpl. auto. Qed.

Lemma mkoptvec4_Some : forall {m d} (u : fin (S m) -> option (exp d)),
  @mkoptvec4 (S m) d u = @mkoptvec_helper m d u mkoptvec4.
Proof. intros. simpl. auto. Qed.

Lemma mkoptvec4_Some_direct : forall {m d} (u : fin (S m) -> option (exp d)),
  @mkoptvec4 (S m) d u = 
  match mkoptvec4 (fun (i:fin m) => 
         u (fin2finS i)), u (nat2fin (Nat.lt_succ_diag_r m)) with
  | Some e, Some e' => Some (e, e')
  | _, _ => None
  end.
Proof. intros. simpl. auto. Qed.

Lemma mkoptvec4_simplify :
  forall (n' : nat) (d : data) (f : fin (S n') -> option (exp d)),
    mkoptvec4 (fun i : fin (S n') => f i) =
    match mkoptvec4 (fun (i:fin n') => f FS[ i]), 
          f (exist _ n' (Nat.lt_succ_diag_r n')) with
    | Some v, Some e' => Some (v, e')
    | _, _ => None
    end.
Proof. intros. simpl. auto. Qed.

Lemma mkoptvec4_dependence : forall m d (u1 u2 : fin m -> option (exp d)),
  (forall i, u1 i = u2 i) -> mkoptvec4 u1 = mkoptvec4 u2.
Proof.
  induction m as [| m' IH]; intros d u1 u2 H.
  - (* Case m = 0 *)
    reflexivity. (* Both definitions return None *)
  - (* Case m = S m' *)
    simpl. 
    specialize( IH d  (fun i : fin m' => u1 FS[ i]) (fun i : fin m' => u2 FS[ i])). 
    rewrite IH. 
    rewrite H. reflexivity.
    intro. rewrite H. reflexivity.
Qed.

Definition mkoptvec {m d} : (fin m -> option (exp d)) -> 
  option (exp (ary '{m} d)) := mkoptvec4.


(*
Lemma mkoption_correct :
  forall (m : nat) (A : Set) (x0 : A) (f : fin m -> option A) (v : vector A m),
    mkoption f = Some v ->
    forall (i : fin m), v_nth x0 v (proj1_sig i) = from_option x0 (f i).
Proof.
  induction m as [|m IH]; intros A x0 f v Hmk.

  - (* Case m = 0 *)
    inversion_clear Hmk.
    destruct i as [n Hn].
    simpl in Hn.
    inversion Hn.  (* Only possible index is 0, but m = 0 ⇒ contradiction *)

  - (* Case m = S m' *)
    simpl in Hmk.
(*
f : fin (S m) -> option A
v : vector A (S m)
Hmk :
  match f (exist _ m (Nat.lt_succ_diag_r m)) with
  | Some e =>
      match mkoption (fun i : fin m => f (Fin.fin2finS i)) with
      | Some e' => Some (e', e)
      | None => None
      end
  | None => None
  end = Some v
______________________________________(1/1)
forall i : fin (S m),
v_nth x0 v (proj1_sig i) = from_option x0 (f i)
Hmk 是一个等式：某个嵌套 match 表达式等于 Some v
这个表达式是 mkoption 的定义展开后的形式：
先检查最后一个索引位置 f (exist _ m ...) 是否有值（即是否是 Some e）
然后递归调用 mkoption 检查前 m 个元素是否有值
如果都有值，则构造向量 (e', e)
我们的目标是证明：这个构造出来的向量 v 中的每个位置都对应 f 在该位置的值
*)
    destruct (f (exist _ m (Nat.lt_succ_diag_r m))) as [e|] eqn:Hlast; try discriminate.
(*
    destruct (mkoption (fun i : fin m' => f (fin2finS i))) as [e'|] eqn:Hrest; 
         injection Hmk; intros ->; clear Hmk.
*)
    + (* Recursive case: both parts are Some *)
     (* intros [i|n Hlt]. as [i Hi]. *) intro i.
        * (* i = m' → 最后一个元素 *)
          simpl. 
          rewrite Nat.eqb_refl.
          unfold from_option.
          rewrite Hlast.
          reflexivity.

        * (* i < m' → 前面的部分 *)
          simpl in Hi.
          apply Nat.eqb_neq.
          rewrite <- Hi.
          apply Nat.lt_0_succ.

          specialize (IH (fun i : fin m' => f (Fin.fin2finS i)) e' Hrest).

          rewrite IH.
          unfold from_option.
          rewrite Hrest0.
          reflexivity.

    + (* This case cannot happen due to pattern matching above *)
      congruence.
Qed.

Fact mkoption_none_ex_ok : 
   mkoption mkoption_none_ex = None. auto. Qed. 

Definition vector_of_list {A:Set} {n} (l : list A) : option (vector A n) :=
  if Nat.eqb (length l) n then Some (Vector.list_to_vector l) else None.
*)
(* the zero element in fin (S n). *)
Definition fin_zero {n:nat} : fin (S n) :=
  nat2fin (Nat.lt_0_succ n). (* 使用 0 < S n 的证明 *)

(* 构造单元素向量 *)
Definition mkvec1 {A: Set} (a : A) : vector A 1 :=
  (tt, a).

(* 递归构造向量 *)
Definition mkvecS {A:Set} {n} (a : A) (v : vector A n) : vector A (S n) :=  (v, a).

Fixpoint v_head {A:Set} {n : nat} : vector A (S n) -> A :=
  match n with
  | O => fun v => match v with (_, a) => a end
  | S m => fun v => match v with (v', _) => v_head v' end
  end.

Definition vec_map {A B : Set} {n : nat} (f : A -> B)
  (v : vector A (S n)) : vector B (S n) :=
  mk_vec (fun x => f (v_idx (@v_head A n v) v x)).

(** test mkoption **)
Example input1 : fin 3 -> option (exp num) :=
  fun i => Some (exp_default num). (* 所有元素为 Some 0 *)

(* Compute mkoption input1. *)
Fact test_input1_some : mkoption input1 = Some [REconst R0 "0", REconst R0 "0", REconst R0 "0"].
Proof. reflexivity. Qed.

Example input2 : fin 3 -> option (exp num) :=
  fun i => if (fin2nat i =? 1)%nat then None else Some (exp_default num). (* 第二个元素为 None *)

Fact test_input2_none : mkoption input2 = None. 
Proof. reflexivity. Qed.

Example input3 : fin 2 -> option nat :=
  fun i => Some (fin2nat i).

Fact test_input3_none : mkoption input3 = Some [0, 1]. 
Proof. reflexivity. Qed.

Example input4 : fin 2 -> option (exp num) :=
  fun i => if (fin2nat i =? 1)%nat then None else Some (exp_default num). (* 最后一个元素为 None *)

Fact test_input4_none : mkoption input4 = None. 
Proof. reflexivity. Qed.

(** 空向量构造的正确性 *)
Lemma mkoption_nil : 
  forall (A : Set), 
    mkoption (fun (_ : fin 0) => None) = Some (tt : vector A 0).
Proof. reflexivity. Qed.

(** 全定义向量的构造性 *)
Lemma mkoption_all_some :
  forall (A : Set) n (f : fin n -> A),
    mkoption (fun i => Some (f i)) = Some (mk_vec f).
Proof.
  induction n; simpl.
  - reflexivity.
  - intros. rewrite IHn. reflexivity.
Qed.

(** 存在None时返回None *)



Definition restrict {n A} (u : fin (S n) -> option A) : fin n -> option A :=
  fun (j : fin n) => u (fin2finS j).

(** 存在None时返回None的等价性证明 *)
Lemma mkoption_none_iff :
  forall (A : Set) n (u : fin n -> option A),
    mkoption u = None <-> exists i, u i = None.
Proof.
  split.
  - (* 方向1: mkoption返回None → 存在None元素 *)
    induction n; simpl; intros H.
    + (* 基本情况 n=0 *)
      discriminate H. (* fin 0无元素，不可能返回None *)
    + (* 归纳步骤 n=S n' *)
      destruct (u (nat2fin (Nat.lt_succ_diag_r n))) eqn:LastElem.
      * (* 最后一个元素为Some *)
        destruct (mkoption (fun i => u (fin2finS i))) eqn:Rec.
        -- discriminate H. (* 递归部分和最后元素均为Some，与H矛盾 *)
        -- apply IHn in Rec. destruct Rec as [i Hi].
           exists (fin2finS i). exact Hi.
      * (* 最后一个元素为None *)
        exists (nat2fin (Nat.lt_succ_diag_r n)). exact LastElem.
  
  - (* 方向2: 存在None元素 → mkoption返回None *)
    intros [i Hi]. induction n.
    + (* n=0时fin 0无元素，矛盾 *)
      inversion i. inversion H.
    + (* n=S n' *)
      destruct (fin_case i) as [j | ->].
      * (* i是前n'个元素之一 *)
        simpl. 
       (* 1. 解构存在性证明 *)
        destruct j as [j Hj]. (* Hj : i = FS[j] *)
        (* 2. 重写Hi *)
        rewrite Hj in Hi. (* Hi : u (FS[j]) = None *)
        (* 3. 定义辅助函数u' *)
        set (u' := fun i0 : fin n => u FS[i0]).
        (* 4. 证明u' j = None *)
        assert (Hj_none : u' j = None).
        { unfold u'. rewrite Hi. reflexivity. }
        (* 5. 应用归纳假设 *) 
        specialize (IHn u' j Hj_none). (* IHn : mkoption u' = None *)
        (* 6. 简化目标 *)
        rewrite IHn.
        (* 7. 处理match表达式 *)
        destruct (u (nat2fin (Nat.lt_succ_diag_r n))) as [e|];
        reflexivity.
      * (* i是最后一个元素 *)
        simpl. rewrite Hi. reflexivity.
Qed.


(* 构造向量 [..] 验证 v_head *)
Example vec1 : vector nat 1 := (tt, 42).
Fact vec1_ok : v_head vec1 = 42. auto. Qed.
Example vec2 : vector nat 2 := ((tt, 10), 20).
Fact vec2_ok : v_head vec2 = 10. auto. Qed.
Example vec3 : vector nat 3 := [ 1,2,3].
Fact vec3_ok : v_head vec3 = 1. auto. Qed.

Lemma v_head_base_case :
  forall (A : Set) (a : A),
    v_head (A := A) (n := 0) (tt, a) = a.
Proof.  intros A a. simpl. reflexivity. Qed.


(* 这个等式表示：将 `0` 作为 `fin (S n)` 的元素（使用 `nat2fin` 构造），然后通过
 `fin2finS` 提升到 `fin (S (S n))`，等价于直接将 `0` 作为 `fin (S (S n))` 的元素。 *)
Lemma fin2finS_nat2fin_0 :
  forall n, FS[ F[ Nat.lt_0_succ n]] = F[ Nat.lt_0_succ (S n)].
(*
    @eq (fin (S (S n)))
      (@fin2finS (S n) (@nat2fin (S n) 0 (Nat.lt_0_succ n)))
      (@nat2fin (S (S n)) 0 (Nat.lt_0_succ (S n))).
*)
Proof.
  intros n.  unfold fin2finS, nat2fin.
  (* 现在我们需要证明：
     exist _ 0 (Nat.lt_lt_succ_r _ _ (Nat.lt_0_succ n)) =
     exist _ 0 (Nat.lt_0_succ (S n)) *)
  apply exist_eq.
Qed.

Lemma v_head_mk_vec :
  forall (A : Set) (n : nat) (f : fin (S n) -> A),
    v_head (mk_vec f) = f fin_zero.
Proof.
  intros A n f.
  (* 需要 mk_vec 的定义和 fin0 的定义 *)
  unfold mk_vec, fin_zero.
  induction n as [|n IH].
  - (* 基础情况 n=0 *)
    simpl. f_equal. (* [ | 0] = F[ Nat.lt_0_succ 0] *)
    { apply fin_eq. simpl. (* 0=0 *) reflexivity. }
  - (* 归纳步骤 n=S n *)
    simpl.
    set (f' := fun i0 : fin (S n) => f FS[i0]).
    specialize(IH f'). unfold f' in IH.
    rewrite IH. f_equal.
    (* f FS[ F[ Nat.lt_0_succ n]] = f F[ Nat.lt_0_succ (S n)] *)
    apply fin2finS_nat2fin_0.
Qed.

Lemma v_head_independent_of_last :
  forall (A : Set) (n : nat) (v : vector A (S (S n))) (a : A),
    v_head v = @v_head A (S n) (fst v, a).
Proof.
  intros A n v a.
    destruct v as [v' a'].
    simpl. destruct v'. reflexivity.
Qed.

Lemma v_head_independent_of_last1 :
  forall (A : Set) (n : nat) (v : vector A (S 0)) (a : A),
    v_head v = snd v.
Proof.
  intros A n v a.
    simpl. destruct v. reflexivity.
Qed.


(** 递归构造的分解性质 *)
Lemma mkoption_unfold :
  forall (A : Set) n (u : fin (S n) -> option A),
    mkoption u =
    match u (nat2fin (Nat.lt_succ_diag_r n)), 
          mkoption (fun i => u (fin2finS i)) with
    | Some x, Some v => Some (v, x)
    | _, _ => None
    end.
Proof. reflexivity. Qed.

(** 验证引理的正确性 *)
Example test_mkoption_nil : 
  mkoption (fun (_ : fin 0) => None) = Some (tt : vector nat 0).
Proof. apply mkoption_nil. Qed.

Example test_mkoption_some : 
  mkoption (fun i : fin 2 => Some (fin2nat i)) = 
  Some (mk_vec (fun i => fin2nat i)).
Proof. apply mkoption_all_some. Qed.


