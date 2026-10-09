Require Import Logic.FunctionalExtensionality.
About v_idx_mk_vec.
Require Import List Reals String Nat Bool Arith Lra.
Require Export easy_logic finType vector DataExp.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Eqdep_dec.
Require Import Coq.Logic.Classical_Prop.
About v_idx_mk_vec.
Import ListNotations.

Set Implicit Arguments. 
Notation " '{ n } " := (fle_self n) (at level 2).


Fixpoint exp (d:data) : Set :=
  match d with
  | num => R
  | ary n d => vector (exp d) n
  end.

Fixpoint acc (d:data) : Set :=
  match d with
  | num => path 
  | ary n d => vector (acc d) n
  end.

(* boolean equality over R. *)
Definition R_beq (x y : R) : bool :=  
  match Req_dec_T x y with  
  | left _ => true  
  | right _ => false  
  end.

(* boolean value equality over exp. *)
Fixpoint exp_beq {d:data} : exp d -> exp d -> bool :=
  match d with
   | num => fun (a1 a2: exp num) => R_beq a1 a2
   | ary n d0 => fun (a1 a2: exp (ary n d0)) =>
       vector_eqb (@exp_beq d0) n a1 a2
  end.

(** properties of exp_beq. **)

Lemma exp_beq_num : forall (a1 a2: exp num), 
  exp_beq a1 a2 = R_beq a1 a2.
Proof. intros; reflexivity. Qed.

Lemma exp_beq_ary : forall {d:data} {m:nat} (n:fle m) 
  (a1 a2: exp (@ary m n d)),
  exp_beq a1 a2 = vector_eqb (@exp_beq d) n a1 a2.
Proof. intros; reflexivity. Qed.

(* Reflexivity *)  
Lemma exp_beq_refl :   
  forall (d : data) (x : exp d), exp_beq x x = true.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x.  
    unfold exp_beq, R_beq.  
    destruct (Req_dec_T x x) as [H | H].  
    + reflexivity.  
    + exfalso. apply H. reflexivity.  

  - (* Inductive case: ary *)  
    intros x.  rewrite exp_beq_ary.
    apply vector_eqb_refl.  apply IHIHd'.  
Qed.  

(* Symmetry *)  
Lemma exp_beq_sym :   
  forall (d : data) (x y : exp d), exp_beq x y = exp_beq y x.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x y.  
    unfold exp_beq, R_beq.  
    destruct (Req_dec_T x y) as [Hxy | Hxy];  
    destruct (Req_dec_T y x) as [Hyx | Hyx];  
    try reflexivity.  
    + rewrite Hxy in Hyx. contradiction.  
    + rewrite Hyx in Hxy. contradiction.  

  - (* Inductive case: ary *)  
    intros x y.  rewrite ?exp_beq_ary.
    apply vector_eqb_sym.  
    exact IHIHd'.  
Qed.  

(* Transitivity *)  
Lemma exp_beq_trans : forall (d : data) (x y z : exp d),   
  exp_beq x y = true -> exp_beq y z = true -> exp_beq x z = true.  
Proof.  
  intros d.  
  induction d as [| n d' IHd'].  
  - (* Base case: num *)  
    intros x y z Hxy Hyz.  
    unfold exp_beq, R_beq in *.  
    destruct (Req_dec_T x y) as [Hx_y | Hx_y];  
    destruct (Req_dec_T y z) as [Hy_z | Hy_z];  
    destruct (Req_dec_T x z) as [Hx_z | Hx_z];  
    try reflexivity.  
    + subst. contradiction.   
    + lia.
    + lia. 
    + lia. 

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
    unfold exp_beq, R_beq.   
    destruct (Req_dec_T x y) as [Hxy | Hxy].  
    + left.  reflexivity.  
    + right. reflexivity.  

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
 | num => R0
 | ary n d => mkvSeq (fun i:fin n => exp_default d)
 end.

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


(* ******************Basic Functional Primitive for data************************* *)

Definition zero 
  : exp num := R0.

Definition one 
  : exp num := R1.

Definition negate (x: exp num) 
  : exp num := Ropp x.

Definition add (x y: exp num)
  : exp num := Rplus x y.

Definition mul (x y: exp num)
  : exp num := Rmult x y.

Definition scal (r: R) (x: exp num)
  : exp num := Rmult r x.

Definition div (x y: exp num)
  : exp num := Rdiv x y.

Definition div_n(x: exp num) (n :nat) 
  : exp num := Rdiv x (INR n).

Definition sub (x y: exp num) 
  : exp num := Rminus x y.

(* x^n *)
Definition pow(x: exp num) (n :nat) 
  : exp num := powerRZ x (Z.of_nat n).

(* ln x *)
Definition log (x: exp num)
  : exp num := ln x.

(* x <= y *)
Definition leExp (x y : exp num) : bool :=
  if Rle_dec x y then true
  else false.

(* x > y *)
Definition gtExp (x y : exp num) : bool :=
  if Rgt_dec x y then true
  else false.

(* e^x *)
Definition pExp(x: exp num)
  : exp num := Reals.Rtrigo_def.exp x.

(* sqrt x *)
Definition make_nonnegreal (x : R) : nonnegreal :=
  match Rle_dec 0 x with
  | left proof => mknonnegreal x proof
  | right _ => mknonnegreal 0 (Rle_refl 0)
  end.

Definition sqrt (x:exp num) 
  : exp num := Rsqrt (make_nonnegreal x).

Definition reduce {n:nat} {s t:data}
  (f: exp s -> exp t -> exp t) (i:exp t) (v:exp (ary '{n} s)) 
  : exp t := v_reduce f i v .

Definition sum {n:nat} (e : exp (ary '{n} num))
  : exp num :=
  v_reduce add zero e.

Definition max {n:nat} (e : exp (ary '{n} num))
  : exp num :=
  v_max gtExp zero e.
(*
Definition max {n:nat} (e : exp (ary '{n} num))
  : exp num :=
  v_max gtExp e|[F[0]] e.
*)

Definition let_binding {s t} (e: exp s)(f:exp s -> exp t) :=
  f e.

Notation "'tlet' x ':=' e 'in' y" := (let_binding e (fun x => y))(at level 81).

(*
Definition join {t:data} {n m:nat} (e: exp (ary '{m} (ary '{n} t)))
  : exp (ary '{(m*n)} t) := mkvSeq (fun x : fin (m * n) =>
    e |[F[ x / n]] |[F[ x mod n]]).
*)
Definition join {t:data} {n m:nat} (e: exp (ary '{m} (ary '{n} t)))
  : exp (ary '{(m*n)} t) := mkvSeq (fun x : fin (m * n) =>
    let '(i, j) := idx_1d_to_2d x in  (* 将一维索引 x 转换为二维索引 (i, j) *)
      e |[ i] |[ j]         (* 从嵌套向量中提取元素 *)
  ).
(*
Definition split {t:data} {n m:nat} (e:exp (ary '{(m*n)} t))
  :(exp (ary '{m} (ary '{n} t))) := mkvSeq(fun i : fin m =>
   mkvSeq (fun j : fin n => e |[F[ i * n + j]])).
*)
Definition split {t:data} {n m:nat} (e:exp (ary '{(m*n)} t))
  :(exp (ary '{m} (ary '{n} t))) := mkvSeq(fun i : fin m =>
   mkvSeq (fun j : fin n => e |[idx_2d_to_1d i j])).
(*
Definition concat {d m n} (e1: exp (ary '{m} d)) (e2: exp (ary '{n} d))
  : exp (ary '{(m+n)} d) := mkvSeq (fun i : fin (m + n) =>
   if i <? m then e1 |[F[ i]] else e2 |[F[ i - m]]).
*)
Definition concat {d m n} (e1: exp (ary '{m} d)) (e2: exp (ary '{n} d))
  : exp (ary '{(m+n)} d) := mkvSeq (fun i : fin (m + n) =>
    let val := fin2nat i in  
    match Nat.ltb_spec0 val m with (* if val < m *)
    | ReflectT _ H_lt => e1 |[ nat2fin H_lt ]
    | ReflectF _ H_ge =>  
        (* Use offset_proof_concise to directly prove val - m < n *)
        let H_lt_sub := @offset_proof_concise val m n (fin_proof i) H_ge in
          e2 |[ nat2fin H_lt_sub ]
    end
  ).
(*
Definition padl {d n} (k : nat) (e: exp (ary '{n} d))
  : exp (ary '{(k+n)} d) := mkvSeq (fun i : fin (k + n) =>
   if i <? k then (exp_default d) else e|[F[ i - k]]).
*)
Definition padl {d n} (k : nat) (e: exp (ary '{n} d))
  : exp (ary '{(k+n)} d) := mkvSeq (fun i : fin (k + n) =>
    let val := fin2nat i in
    match Nat.ltb_spec0 val k with (* if val < k *)
    | ReflectT _ H_lt => (exp_default d)
    | ReflectF _ H_ge =>
        (* Use offset_proof_concise to directly prove val - k < n *)
        let H_lt_sub := @offset_proof_concise val k n (fin_proof i) H_ge in
          e |[ nat2fin H_lt_sub ]
    end
  ).
(*  
Definition padr {d n} (k : nat) (e: exp (ary '{n} d))
  : exp (ary '{(n+k)} d) := mkvSeq (fun i : fin (n + k) =>
   if i <? n then e|[F[ i]] else (exp_default d)).
*)
Definition padr {d n} (k : nat) (e: exp (ary '{n} d))
  : exp (ary '{(n+k)} d) := mkvSeq (fun i : fin (n + k) =>
    let val := fin2nat i in
    match Nat.ltb_spec0 val n with (* if val < n *)
    | ReflectT _ H_lt => e |[ nat2fin H_lt ]
    | ReflectF _ H_ge => (exp_default d)
    end
  ).

Definition ary_idx_sub {d:data} {n:nat} (k:fin n) (i:fin k) : fin n :=
  let H_lt : i<n := 
     Nat.lt_trans (fin2nat i) k n (fin_proof i) (fin_proof k)
  in nat2fin H_lt .
(*
Definition truncl {d n} (k : fin n) (e: exp (ary '{n} d)) 
  : exp (ary '{k} d) := 
   mkvSeq (fun i : fin k => e|[F[ i]]).
*)
Definition truncl {d n} (k : fin n) (e: exp (ary '{n} d)) 
  : exp (ary '{k} d) := 
   mkvSeq (fun i : fin k => e |[ @ary_idx_sub d n k i]).

Lemma offset_add_le {n k : nat} (H_lt : k < n) : k + (n-k) <= n.
Proof. rewrite Nat.add_comm. lia. Qed.

(* return i+(n-k) and its proof that i+(n-k) < n. *)
Definition idx_sub_offset {n : nat} (k : fin n) (i : fin k) : fin n :=
  let offset : nat := n - k in
  let H : k + offset <= n := offset_add_le (fin_proof k) in
  let val := i + offset in
  let H1 : val < k + offset := 
    proj1 (Nat.add_lt_mono_r i k offset) (fin_proof i) in
  let H_lt_n : i+(n-k) < n := Nat.lt_le_trans val (k+offset) n H1 H in
    nat2fin H_lt_n. 

(* 从一个长度为 n 的向量 v 中截取最后 k 个元素，生成一个新的长度为 k 的向量 *)
Definition truncr {d n} (k : fin n) (e: exp (ary '{n} d))
  : exp (ary '{k} d) :=  mkvSeq (fun i : fin k => 
   let idx : fin n := idx_sub_offset k i in (* i+n-k *)
     e|[ idx]).
(*
Definition truncr {d n} (k : fin n) (e: exp (ary '{n} d))
  : exp (ary '{k} d) := 
    mkvSeq (fun i : fin k => e|[F[ i + n - k]]).
*)

(* Swaps rows and columns of a 2D array. *)
Definition trans {d m n} (e: exp (ary '{m} (ary '{n} d)))
  : exp (ary '{n} (ary '{m} d)) := 
    mkvSeq (fun i:fin n => mkvSeq (fun j:fin m => e|[j] |[i])).

(* convert the type of an array to a type of the same length. *)
Definition size {d m n} (k: m = n) (e: exp (ary '{m} d))
  : exp (ary '{n} d) := 
   mkvSeq (fun i:fin n => 
    let pf : fin m := eq_rect n fin i m (eq_sym k) in e|[pf]).
(*
Definition size {d m n} (k: m = n) (e: exp (ary '{m} d))
  : exp (ary '{n} d) := mkvSeq (fun i:fin n => e|[F[i]]).
*)

(* 环境的定义，用于后续定义comm的语义。更改env的定义：path -> option (exp num), 用于处理remove的情况
   其中env的定义方式有两种，一种是基于映射函数实现，另一种是基于对偶的列表实现，这里选择第一种 *)

(* ****************** Environment ****************** *)

Definition env := path -> option (exp num). 

Definition env_empty : env :=
   fun _ => None.

Definition update (m : env) (x : path)(v : exp num) :=
  fun x' => if (path_eqb x x') then Some v else m x'.

Notation "'_' '!->' v" := (env_empty v)
  (at level 100, right associativity).

Notation "x '!->' v ';' m" := (update m x v)
  (at level 100, v at next level, right associativity).


(* (* 环境变量删除函数 *)
Parameter remove: path -> env -> env. *)

(* 环境变量删除函数的语义实现通过同变量更新函数相关的公理实现 *)
(* Lemma remove_update: forall (x:path) (e:exp num) (m:env),
  remove x (update m x e) = envGet m.
Proof. intros. unfold update,remove,envGet,get. fun_ext. 
  induction x. 
Admitted.    *)

Definition remove(m: env) (x: path) : env :=
  fun x' => if path_eqb x x' then None else m x'.

Definition Undefined (x : path) (rho:env) : Prop :=
  rho x = None.

Theorem update_eq : forall (m : env) x v,
  (x !-> v ; m) x = Some v.
Proof.
  unfold update. intros. rewrite path_eqb_refl;auto.
Qed.

Theorem update_neq : forall (m : env) x1 x2 v,
  x1 <> x2 ->
  (x1 !-> v ; m) x2 = m x2.
Proof.
  intros. unfold update. apply path_eqb_neq in H.
  rewrite H. auto.
Qed.

Lemma update_shadow : forall (m : env) x v1 v2,
  (x !-> v2 ; x !-> v1 ; m) = (x !-> v2 ; m).
Proof.
  intros. unfold update. fun_ext. destruct (x=?x0).
  auto. auto.
Qed.

Theorem update_permute : forall (m : env) v1 v2 x1 x2,
  x2 <> x1 ->
  (x1 !-> v1 ; x2 !-> v2 ; m) = (x2 !-> v2 ; x1 !-> v1 ; m).
Proof.
  intros. unfold update. fun_ext. destruct (x1=?x) eqn:E.
  apply path_eqb_eq in E. subst. apply path_eqb_neq in H.
  rewrite H. auto. auto.
Qed.

Lemma remove_update: forall (x:path) (e:exp num) (m:env),
  Undefined x m  ->
  remove (update m x e) x = m.
Proof. 
  intros. unfold remove, update. unfold Undefined in H. 
  fun_ext. destruct (x =? x0) eqn:H1. rewrite <- H.
  apply path_eqb_eq in H1. subst. auto. auto.
Qed.

Lemma remove_commute : forall x y m,
  x <> y -> remove (remove m y) x = remove (remove m x) y.
Proof.
  intros. unfold remove. apply functional_extensionality. intro z.
  destruct (path_eqb x z) eqn:Exz;
  destruct (path_eqb y z) eqn:Eyz.
  - apply path_eqb_eq in Exz. apply path_eqb_eq in Eyz. subst. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma remove_update_commute : forall x y m e,
  x <> y -> remove (update m y e) x = update (remove m x) y e.
Proof.
  intros. unfold remove, update. apply functional_extensionality. intro z.
  destruct (path_eqb x z) eqn:Exz;
  destruct (path_eqb y z) eqn:Eyz.
  - apply path_eqb_eq in Exz. apply path_eqb_eq in Eyz. subst. contradiction.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma remove_update_same : forall x m e,
  remove (update m x e) x = remove m x.
Proof.
  intros. unfold remove, update. apply functional_extensionality. intro z.
  destruct (path_eqb x z) eqn:Exz.
  - reflexivity.
  - reflexivity.
Qed.

(* 命令的定义，对于后续翻译器A、翻译器C及其重写规则的定义至关重要
   原来代码生成过程中只定义了comm的类型，在这里定义出每个comm的语义，便于后续对重写规则进行证明 *)

(* ****************** Command ****************** *)

Definition comm:= env -> env.

Definition skip :comm:= fun (rho:env) => rho.

Definition If (b:bool)(p1 p2:comm) : comm := 
  fun (rho:env) => if b then p1 rho else p2 rho.

Definition seq (p1 p2:comm):comm:= 
  fun (rho:env) => p2 (p1 rho).

Notation " p1 '; p2 " := (seq p1 p2) (right associativity,at level 65).

Notation "FS[ i ]" := (fin2finS i).

Notation "'[ i ]" := (ltS i).

Fixpoint seqfor {m:nat} : (fin m -> comm) -> comm :=
  match m with
  | O => fun (_ :_ )=> skip
  | S m' => fun (p: fin (S m') -> comm) =>
     seqfor (fun i => p FS[i]) '; p '[m']
  end.

Fixpoint parfor {d:data}{m:nat}: acc (ary '{m} d) ->(fin m -> acc d -> comm) -> comm :=
  match m with
  | O => fun _ _ => skip
  | S m' => fun v (p: fin (S m') -> acc d -> comm )
         => parfor (fst v) (fun i => p FS[i])  ';
            p '[m'] (snd v)
  end.

Fixpoint assign {d:data} : acc d -> exp d -> comm :=
  match d with
  | num => fun (a:acc num) (e: exp num) (rho:env) => 
      update rho a e
  | @ary n m d1 => fun (a:acc(@ary n m d1)) (e: exp (@ary n m d1)) =>
    seqfor (fun i =>(assign a|{i} e|[i]) )
end.

Notation " a |:= e " := (assign a e) (at level 60).

(* new *)

 (* 针对不同数据类型整体释放空间 *)
(* Parameter vrm: forall {d:data}, acc d -> env -> env. *)

Fixpoint for_rev {n:nat} :(fin n -> comm)-> comm:=
  match n with
  | O => fun (p: fin O -> comm) => fun rho => rho
  | S n' => fun (p: fin (S n') -> comm)
      => p '[n'] '; for_rev (fun i => p FS[i]) 
  end.

(* If a command c commutes with every p i, then c commutes with seqfor p *)
Lemma seqfor_commute : forall n (p : fin n -> comm) (c : comm),
  (forall i rho, c (p i rho) = p i (c rho)) ->
  forall rho, c (seqfor p rho) = seqfor p (c rho).
Proof.
  induction n; intros p c Hcomm rho.
  - simpl. auto.
  - change (seqfor p) with (seqfor (fun i => p FS[i]) '; p '[n]).
    unfold seq.
    rewrite Hcomm.
    rewrite IHn; auto.
Qed.

(* If all operations pairwise commute, forward and reverse iteration are equivalent.
   This theorem explains why for_rev was chosen: for_rev and seqfor are
   provably equivalent under commutation, preserving the design flexibility. *)
Lemma seqfor_for_rev_equiv : forall n (p : fin n -> comm),
  (forall i j rho, i <> j -> p i (p j rho) = p j (p i rho)) ->
  forall rho, seqfor p rho = for_rev p rho.
Proof.
  induction n; intros p Hcomm rho.
  - simpl. auto.
  - change (seqfor p) with (seqfor (fun i => p FS[i]) '; p '[n]).
    change (for_rev p) with (p '[n] '; for_rev (fun i => p FS[i])).
    unfold seq.
    set (p' := fun i : fin n => p FS[i]).
    assert (Hcomm' : forall i j rho, i <> j -> p' i (p' j rho) = p' j (p' i rho)).
    { intros i j eta0 Hneq. unfold p'. apply Hcomm.
      intro H. apply Hneq. apply fin_eq.
      assert (H1 : @fin2nat (S n) (FS[i]) = @fin2nat (S n) (FS[j])).
      { rewrite H. reflexivity. }
      unfold fin2finS in H1. rewrite !fin2nat_exist in H1. auto. }
    assert (Hlast : forall eta0, p '[n] (seqfor p' eta0) = seqfor p' (p '[n] eta0)).
    { apply seqfor_commute. intros i eta0. apply Hcomm.
      intro H. assert (False).
      { assert (H1 : @fin2nat (S n) '[n] = @fin2nat (S n) (FS[i])).
        { rewrite H. reflexivity. }
        unfold fin2finS, ltS in H1. rewrite !fin2nat_exist in H1.
        pose proof (fin_correct i) as Hi. lia. }
      contradiction. }
    rewrite Hlast.
    apply IHn. apply Hcomm'.
Qed.

(* If two seqfor's operations pairwise commute and locally cancel,
   then their composition is the identity. *)
Lemma seqfor_seqfor_cancel : forall n (p q : fin n -> comm),
  (forall i j rho, i <> j -> p i (q j rho) = q j (p i rho)) ->
  (forall i rho, p i (q i rho) = rho) ->
  forall rho, seqfor p (seqfor q rho) = rho.
Proof.
  induction n; intros p q Hcomm Hcancel rho.
  - simpl. auto.
  - change (seqfor p) with (seqfor (fun i => p FS[i]) '; p '[n]).
    change (seqfor q) with (seqfor (fun i => q FS[i]) '; q '[n]).
    unfold seq.
    set (p' := fun i : fin n => p FS[i]).
    set (q' := fun i : fin n => q FS[i]).
    assert (Hcomm' : forall i j rho, i <> j -> p' i (q' j rho) = q' j (p' i rho)).
    { intros i j eta0 Hneq. unfold p', q'. apply Hcomm.
      intro H. apply Hneq. apply fin_eq.
      assert (H1 : @fin2nat (S n) (FS[i]) = @fin2nat (S n) (FS[j])).
      { rewrite H. reflexivity. }
      unfold fin2finS in H1. rewrite !fin2nat_exist in H1. auto. }
    assert (Hcancel' : forall i rho, p' i (q' i rho) = rho).
    { intros i eta0. unfold p', q'. apply Hcancel. }
    assert (Hcomm_q_last : forall eta0, q '[n] (seqfor p' eta0) = seqfor p' (q '[n] eta0)).
    { apply seqfor_commute. intros i eta0. symmetry. apply Hcomm.
      intro H. assert (False).
      { assert (H1 : @fin2nat (S n) '[n] = @fin2nat (S n) (FS[i])).
        { rewrite H. reflexivity. }
        unfold fin2finS, ltS in H1. rewrite !fin2nat_exist in H1.
        pose proof (fin_correct i) as Hi. lia. }
      contradiction. }
    rewrite <- Hcomm_q_last.
    assert (Hcancel_last : forall eta0, p '[n] (q '[n] eta0) = eta0).
    { intros eta0. apply Hcancel. }
    rewrite Hcancel_last.
    apply IHn; auto.
Qed.

(* seqfor with constant skip is skip. *)
Lemma seqfor_skip : forall n,
  seqfor (fun _ : fin n => skip) = skip.
Proof.
  induction n.
  - reflexivity.
  - cbn [seqfor]. unfold seq. rewrite IHn. reflexivity.
Qed.

Fixpoint vrm {d:data} : acc d -> comm :=
  match d with
  | num => fun(a:acc num) (rho:env) =>
      remove rho a
  | @ary n m d1 => fun (a:acc(@ary n m d1)) => 
    seqfor (fun i  => (vrm a|{i}) )
  end.

(*
(* vrm与assign满足以下条件 *)
Axiom vrm_assign: forall d (a:acc d) (e:exp d) rho,
  vrm a ((a |:= e) rho) = rho. *)

(* DPIA-style [new]: the temporary path is supplied by the caller and the
   body is executed in-place.  No automatic cleanup is performed, which keeps
   Leibniz rewrite rules for reductions simple (cf. Zonia/Progress/operation.v). *)
Definition new {d:data} (p: acc d -> comm) (a: acc d): comm := 
  p a.


(*
Fixpoint v_nth {n : nat} (x0 : A) : (vector n) -> nat -> A 
  := match n with
  | O => fun (_ : vector O) (_ : nat) => x0
  | S n' => fun (v : vector (S n')) (i : nat) => 
     if i =? n' then snd v else v_nth x0 (fst v) i
  end.
Definition v_idx {n: nat} (x0 : A) : (vector n) -> fin n -> A :=
  fun v i => v_nth x0 v i.
Definition idx {n:nat} {t:data} (v:exp (ary '{n} t)) (i: fin n) 
  : exp t := v_idx (exp_default t) v i.

Notation " a |[ i ] " := (idx a i) (at level 2).
*)

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


(* (option (vector m), option b) 不能映射为option (vector(S m))  *)
Fixpoint mkoptvec1 {m d} : (fin m -> (option (exp d))) -> option (exp (ary '{m} d)):=
  match m with
  | 0 => fun ( _:_ ) => Some tt
  | S m' => fun ( u: fin (S m') -> option (exp d))  =>
    (* check if the last element of the array is none or some element *)
          match mkoptvec1 (fun (i:fin m') => u (fin2finS i)) with
          | Some e =>  
             match u (nat2fin (Nat.lt_succ_diag_r m':m'<S m')) with
               Some e' => Some (e,e') 
             | None => None
             end        
          | None   => None
          end
end.


(**
 Old version of mkoptvec1 where m=0 returns None.
 This was proven to always return None, which is why we changed the design.
 *)
(*
Fixpoint mkoptvec1 {m d} : (fin m -> (option (exp d))) -> option (exp (ary '{m} d)):=
  match m with
  | 0 => fun ( _:_ ) => None
  | S m' => fun ( u: fin (S m') -> option (exp d))  =>
          match mkoptvec1 (fun (i:fin m') => u (fin2finS i)) with
          | Some e =>  
             match u (nat2fin (Nat.lt_succ_diag_r m':m'<S m')) with
               Some e' => Some (e,e') 
             | None => None
             end        
          | None   => None
          end
end.
*)
Fixpoint mkoptvec2 {m d} : (fin m -> option (exp d)) -> option (exp (ary '{m} d)) :=
  match m with
  | 0 => fun _ => None
  | S m' => fun u =>
      match mkoptvec2 (fun i => u (fin2finS i)), 
                                u (nat2fin (Nat.lt_succ_diag_r m')) with
      | Some e, Some e' => Some (e, e')
      | _, _ => None
      end
  end.

Fixpoint mkoptvec3 {m d} : (fin m -> option (exp d)) -> option (exp (ary '{m} d)) :=
  match m with
  | 0 => fun _ => None
  | S m' => fun u =>
      let rec_result := mkoptvec3 (fun i => u (fin2finS i)) in
      match rec_result, u (nat2fin (Nat.lt_succ_diag_r m')) with
      | Some e, Some e' => Some (e, e')
      | _, _ => None
      end
  end.

(*
Fixpoint mkoptvec4 {m d} : (fin m -> option (exp d)) -> option (exp (ary '{m} d)) :=
  match m with
  | 0 => fun _ => None
  | S m' => fun u => mkoptvec_helper u mkoptvec4
  end.
*)
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

Fixpoint mkoptvec5 {m d} : (fin m -> option (exp d)) -> option (exp (ary '{m} d)) :=
  match m with
  | 0    => fun _ => Some tt (* Return Some for the empty vector *)
  | S m' => fun u => mkoptvec_helper u mkoptvec5
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

Lemma validf_ok {d:data} (n:nat) (f:fin n -> option (exp d)) : 
    validf f = true <-> forall (i:fin n), f i <> None.
Proof. split. 
+ (* -> *) intros H i. unfold validf in H.
 rewrite<- i_forall_correct in H.
 specialize(H i). rewrite negb_opt_exp_beq in H. exact H.
+ (* <- *) intro H. unfold validf.  rewrite<- i_forall_correct.
   intro i. rewrite negb_opt_exp_beq. apply H.
Qed.

(* left subvector of mkoptvec f. *)
(*
Lemma mkoptvec4_S : forall {m d} (u : fin (S m) -> option (exp d)) (i:fin m),
  idx_opt (@mkoptvec4 (S m) d u) FS[i] = u FS[i].
Proof. intros. simpl.  unfold idx_opt. simpl. auto.  
Qed.
*)

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

Lemma mkoptvec4_equiv : forall m d (u : fin m -> option (exp d)),
  mkoptvec4 u = mkoptvec1 u.
Proof.
  induction m as [| m' IH]; intros d u.
  - (* Case m = 0 *)
    reflexivity. (* Both definitions return None *)
  - (* Case m = S m' *)
    simpl.
    unfold mkoptvec_helper.
    destruct (mkoptvec1 (fun i => u (fin2finS i))) as [e|] eqn:Hrec.
    + (* Subcase: recursive call returns Some e *)
      destruct (u (nat2fin (Nat.lt_succ_diag_r m'))) as [e'|] eqn:Hlast.
      * (* Subsubcase: last element is Some e' *)
        rewrite IH. rewrite Hrec. (* Apply induction hypothesis *)
        reflexivity.
      * (* Subsubcase: last element is None *)
        rewrite IH. rewrite Hrec. (* Apply induction hypothesis *)
        reflexivity.
    + (* Subcase: recursive call returns None *)
      rewrite IH. rewrite Hrec. (* Apply induction hypothesis *)
      reflexivity.
Qed.

Lemma mkoptvec4_dependence : forall m d (u1 u2 : fin m -> option (exp d)),
  (forall i, u1 i = u2 i) -> mkoptvec4 u1 = mkoptvec4 u2.
Proof.
  induction m as [| m' IH]; intros d u1 u2 H.
  - (* Case m = 0 *)
    reflexivity. (* Both definitions return None *)
  - (* Case m = S m' *)
    simpl. unfold mkoptvec_helper.
    specialize( IH d  (fun i : fin m' => u1 FS[ i]) (fun i : fin m' => u2 FS[ i])). 
    rewrite IH. 
    rewrite H. reflexivity.
    intro. rewrite H. reflexivity.
Qed.

Definition mkoptvec {m d} : (fin m -> option (exp d)) -> 
  option (exp (ary '{m} d)) := mkoptvec4.

Lemma nat_lt_neq : forall x m : nat, x < m -> (x =? m)%nat = false.
Proof.
  intros x m H.                  (* Introduce the hypothesis x < m *)
  apply Nat.eqb_neq.           (* Rewrite (x =? m) as negb (x =? m) = false *)
  apply Nat.lt_neq.
  exact H.
Qed.

(* v_idx (v,e) i = v_idx v i for i:fin n *)
Lemma v_idx_Sn {d:data} {x0:exp d} :
  forall (n:nat) (v : vector (exp d) n) (e : exp d) (i : fin n),
  @v_idx _ (S n) x0 (v, e) FS[i] = v_idx x0 v i.
Proof.
  intros n v e i.
  unfold v_idx.
  destruct i. simpl. 
  assert((x=?n)%nat = false). { apply nat_lt_neq; exact l. }
  rewrite H. reflexivity.
Qed.

(* return the head sub vector of a vector of size > 0. *)
Definition v_hd {m:nat} {d:data} (e:option (exp (ary '{ (S m)} d)))
  : option (exp (ary '{ m} d)) := 
  match e with
   | Some (v1,v2) => Some v1
   | None => None
  end. 

(* idx_opt_ary_equiv  *)
Lemma v_hd_correct {m:nat} {d:data}: 
  forall (e:option (exp (ary '{ (S m)} d))) (i:fin m),
  idx_opt e FS[i] = idx_opt (v_hd e) i.
Proof. intros. unfold v_hd. unfold fin2finS. destruct e.
+ simpl. unfold idx_opt. simpl. unfold idx. destruct e.
(* Some (v_idx (exp_default d) (v, e) [ | i]) = Some (v_idx (exp_default d) v i) *)
  f_equal. apply v_idx_Sn.
+ reflexivity. 
Qed.

Lemma idx_opt_Some_idx : forall {n : nat} {t : data} 
  (v : exp (ary '{n} t)) (i : fin n),
  idx_opt (Some v) i = Some (idx v i).
Proof. intros. unfold idx_opt. reflexivity. Qed.

Lemma idx_opt_Sn {d : data} :
  forall (n : nat) (v : exp (ary '{n} d)) (e:exp d) (i : fin n),
  @idx_opt (S n) d (Some (v,e))  FS[i] = idx_opt (Some v) i.
Proof.
  intros n v e i. rewrite ?idx_opt_Some_idx. 
  rewrite (@idx_opt_Some_idx (S n)). f_equal. 
  apply v_idx_Sn.
Qed.

(* extend f: fin i -> A to a function on fin (S i) -> A. *)
Definition restrictf {d:data} (m:nat) (f : fin (S m) -> option (exp d))
  : (fin m -> option (exp d)) := fun (i : fin m) => f FS[i].

Lemma restrictf_ok {d:data} (m:nat) (f : fin (S m) -> option (exp d)):
  forall (i:fin m), restrictf f i = f FS[i].
Proof. intros. unfold restrictf. reflexivity. Qed.

Lemma mkoptvec4_but_last :
  forall (n : nat) (d : data) (f : fin (S (S n)) -> option (exp d)),
    (forall (i:fin (S (S n))), f i <> None) ->
    mkoptvec4 (fun i : fin (S n) => f FS[ i]) = v_hd (mkoptvec4 f).
Proof.
  intros n d f H. unfold v_hd. simpl. 
  destruct(mkoptvec4 (fun i : fin n => f FS[ FS[ i]]) ); 
  try(reflexivity).
 
  destruct(f FS[ F[ Nat.lt_succ_diag_r n]] ); try(reflexivity).
  specialize(H F[ Nat.lt_succ_diag_r (S n)]).
  destruct(f F[ Nat.lt_succ_diag_r (S n)] ); try(reflexivity).
+ contradiction. 
Qed.

Lemma validf_true_mkoptvec {d : data} :
  forall (n : nat) (f : fin n -> option (exp d)),
    validf f = true -> (mkoptvec f) <> None.
Proof. unfold mkoptvec. intros. 
 rewrite validf_ok in H. induction n.
+ unfold mkoptvec4. intro H0. inversion H0.
+ specialize (IHn (restrictf f)). unfold restrictf in IHn.
  assert(H0 : forall i : fin n, f FS[ i] <> None) . {
   intro i. apply H. }
  specialize (IHn H0).
  rewrite mkoptvec4_simplify. (* avoid unfold mkoptvec4 which is too complicated. *)
  destruct(mkoptvec4 (fun i : fin n => f FS[ i]) ).
  -   
    specialize(H (nat2fin (Nat.lt_succ_diag_r n))).
    unfold nat2fin in H.
    destruct(f [ | n]).
    * intro H1. discriminate H1.
    * contradiction H. auto. 
  - contradiction IHn. auto.
Qed.

Require Import Coq.Program.Equality.


Lemma mkoptvec_validf_true {d : data} :
  forall (n : nat) (f : fin n -> option (exp d)),
     (mkoptvec f) <> None -> validf f = true.
Proof. unfold mkoptvec. intros. 
 rewrite validf_ok. intro i.
 induction n.
+ destruct i.  lia.
+ specialize (IHn (restrictf f)). unfold restrictf in IHn.
  rewrite mkoptvec4_simplify in H.
  destruct i.
  assert(Hl : x <= n). lia.
(* case analysis on x<n and x=n *)
  destruct( proj1 (Nat.lt_eq_cases x n) Hl) as [H_lt | H_eq].
  - (* H_lt : x < n *)
    destruct(mkoptvec4 (fun i : fin n => f FS[ i])) .
    * (* Some *)
      assert(Some e <> None ). { intro Hsn; inversion Hsn. }
      specialize (IHn H0 ) .
      specialize(IHn (nat2fin H_lt)). 
      unfold fin2finS in IHn. simpl in IHn.
      assert(H2 : l = (Nat.lt_lt_succ_r x n H_lt)).
      apply proof_irrelevance. rewrite H2. exact IHn.
     * (* None *) contradiction H. auto.
  - (* H_eq *)
    subst x.       
    destruct(mkoptvec4 (fun i : fin n => f FS[ i])) .
    * (* Some *)
      assert(l = (Nat.lt_succ_diag_r n)) by
         apply proof_irrelevance.
      rewrite H0.
      destruct (f [|n]) as [e' |] eqn:Hf.
      ** (* Some *) apply some_neq_none.
      ** (* H: None <> None *) contradiction H. auto.
    * (* H: None <> None *) contradiction H. auto. 
Qed.

Theorem mkoptvec_iff_validf {d : data} :
  forall (n : nat) (f : fin n -> option (exp d)),
    (mkoptvec f) <> None <-> validf f = true.
Proof. split. 
+ apply mkoptvec_validf_true.
+ apply validf_true_mkoptvec. 
Qed.

Theorem mkoptvec_iff_all_fi {d : data} :
  forall (n : nat) (f : fin n -> option (exp d)),
    (mkoptvec f) <> None <-> (forall i : fin n, f i <> None).
Proof. intros.
 rewrite mkoptvec_iff_validf. apply validf_ok. 
Qed.



Corollary mkoptvec_none_iff_exist_none {d : data} :
  forall (n : nat) (f : fin n -> option (exp d)),
    (mkoptvec f) = None <-> (exists i : fin n, f i = None).
Proof. intros. rewrite negation_equivalence. 
rewrite mkoptvec_iff_all_fi. rewrite all_ex_not.
split.
+ intro. intro. destruct H0.
  rewrite double_negation_iff in H0.
  destruct H. exists x. exact H0.
+ apply contrapositive. intro H. destruct H. exists x. 
  rewrite double_negation_iff. exact H.
Qed.


Corollary mkoptvec_none_validf_false {d : data} :
  forall (n : nat) (f : fin n -> option (exp d)),
    (mkoptvec f) = None <-> validf f = false.
Proof.  
intros n f. rewrite negation_equivalence.
rewrite mkoptvec_iff_validf.
rewrite true_iff_not_false.
reflexivity.
Qed.

Lemma mkoptvec_last {d : data} :
  forall (n : nat) (f : fin (S n) -> option (exp d)) (e : exp d),
    validf f = true -> (f (fin_last n) = Some e) ->
    idx_opt (mkoptvec f) (fin_last n) = f (fin_last n).
Proof.
  intros n f e Hvalid Hlast.
  induction n as [| n' IH].
  - (* Base case: n = 0 *)
    simpl in *.
    destruct (f (fin_last 0)) eqn:H; [| discriminate].
    inversion Hlast; subst.
    unfold fin_last in H. rewrite H. simpl. f_equal.

  - (* Inductive case: n = S n' *)
    rewrite validf_ok in Hvalid. 
    rewrite Hlast. unfold mkoptvec.
    rewrite<- Hlast. unfold fin_last.
    simpl. unfold idx_opt. 
      unfold fin_last in * |- *.          
    unfold mkoptvec in  IH.
    assert(Hm : mkoptvec4 (fun i : fin n' => f FS[ FS[ i]]) <> None).
    { rewrite mkoptvec_iff_all_fi. (* key lemma *)
      assert(Hf : forall i : fin n', f FS[ FS[ i]] <> None).
      intro i. apply Hvalid.  exact Hf.
    } 
    destruct(mkoptvec4 (fun i : fin n' => f FS[ FS[ i]]) ). 
    +  rewrite Hlast. f_equal. unfold nat2fin.
       unfold idx, v_idx in IH .
       specialize(Hvalid FS[ nat2fin (Nat.lt_succ_diag_r n')]).
       unfold fin2finS in Hvalid. simpl in Hvalid.
       unfold fin2finS. simpl. 
       destruct(f [ | n'] ). 
       *  f_equal. unfold nat2fin. 
        unfold idx, v_idx. simpl. rewrite (Nat.eqb_refl). auto.
       * contradiction Hvalid. auto.
    +  contradiction Hm. auto. 
Qed.


(* given a function u defined on fin (S m'), build a function on fin m'. *)
Definition finf_pred {m d} (u : fin (S m) -> option (exp d)) 
 : fin m -> option (exp d) := fun (i:fin m) => u (@fin2finS m i).

Lemma finf_pred_correct {m d} (u : fin (S m) -> option (exp d)) :
  forall (i: fin m), u (fin2finS i) = finf_pred u i.
Proof. intro. reflexivity. Qed.

Lemma finf_pred_eq0 {m d} (u1 u2 : fin (S m) -> option (exp d)) :
  (forall (i:fin (S m)), u1 i = u2 i) ->
  forall (i:fin m), finf_pred u1 i = finf_pred u2 i.
Proof. intros. unfold finf_pred. apply H. Qed.

Lemma finf_eq_r {m d} (u1 u2 : fin m -> option (exp d)) :
  (forall (i:fin m), u1 i = u2 i) -> u1 = u2.
Proof. intros.  fun_ext. apply H. Qed.

Lemma finf_eq_l {m d} (u1 u2 : fin m -> option (exp d)) :
  u1 = u2 ->  (forall (i:fin m), u1 i = u2 i).
Proof. intros. rewrite H. auto. Qed.

Lemma finf_eq {m d} (u1 u2 : fin m -> option (exp d)) :
  u1 = u2 <->  (forall (i:fin m), u1 i = u2 i).
Proof. split ; [ apply finf_eq_l | apply finf_eq_r ]. Qed.

Lemma finf_pred_eq {m d} (u1 u2 : fin (S m) -> option (exp d)) :
  u1 = u2  -> finf_pred u1 = finf_pred u2.
Proof. intros. unfold finf_pred. fun_ext.
   rewrite finf_eq in H. rewrite (H FS[ x]). reflexivity. 
Qed.

(* (u finf_pred) i = f i *)
Lemma finf_pred_consistent :
  forall (m : nat) (d : data) (u : fin (S m) -> option (exp d)) 
    (i : fin m) (e : option (exp d)),
      u FS[i] = finf_pred u i.
Proof.
  intros m d u i e.  unfold finf_pred. reflexivity.
Qed.

Lemma lt_lt_succ_neq : forall i' m', i' < S m' -> i' <> m' -> i' < m'.
Proof.
  intros i' m' Hlt Hneq. lia. 
Qed.

(* rebuild u from finf_pred u. *)
Definition finf_pred2u {m' d} (upred : fin m' -> option (exp d)) 
  (ulast : option (exp d)) : fin (S m') -> option (exp d) :=
  fun i =>
    match i with
    | exist _ i' Hi' => (* Hi' : i' < S m' *)
      match Nat.eq_dec i' m' with
      | left _ => (* i'=m' *) ulast (* i is the last index *)
      | right Hneq => (* i'<>m' *)
          (* Use the lemma to construct a proof of i' < m' *)
          let Hlt : i' < m' := @lt_lt_succ_neq i' m' Hi' Hneq in
          upred (exist _ i' Hlt)
      end
    end.

(* finf_pred2u can rebuild u from (finf_pred u). *)
Lemma finf_pred2u_correct : forall m' d (u : fin (S m') -> option (exp d)),
  finf_pred2u (finf_pred u) (u (exist _ m' (Nat.lt_succ_diag_r m'))) = u.
Proof.
  intros m' d u.
  apply functional_extensionality. (* Prove equality pointwise *)
  intros i.
  unfold finf_pred2u, finf_pred.
  destruct i as [i' Hi'].
  destruct (Nat.eq_dec i' m') as [-> | Hneq].
  - (* Case 1: i' = m'  --  u [ | m'] = u [ | m']  *)
     f_equal. apply exist_eq.
  - (* Case 2: i' < m'  --  u FS[ [ | i']] = u [ | i'] *)
    simpl. f_equal. unfold fin2finS. simpl. apply exist_eq. 
Qed.

Lemma decompose_ary {d:data} {n:nat} : forall (v : exp (ary '{ S n} d)),
   v = (fst v, snd v).
Proof. intro v. destruct v. reflexivity. Qed.

Lemma mkoptvec_finf_pred :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)) 
    (v : exp (ary '{n} d)) (e : exp d),
    mkoptvec f = Some (v, e) -> mkoptvec (finf_pred f) = Some v.
Proof.
  intros n d f v e Hmkoptvec. (* Introduce variables and hypothesis *)
  unfold finf_pred. unfold mkoptvec in *.  
  induction n as [ | n'].
+ destruct v.
  unfold mkoptvec4 in Hmkoptvec.
  destruct (F[ Nat.lt_succ_diag_r 0]).
  unfold mkoptvec4 . reflexivity.
+ specialize(IHn' (@finf_pred (S n') d f)). specialize(IHn' (fst v)).
  assert(v = (fst v, snd v)). apply decompose_ary.
  rewrite H. unfold finf_pred in IHn'.
  rewrite H in Hmkoptvec.
  assert(H1 : mkoptvec4 (fun i : fin (S n') => f FS[ i]) <> None).
  rewrite mkoptvec_iff_all_fi. intro i.
  assert(H2 : mkoptvec4 f <> None). rewrite Hmkoptvec. 
  apply some_neq_none .
  rewrite mkoptvec_iff_all_fi in H2.  apply H2.
 rewrite<- decompose_ary in *. 
 rewrite mkoptvec4_simplify in Hmkoptvec.
 destruct(mkoptvec4 (fun i : fin (S n') => f FS[ i]) ).
 - (* Some *) destruct (f [ | S n'] )  in Hmkoptvec.
   * rewrite (@some_equal (exp (ary '{ S n'} d)) (exp d) e0 v e1 e) in Hmkoptvec.
     inversion Hmkoptvec. subst e0. auto.
   * inversion Hmkoptvec.
 - (* None *) inversion Hmkoptvec.
Qed.

Lemma mkoptvec_fin_last :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)) 
    (v : exp (ary '{n} d)) (e : exp d),
    mkoptvec f = Some (v, e) -> f (fin_last n) = Some e.
Proof. intros. 
assert(mkoptvec f <> None). rewrite H. apply some_neq_none.
rewrite mkoptvec_iff_all_fi in H0. 
  induction n as [ | n'].
+ unfold mkoptvec,mkoptvec4 in H.
  destruct( F[ Nat.lt_succ_diag_r 0]).
  - assert(x = 0) by lia. subst x.
    specialize(H0 (fin_last 0) ).
    apply some_none in H0.
    destruct H0. (* Set Printing All *)
    assert((fin_last 0) = (@exist nat (fun i : nat => lt i (S O)) O l) ).
    apply exist_equal. auto.
    rewrite<- H1 in H. rewrite H0 in H.
    inversion H. subst x. exact H0.
+ unfold mkoptvec in H. rewrite mkoptvec4_simplify in H.
  destruct (mkoptvec4 (fun i : fin (S n') => f FS[ i])).
  - (* Some *)
   (* assert(H1 : f [ | S n'] <> None). *)
    assert(H1 : f (@exist nat (fun i : nat => lt i (S (S n'))) 
       (S n') (Nat.lt_succ_diag_r (S n')))  <> None ).
      { apply H0. } 
    apply some_none in H1. destruct H1. rewrite H1 in H.
    inversion H. subst x. exact H1.
   - (* None *) inversion H.
Qed.

Lemma some_imply_none {A:Set} : forall (a: option A) (b:A),
  a = Some b -> a <> None.
Proof. intros. rewrite H. apply some_neq_none. Qed.

Corollary mkoptvec_not_none_finf_pred :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)), 
    mkoptvec f <> None -> mkoptvec (finf_pred f) <> None.
Proof. intros. 
apply some_none in H. destruct H. destruct x.
apply mkoptvec_finf_pred in H.
apply some_imply_none with (b:=v) (a := mkoptvec (finf_pred f)).
exact H. 
Qed.

Corollary mkoptvec_not_none_fin_last :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)) ,
    mkoptvec f <> None -> f (fin_last n) <> None.
Proof. intros. 
apply some_none in H. destruct H. destruct x.
apply mkoptvec_fin_last in H.
apply some_imply_none with (b:=e) (a := (f (fin_last n))).
exact H. 
Qed.

Lemma mkoptvec_none :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)) ,
    mkoptvec f = None -> 
     mkoptvec (finf_pred f) = None \/ f (fin_last n) = None.
Proof. intros. rewrite mkoptvec_none_iff_exist_none in H. destruct H.
 destruct n. 
+ (* n=0 *) right. unfold fin_last. rewrite<- H.
  f_equal. destruct x.  apply exist_equal. lia. 
+ (* S n *) (* analysis by x = S n or x < S n *)
  destruct x  eqn:H0.  
  specialize (Nat.lt_eq_cases x0 (S n) ).
  assert(H1 : x0 <= S n) by lia. intro H2. 
  rewrite H2 in H1. destruct H1. (* H1 : x0 < S n \/ x0 = S n *) 
  - left.  rewrite mkoptvec_none_iff_exist_none.
    exists (nat2fin H1). rewrite<- H. unfold finf_pred.
    f_equal. apply exist_equal. (* F[ H1]=x0 *) reflexivity.
  - right. rewrite<- H. f_equal. unfold fin_last. 
    apply exist_equal. rewrite H1. auto. 
Qed.

Corollary mkoptvec_not_none :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)),
    mkoptvec f <> None -> 
    mkoptvec (finf_pred f) <> None /\ f (fin_last n) <> None.
Proof.
  intros n d f. split.
  + apply mkoptvec_not_none_finf_pred . exact H. 
  + apply mkoptvec_not_none_fin_last. exact H.    
Qed.

Lemma mkoptvec_none_inv :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)) ,
     mkoptvec (finf_pred f) = None \/ f (fin_last n) = None
  ->  mkoptvec f = None.
Proof. intros. destruct (mkoptvec f) eqn:Hf. 
+ apply some_is_not_none in Hf. apply mkoptvec_not_none in Hf. tauto. 
+ reflexivity. 
Qed.

Corollary mkoptvec_none_equiv :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)) ,
   mkoptvec f = None <->
   mkoptvec (finf_pred f) = None \/ f (fin_last n) = None.
Proof. intros. split;[apply mkoptvec_none | apply mkoptvec_none_inv]. Qed.

Definition opt_exp_pair {d:data} (n:nat) 
 (z: option (exp (ary '{n} d)) * option (exp d)) : (option (exp (ary '{S n} d))) :=
  opt_pair z.

(* decompose (mkoptvec f) into first part and the last element. *)
Lemma mkoptvec_decompose {d:data} :
  forall (n:nat) (f : fin (S n) -> option (exp d)), 
    mkoptvec f = opt_pair (mkoptvec (finf_pred f), f (fin_last n)).
Proof. intros.
 destruct (mkoptvec f) as [e |] eqn:H.  
 (* e : exp (ary '{ S n} d) H : mkoptvec f = Some e *)
+ (* Some *) destruct e. 
  assert(H0 : mkoptvec (finf_pred f) = Some v). 
    { apply mkoptvec_finf_pred with (e:=e). exact H. }
  assert(H1 : f (fin_last n) = Some e).
    { apply mkoptvec_fin_last with (v:=v). exact H. } 
  rewrite H0,H1. reflexivity. 
+ (* None *)  apply mkoptvec_none in H. destruct H; rewrite H.
  - (* None = opt_pair (None, f (fin_last n)) *) reflexivity. 
  - (* None = opt_pair (mkoptvec (finf_pred f), None) *) 
     rewrite opt_pair_right_none; reflexivity. 
Qed.

Corollary mkoptvec_not_none_inv :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)),
    mkoptvec (finf_pred f) <> None /\ f (fin_last n) <> None
    ->  mkoptvec f <> None.
Proof.
  intros n d f H. rewrite mkoptvec_decompose.
  rewrite<- opt_pair_not_none in H. exact H.
Qed.

Theorem mkoptvec_not_none_equiv :
  forall (n : nat) (d : data) (f : fin (S n) -> option (exp d)),
    mkoptvec f <> None <-> 
    mkoptvec (finf_pred f) <> None /\ f (fin_last n) <> None.
Proof.   intros n d f. split;
[ apply mkoptvec_not_none | apply mkoptvec_not_none_inv]. 
Qed.

Lemma mkoptvec4_finf_pred_injective : 
  forall m d (u1 u2 : fin (S m) -> option (exp d)),
  mkoptvec4 u1 <> None -> mkoptvec4 u1 = mkoptvec4 u2 -> 
  mkoptvec4 (finf_pred u1) = mkoptvec4 (finf_pred u2).
Proof. intros. destruct ( mkoptvec4 u1) eqn: H1. symmetry in H0.
  destruct e. 
+ apply mkoptvec_finf_pred in H0, H1.
  unfold mkoptvec in H0,H1. 
  rewrite H1, H0. reflexivity. 
+ contradiction H. auto. 
Qed. 

Lemma mkoptvec4_fin_last_injective : 
  forall m d (u1 u2 : fin (S m) -> option (exp d)),
  mkoptvec4 u1 <> None -> mkoptvec4 u1 = mkoptvec4 u2 -> 
    u1 (fin_last m) = u2 (fin_last m).
Proof. intros. destruct ( mkoptvec4 u1) eqn: H1. symmetry in H0.
  destruct e. 
+ apply mkoptvec_fin_last in H0, H1.
  rewrite H1, H0. reflexivity. 
+ contradiction H. auto. 
Qed. 

Lemma exist_proof_irrelevance {A:Set} {m a:nat} {h k:a<m} : 
 forall (u1 u2 : fin m -> A) (H: u1 (nat2fin h) = u2 (nat2fin h)),
   u1 (nat2fin k) = u2 (nat2fin k).
Proof. intros. assert(H0 : h = k) by apply proof_irrelevance.
rewrite H0 in H. exact H. 
Qed. 
  

Theorem mkoptvec_injective : forall m d (u1 u2 : fin m -> option (exp d)),
   mkoptvec u1 <> None -> mkoptvec u1 = mkoptvec u2 
     -> (forall i, u1 i = u2 i). 
Proof.
  induction m as [| m' IH]; intros d u1 u2 H H1 i .
  - (* Case m = 0 *)
    inversion i. lia. (* No valid indices *)
  - (* Case m = S m' *) 
    assert(H2: mkoptvec4 (finf_pred u1) = mkoptvec4 (finf_pred u2)).
    { apply mkoptvec4_finf_pred_injective. exact H. exact H1. }
    assert(H3 : u1 (fin_last m') = u2 (fin_last m')).
    { apply mkoptvec4_fin_last_injective. exact H. exact H1. }
    assert(H7: mkoptvec4 (finf_pred u1) <> None).
    { apply mkoptvec_not_none_finf_pred. exact H. }
    assert(H8: u1 (fin_last m') <> None).
    { apply mkoptvec_not_none_fin_last. exact H. }
    specialize(IH d (finf_pred u1) (finf_pred u2) H7 H2).
    unfold finf_pred in IH.
    (* analysis by i = S m' or i < S m' *)
    destruct i eqn:H4.  
    specialize (Nat.lt_eq_cases x m' ).
    intro H5. 
    assert(H6: x<=m') by lia. rewrite H5 in H6.
    destruct H6.    
    + (* H0 : x < m' *)
        specialize(IH (nat2fin H0)). 
        unfold fin2finS in IH. simpl in IH.
        (* IH:u1 [ | x] = u2 [ | x] |- u1 [ | x] = u2 [ | x] *)
        (* avoid using explicit proof terms *)
        apply (exist_proof_irrelevance u1 u2 IH). 
    + (* x=m' *) subst x. 
        unfold fin_last in H3. 
        apply (exist_proof_irrelevance u1 u2 H3). 
Qed.

(* idx access an element of a vector which is not the last one. *)
Lemma idx_pred : forall {n : nat} {t : data} 
  (v : exp (ary '{n} t)) (e: exp t)  (i : fin n),
  @idx (S n) t ((v,e):exp (ary '{S n} t)) FS[i] = idx v i.
Proof. intros. unfold idx,v_idx. destruct i eqn:Hi.
 assert(Hfs : FS[ i] < n). 
 { unfold fin2finS. rewrite Hi. simpl. exact l. } 
 specialize (@v_nth_Sn (exp t) n v e FS[ i] (exp_default t) Hfs).
 intro H. rewrite Hi in H. exact H. 
Qed.

(* idx access the last element of an array. *)
Lemma idx_last : forall {n : nat} {t : data} 
  (v : exp (ary '{n} t)) (e: exp t),
  @idx (S n) t ((v,e):exp (ary '{S n} t)) (fin_last n) = e.
Proof. intros. unfold idx,v_idx.
simpl. rewrite Nat.eqb_refl.  auto.
Qed.

(* idx_opt access an element of an optino vector which is not the last one. *)
Lemma idx_opt_pair_pred {d:data} {n:nat}  :
  forall (v : exp (ary '{ n} d)) (e : exp d) (i:fin n), 
   idx_opt (opt_exp_pair n (Some v, Some e)) FS[i] = idx_opt (Some v) i.
Proof. intros. unfold opt_exp_pair.  simpl. specialize (idx_pred v e i). intro H.
f_equal. exact H. 
Qed.
(* generally the following is not valid:
   idx_opt (opt_exp_pair n (v,e)) FS[i] = idx_opt v i
   because any element in v,e is none leads to opt_exp_pair returns None.
*)

(* conversion between opt_exp_pair and opt_pair. *)
Lemma opt_pair_eq_opt_exp_pair  {d:data} {n:nat} :
  forall (v : option (exp (ary '{ n} d))) (e : option ( exp d)) , 
    opt_exp_pair n (v,e) = opt_pair (v,e).
Proof. unfold opt_exp_pair. reflexivity. Qed. 

(* idx_opt access the last element of an option array. *)
Lemma idx_opt_pair_last {d:data} {n:nat} {f:fin (S n) -> option (exp d)} :
  forall (v : exp (ary '{ n} d)) (e : exp d), 
   idx_opt (opt_exp_pair n (Some v, Some e)) (fin_last n) = Some e.
Proof. intros.  simpl. specialize (idx_last v e). intro H.
f_equal. exact H. 
Qed.

Lemma idx_opt_pair_pred_not_none {d:data} {n:nat}  :
  forall (v : option (exp (ary '{ n} d))) (e : option (exp d)) (i:fin n), 
   (opt_pair (v,e))<>None -> 
   idx_opt (opt_exp_pair n (v,e)) FS[i] = idx_opt v i.
Proof. unfold opt_exp_pair. intros. 
  rewrite (opt_pair_not_none v e) in H. destruct H.
  apply some_none in H. apply some_none in H0.
  destruct H,H0. subst v. subst e.
  rewrite<-  (@opt_pair_eq_opt_exp_pair d n). 
  apply idx_opt_pair_pred.
Qed.

(*
Lemma v_nth_mk_vec: forall  (n:nat) (i:nat) (f:fin n -> A) (x0:A)
 (H: i < n),  v_nth x0 (mk_vec f) i = f (nat2fin  H).
*)
Theorem idx_opt_mkoptvec : forall (n : nat) (d : data) 
  (f : fin n -> option (exp d)) (i : fin n),
  mkoptvec f <> None -> idx_opt (mkoptvec f) i = f i.
Proof.
  intros n d f i Hn. (* Introduce variables *)
  induction n as [| n' IH]. (* Induction on n *)
  - (* Base case: n = 0 *)
    destruct i. lia. (* fin 0 is uninhabited, so this case is trivial *)
  - (* Inductive case: n = S n' *)
    (* decompose (mkoptvec f) to first part and the last element. *)
    rewrite mkoptvec_decompose.    
    assert(Hfp : mkoptvec (finf_pred f) <> None).   
      { apply mkoptvec_not_none_finf_pred. exact Hn. }
      apply some_none in Hfp. destruct Hfp as [x0] .  
      (* H : mkoptvec (finf_pred f) = Some x0 *) rewrite H.
    assert(Hfl : f (fin_last n') <> None).   
      { apply mkoptvec_not_none_fin_last. exact Hn. }
      apply some_none in Hfl. destruct Hfl as [x1] .  
      (* H0 : mkoptvec (finf_pred f) = Some x1 *) rewrite H0.
    (* idx_opt (opt_pair (Some x0, Some x1)) [ | x] = f [ | x] *)

    (* analysis by i = n' or i < n' *)
    destruct i eqn:Hi.  
    specialize (Nat.lt_eq_cases x n' ).
    specialize (IH (finf_pred f) ).
    (* derive H: mkoptvec f = Some x0 *)
    assert(Hnoriginal : mkoptvec f <> None) by exact Hn.
    apply some_none in Hn. destruct Hn. 
    intro Hxn. (* Hxn : x <= n' <-> x < n' \/ x = n' *)
    assert(Hxlen: x<=n') by lia. rewrite Hxn in Hxlen.
    (* Hxlen : x < n' \/ x = n' *) 
    destruct Hxlen.
    + (* x<n' *) 
      (* H2 : x < n' *)
      (* idx_opt (opt_pair (Some x0, f (fin_last n'))) [ | x] = f [ | x] *)
      specialize( @idx_opt_pair_pred d n' x0 x1 F[H2]).
      intro Hiopp. unfold opt_exp_pair in Hiopp.
      simpl in Hiopp. (* Hiopp : Some (x0, x1) |[ FS[ F[ H2]]] = Some x0 |[ F[ H2]] *)
      simpl. (* Some (x0, x1) |[ [ | x]] = f [ | x] *)
      specialize(IH F[H2]).
      rewrite H in IH.      
      assert(H5: Some x0 <> None) by apply some_neq_none.
      specialize(IH H5). simpl in IH.
(* 
     inversion Hiopp. unfold fin2finS in H4. simpl in H4.
      (*H4 : (x0, x1) |[ [ | x]] = x0 |[ F[ H2]] *)
*)
      rewrite IH in Hiopp. unfold finf_pred in Hiopp.
      (* Hiopp : Some (x0, x1) |[ FS[ F[ H2]]] = finf_pred f F[ H2] *)
      unfold fin2finS in Hiopp. simpl in Hiopp. clear H5.
(*
Hiopp : Some (x0, x1) |[ [ | x]] = f [ | x]
______________________________________(1/1)
Some (x0, x1) |[ [ | x]] = f [ | x]
*)
     assert (Heq : Nat.lt_lt_succ_r x n' H2 = l ) by
        apply proof_irrelevance. 
     rewrite Heq in Hiopp. exact Hiopp.
   + (* x=n' *) subst x. simpl. 
      unfold fin_last in H0. simpl in H0.
      unfold nat2fin in H0. simpl in H0. 
      assert (Heq : Nat.lt_succ_diag_r n' = l ) by
        apply proof_irrelevance.
      rewrite<- Heq. rewrite H0.
      f_equal. (* (x0, x1) |[ [ | n']] = x1 *)
      specialize( idx_last x0 x1). unfold fin_last.
      rewrite Heq. auto. 
Qed.

Corollary idx_opt_mkoptvec_all : forall (n : nat) (d : data) 
  (f : fin n -> option (exp d)),  mkoptvec f <> None 
  -> forall (i : fin n), idx_opt (mkoptvec f) i = f i.
Proof. intros.  apply idx_opt_mkoptvec. exact H. Qed. 


Corollary idx_opt_mkoptvec_none : forall (n : nat) (d : data) 
  (f : fin n -> option (exp d)) (i : fin n), 
  idx_opt (mkoptvec f) i = None -> (mkoptvec f) = None.
Proof. intros.  destruct (option_none_dec (mkoptvec f)) as [Hl | Hr].
+ (* Hl : mkoptvec f = None *) exact Hl. 
+ (* Hr : mkoptvec f <> None *) rewrite idx_opt_mkoptvec in H.
  rewrite mkoptvec_iff_all_fi in Hr. 
  - specialize(Hr i). contradiction. 
  - exact Hr. 
Qed.

Corollary idx_opt_mkoptvec_all_not_none : forall (n : nat) (d : data) 
  (f : fin n -> option (exp d)),  mkoptvec f <> None 
  -> forall (i : fin n), idx_opt (mkoptvec f) i <> None.
Proof. intros. intro Hn. 
apply (idx_opt_mkoptvec_none  d f i) in Hn. contradiction. 
Qed.  

Definition zero_lt_one : 0<1 := Nat.lt_succ_diag_r 0.
Definition fin1 {n:nat} := F[zero_lt_one].

Lemma idx_opt_mkoptvec_pred : forall (n : nat) (d : data) 
  (f : fin (S (S n)) -> option (exp d)), 
  (forall (i : fin (S (S n))), idx_opt (mkoptvec f) i <> None)
   ->  (forall i : fin (S n), idx_opt (mkoptvec (finf_pred f)) i <> None).
Proof. intros n d f H. intro i.
specialize(H FS[i]). unfold finf_pred. intro.
rewrite<- H0 in H. apply H.
assert(mkoptvec (fun i : fin (S n) => f FS[ i]) = None).
apply idx_opt_mkoptvec_none with (i:=i). exact H0.
rewrite H0. rewrite H1 in H. 
assert(H2 : @idx_opt (S n) d None i = None). simpl.  auto. 
rewrite  H2 in H. clear H0.
assert(H3 : mkoptvec(f) = None).
rewrite mkoptvec_none_equiv . left. exact H1. 
rewrite H3. simpl. auto. 
Qed.

(*
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  mkoptvec f = None ->
  mkoptvec (finf_pred f) = None \/ f (fin_last n) = None
*) 
Lemma mkoptvec_last_none : forall (n : nat) (d : data) 
  (f : fin (S n) -> option (exp d)), forall (i : fin (S n)), 
    f (fin_last n) = None ->  mkoptvec f = None.
Proof. intros.  rewrite mkoptvec_none_equiv. right. exact H.  Qed.

Lemma mkoptvec_pred_none : forall (n : nat) (d : data) 
  (f : fin (S n) -> option (exp d)), forall (i : fin (S n)), 
    mkoptvec (finf_pred f) = None ->  mkoptvec f = None.
Proof. intros.  rewrite mkoptvec_none_equiv. left. exact H. Qed.

Corollary idx_opt_mkoptvec_inv : forall (n : nat) (d : data) 
  (f : fin (S n) -> option (exp d)), 
  (forall (i : fin (S n)), idx_opt (mkoptvec f) i <> None)
   ->  mkoptvec f <> None. 
Proof. intros.  intro Hv. induction n as [|n'].
+ (* n=0 *) 
  rewrite mkoptvec_none_equiv in Hv. destruct Hv.
  - simpl in H0. inversion H0.
  -  unfold fin_last in H0. specialize(H (@fin1 1)).  simpl in H.
     destruct (f F[ Nat.lt_succ_diag_r 0] ).
     * (* H0 : Some e = None *) inversion H0.
     * (* H : idx_opt None fin1 <> None *) simpl in H.  contradiction H. 
+ (* Hv : mkoptvec f = None *)
  specialize (IHn' (finf_pred f)).
  rewrite mkoptvec_none_equiv in Hv. destruct Hv.
  - (* H0 : mkoptvec (finf_pred f) = None *)
   assert(H1:(forall i : fin (S n'), idx_opt (mkoptvec (finf_pred f)) i <> None)).
   { apply  idx_opt_mkoptvec_pred. exact H. }
   specialize(IHn' H1). apply  IHn'. exact H0.
  - (* H0 : f (fin_last (S n')) = None  *)
    rewrite mkoptvec_decompose in H. 
    assert(Hns : n' < S (S n')) by lia. 
    specialize(H F[Hns]).
    unfold opt_exp_pair in H. rewrite H0 in H.
    rewrite opt_pair_right_none in H.
    simpl in H. contradiction H. auto.
Qed.

Theorem idx_opt_mkoptvec_equiv : forall (n : nat) (d : data) 
  (f : fin (S n) -> option (exp d)), 
  mkoptvec f <> None <->
  (forall (i : fin (S n)), idx_opt (mkoptvec f) i <> None). 
Proof. intros. split. 
+ apply idx_opt_mkoptvec_all_not_none.
+ apply idx_opt_mkoptvec_inv.
Qed.

Definition liftf {d:data} {n:nat} (f: fin (S n) -> (exp d)) 
  : fin (S n) -> option (exp d) := fun (i:fin (S n)) => Some (f i).

Lemma liftf_not_none {d:data} {n:nat} (f: fin (S n) -> (exp d)) :
   forall (i:fin (S n)), (liftf f) i <> None.
Proof. intro i. unfold liftf. apply some_neq_none. Qed.

Lemma liftf_some {d:data} {n:nat} (f: fin (S n) -> (exp d)) :
   forall (i:fin (S n)), (liftf f) i = Some (f i).
Proof. intro i. unfold liftf. reflexivity. Qed.

Lemma mkoptvec_liftf_not_none {d:data} {n:nat} (f: fin (S n) -> (exp d)) :
   mkoptvec (liftf f) <> None.
Proof. rewrite mkoptvec_iff_all_fi. intro i. unfold liftf. apply some_neq_none.  Qed. 

Lemma idx_opt_mkoptvec_liftf {d:data} {n:nat} (f: fin (S n) -> (exp d)) (i:fin (S n)) :
   idx_opt (mkoptvec (liftf f)) i = Some (f i).
Proof. rewrite idx_opt_mkoptvec.  apply liftf_some. apply mkoptvec_liftf_not_none. Qed. 

Lemma case_i_SSn : forall (n:nat) (i : fin (S (S n))), 
   i = fin_last (S n) \/ i < fin_last (S n).
Proof. intros. destruct i. unfold fin_last. 
  unfold nat2fin. unfold fin2nat.
  assert(H: x = S n \/ x < S n) by lia. destruct H.
+ (* x=S n *) subst x. left. apply exist_eq.
+ (* x<S n *) right. exact H.
Qed.

Lemma case_i_SSn_fin2nat : forall (n:nat) (i : fin (S (S n))), 
   fin2nat i = S n \/ fin2nat i < S n.
Proof. intros. destruct i. unfold fin2nat. lia. Qed.

Lemma mk_vec_S {A:Set} : forall (n:nat) (f : fin (S n) -> A),
  mk_vec f =
  (mk_vec (fun i : fin n => f (fin2finS i)), f (fin_last n)).
Proof. intros x f. reflexivity.  Qed.

Lemma mk_vec_S2 {A:Set} : forall (n:nat) (f : fin (S n) -> A),
  mk_vec f =
  (mk_vec (fun i : fin n => f (fin2finS i)),
   f (exist _ n (Nat.lt_succ_diag_r n))).
Proof. intros x f. reflexivity.  Qed.

Lemma idx_mk_vec_fin_last {d:data} :
  forall (n : nat) (f : fin (S n) -> (exp d)),
    idx (mk_vec f) (fin_last n) = f (fin_last n).
Proof. 
  intros n f. rewrite mk_vec_S. unfold idx. unfold v_idx. 
  apply v_nth_x.
Qed.

(*  accessing the last element of an optional vector constructed by mk_vec f 
    using idx_opt returns Some (f (fin_last (S n))). *)
Lemma idx_opt_mk_vec_fin_last {d : data} :
  forall (n : nat) (f : fin (S (S n)) -> exp d),
    idx_opt (Some (mk_vec f)) (fin_last (S n)) = Some (f (fin_last (S n))).
Proof.
  intros n f.  unfold idx_opt.
  (* Unfold mk_vec *)
  rewrite mk_vec_S. unfold idx. unfold v_idx. f_equal.
  apply v_nth_x.
Qed.
 
Definition finf_pred_pure {m d} (u : fin (S m) -> exp d) 
 : fin m -> (exp d) := fun (i:fin m) => u (@fin2finS m i).
(*
1 goal
d : data
n : nat
f : fin (S (S n)) -> exp d
IHn : forall i : fin (S n), liftf (finf_pred_pure f) i = idx_opt (Some (mk_vec (finf_pred_pure f))) i
i : fin (S (S n))
H : i < fin_last (S n)
______________________________________(1/1)
liftf f i = idx_opt (Some (mk_vec f)) i
*)



Lemma liftf_mk_vec {d:data} {n:nat} (f: fin (S n) -> (exp d)) :
  forall (i:fin (S n)),  liftf f i = idx_opt (Some (mk_vec f)) i.
Proof.
  intros i. unfold liftf, idx_opt. f_equal.
  symmetry. apply v_idx_mk_vec.
Qed.

Lemma mkoptvec_mk_vec {d:data} {n:nat} (f: fin (S n) -> (exp d)) :
   mkoptvec (liftf f) = Some (mk_vec f).
Proof.
  assert (Hnn: mkoptvec (liftf f) <> None) by apply mkoptvec_liftf_not_none.
  apply idx_opt_ary_equiv.
  intro i.
  rewrite idx_opt_mkoptvec_all; auto.
  apply liftf_mk_vec.
Qed.

(* Remaining useful lemmas about mkoptvec: *)
(*
mkoptvec_iff_all_fi:
  forall {d : data} [n : nat] (f : fin n -> option (exp d)),
  mkoptvec f <> None <-> (forall i : fin n, f i <> None)
idx_opt_mkoptvec_liftf:
  forall {d : data} {n : nat} (f : fin (S n) -> exp d) (i : fin (S n)),
  idx_opt (mkoptvec (liftf f)) i = Some (f i)
idx_opt_mkoptvec_all:
  forall [n : nat] (d : data) (f : fin n -> option (exp d)),
  mkoptvec f <> None -> forall i : fin n, idx_opt (mkoptvec f) i = f i
mkoptvec_none_validf_false:
  forall {d : data} [n : nat] (f : fin n -> option (exp d)),
  mkoptvec f = None <-> validf f = false
mkoptvec_validf_true:
  forall {d : data} [n : nat] (f : fin n -> option (exp d)),
  mkoptvec f <> None -> validf f = true
validf_true_mkoptvec:
  forall {d : data} [n : nat] (f : fin n -> option (exp d)),
  validf f = true -> mkoptvec f <> None
mkoptvec_liftf_not_none:
  forall {d : data} {n : nat} (f : fin (S n) -> exp d), mkoptvec (liftf f) <> None
mkoptvec_iff_validf:
  forall {d : data} [n : nat] (f : fin n -> option (exp d)),
  mkoptvec f <> None <-> validf f = true
idx_opt_mkoptvec_none:
  forall [n : nat] (d : data) (f : fin n -> option (exp d)) (i : fin n),
  idx_opt (mkoptvec f) i = None -> mkoptvec f = None

mkoptvec_none_iff_exist_none:
  forall {d : data} [n : nat] (f : fin n -> option (exp d)),
  mkoptvec f = None <-> (exists i : fin n, f i = None)

idx_opt_mkoptvec:
  forall [n : nat] (d : data) (f : fin n -> option (exp d)) (i : fin n),
  mkoptvec f <> None -> idx_opt (mkoptvec f) i = f i
idx_opt_mkoptvec_all_not_none:
  forall [n : nat] (d : data) (f : fin n -> option (exp d)),
  mkoptvec f <> None -> forall i : fin n, idx_opt (mkoptvec f) i <> None
mkoptvec_last_none:
  forall [n : nat] (d : data) (f : fin (S n) -> option (exp d)),
  fin (S n) -> f (fin_last n) = None -> mkoptvec f = None
mkoptvec_not_none_fin_last:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  mkoptvec f <> None -> f (fin_last n) <> None
mkoptvec_last:
  forall {d : data} [n : nat] (f : fin (S n) -> option (exp d)) [e : exp d],
  validf f = true ->
  f (fin_last n) = Some e -> idx_opt (mkoptvec f) (fin_last n) = f (fin_last n)
mkoptvec_decompose:
  forall {d : data} [n : nat] (f : fin (S n) -> option (exp d)),
  mkoptvec f = opt_pair (mkoptvec (finf_pred f), f (fin_last n))
mkoptvec_injective:
  forall [m : nat] (d : data) (u1 u2 : fin m -> option (exp d)),
  mkoptvec u1 <> None -> mkoptvec u1 = mkoptvec u2 -> forall i : fin m, u1 i = u2 i
idx_opt_mkoptvec_inv:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  (forall i : fin (S n), idx_opt (mkoptvec f) i <> None) -> mkoptvec f <> None
mkoptvec_pred_none:
  forall [n : nat] (d : data) (f : fin (S n) -> option (exp d)),
  fin (S n) -> mkoptvec (finf_pred f) = None -> mkoptvec f = None
mkoptvec_not_none_finf_pred:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  mkoptvec f <> None -> mkoptvec (finf_pred f) <> None
idx_opt_mkoptvec_equiv:
  forall [n : nat] (d : data) (f : fin (S n) -> option (exp d)),
  mkoptvec f <> None <-> (forall i : fin (S n), idx_opt (mkoptvec f) i <> None)
idx_opt_mkoptvec_pred:
  forall [n : nat] (d : data) (f : fin (S (S n)) -> option (exp d)),
  (forall i : fin (S (S n)), idx_opt (mkoptvec f) i <> None) ->
  forall i : fin (S n), idx_opt (mkoptvec (finf_pred f)) i <> None
mkoptvec_fin_last:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)) 
    [v : exp (ary '{ n} d)] [e : exp d],
  mkoptvec f = Some (v, e) -> f (fin_last n) = Some e
mkoptvec_none_inv:
  forall [n : nat] (d : data) (f : fin (S n) -> option (exp d)),
  mkoptvec (finf_pred f) = None \/ f (fin_last n) = None -> mkoptvec f = None
mkoptvec_none:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  mkoptvec f = None -> mkoptvec (finf_pred f) = None \/ f (fin_last n) = None
mkoptvec_none_equiv:
  forall [n : nat] (d : data) (f : fin (S n) -> option (exp d)),
  mkoptvec f = None <-> mkoptvec (finf_pred f) = None \/ f (fin_last n) = None
mkoptvec_not_none_inv:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  mkoptvec (finf_pred f) <> None /\ f (fin_last n) <> None -> mkoptvec f <> None
mkoptvec_not_none:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)),
  mkoptvec f <> None -> mkoptvec (finf_pred f) <> None /\ f (fin_last n) <> None
mkoptvec_not_none_equiv:
  forall [n : nat] (d : data) (f : fin (S n) -> option (exp d)),
  mkoptvec f <> None <-> mkoptvec (finf_pred f) <> None /\ f (fin_last n) <> None
mkoptvec_finf_pred:
  forall [n : nat] [d : data] (f : fin (S n) -> option (exp d)) 
    [v : exp (ary '{ n} d)] [e : exp d],
  mkoptvec f = Some (v, e) -> mkoptvec (finf_pred f) = Some v
*)

Lemma skip_l: forall c:comm,
  skip '; c = c.
Proof. auto. Qed.

Lemma skip_r: forall c:comm,
  c '; skip = c.
Proof. auto. Qed.

Lemma seq_assoc: forall (c1 c2 c3:comm),
  c1 '; (c2 '; c3) = (c1 '; c2) '; c3 .
Proof. auto. Qed.

Lemma seq_fold: forall (c1 c2:comm) (rho:env),
  c2 (c1 rho) = (c1 '; c2) rho.
Proof. auto. Qed. 

Lemma seqfor_Sn: forall (m:nat)(p: fin (S m) -> comm),
  seqfor p = seqfor (fun i:fin m => p FS[i]) '; p '[m].
Proof. auto. Qed.

Lemma parfor_Sn: forall d m p (a:acc (ary '{(S m)} d)),
  parfor a p
  = parfor (fst a) (fun i => p FS[i]) ';
    p '[m] (snd a).
Proof. auto. Qed.

Lemma seqfor_no_change: forall (m:nat),
  seqfor (fun (i:fin m) (rho:env) => rho) = skip.
Proof. induction m;auto. Qed.

Lemma seqfor_mul_0: forall (m:nat) (p: fin (m*0) -> comm),
  seqfor p = skip.
Proof.
  induction m. auto. auto.
Qed.

Lemma seqfor_0: forall (p: fin 0 -> comm),
  seqfor p = skip.
Proof. auto. Qed.

Ltac v_simpl:=
  try (rewrite ?v_nth_mk_vec;f_simpl);
  try (rewrite ?v_nth_Sn;f_simpl).

Ltac c_simpl :=
  try unfold mkvSeq,mkvPar,idx,idxAcc,v_idx;
  rewrite ?skip_l,?skip_r,?seq_assoc,?seqfor_no_change,?seqfor_mul_0,?seqfor_0; 
  repeat
    match goal with
    | f: fle _ |- _ => induction f;simpl
    | |- seq _ _ = seq _ _ => f_equal
    | |- seqfor (fun _: fin (S ?n) => _) 
                   = seqfor (fun _: fin (S ?n) => _) =>
                   f_equal;fun_ext;v_simpl
    | |- seqfor (fun _: fin ?n => _) 
                   = seqfor (fun _: fin ?n => _) =>
                   induction n;auto;f_equal;fun_ext;v_simpl
    | |- seqfor (fun _: fin (S ?n) => _) _
                   = seqfor (fun _: fin (S ?n) => _) _ =>
                   f_equal;fun_ext;f_equal;v_simpl
    | |- seqfor (fun _: fin ?n => _) _ 
                   = seqfor (fun _: fin ?n => _) _ =>
                   induction n;auto;f_equal;fun_ext;v_simpl
    | |- mk_vec (fun _: fin ?n => _) = mk_vec (fun _: fin ?n => _) =>
                   induction n;auto;f_equal;fun_ext;v_simpl
    | |- mk_vec (fun _: fin (S ?n) => _) = mk_vec (fun _: fin (S ?n)=> _) =>
                   f_equal;fun_ext;v_simpl
    | |- (fun _: fin (S ?n) => _ ) = (fun _: fin (S ?n) => _ ) => fun_ext;v_simpl
    | _ => auto
    end.

Ltac p_simpl:=
  rewrite ?path_eqb_refl,?Nat.eqb_refl,
    ?Bool.andb_true_l,?Bool.andb_true_r,
    ?Bool.andb_false_l,?Bool.andb_false_r;auto;
  match goal with
  | H : path_eqb _ _ = true |- _ => apply path_eqb_eq in H;subst
  | H : path_eqb _ _  = false |- _ => apply path_eqb_neq in H
  | _ => auto
  end.

(* 针对不同数据类型的操作(assign, access)之间所满足的性质, 该性质对于后续new_equiv、max_equiv的证明至关重要.
1. access_assign: access ((a |:= e) x) a = e.
2. assign_assign: (a |:= e1) ((a |:= e2) x) = (a |:= e1) x. *)

(* env的定义是path -> exp num, 以最底层的类型为基地,
而我们实际操作的是针对acc d -> exp d整体类型之间的访问、更新等等操作,
因此为了将以上两者关联起来，方便后续对环境中的不同类型的元素(acc,exp)进行操作,
将acc d类型替换为和path有关的类型定义：

acc d的具体定义：
acc' : {d:data} path -> acc d.

该函数接受一个data的隐式参数, path类型的参数，返回acc d类型, 这样就根据访问路径path具体定义出了acc d. *)
Fixpoint acc' {d : data} (p : path) : acc d :=
  match d with
  | num => p:acc num
  | @ary n m d1 => mk_vec (fun i => acc' (AryIdx i p)) (* array of length m *)
end.
(* 
Fixpoint acc' {d:data} (p:path) : acc d:=
  match d with
  | num => p:acc num
  | @ary n m d1 => mk_vec (fun i => acc' (AryIdx n F[ i ] p))
  end.
*)

Lemma if_then_eq {A:Set} (b:bool) : forall (e e1 e2:A), e1 = e2 ->
  (if b then e else e1) = (if b then e else e2).
Proof. intros. destruct b.  reflexivity. apply H. Qed.

Lemma update_equal {d:data} : forall (a1 a2: acc d) (e1 e2 : exp d),
   a1=a2 -> e1=e2 -> a1 |:= e1 = a2 |:= e2.
Proof. intros. f_equal. exact H. exact H0. Qed.
(*
Lemma acc'_AryIdx_eq {d:data} : 
  forall  (x : nat) (x1 : fin (S x)) (a1 : path)
         (H3 : fin2nat x1 < S (S x)) (H4 : fin2nat x1 < S x),
    @acc' d (AryIdx (nat2fin H3) a1) = 
    @acc' d (AryIdx (nat2fin H4) a1).
Proof.
  intros d x x1 a1 H3 H4.

  (* Simplify the indices *)
  unfold nat2fin.

  (* Show that the indices are equal *)
  assert (Heq: fin2nat (exist _ (fin2nat x1) H3) = fin2nat (exist _ (fin2nat x1) H4)).
  {
    (* Both indices reduce to fin2nat x1 *)
    rewrite fin2nat_exist.
    rewrite fin2nat_exist.
    reflexivity.
  }

  (* Use injectivity of AryIdx to prove equality of paths *)
  apply f_equal with (f := fun idx => AryIdx idx a1) in Heq.
  rewrite Heq.

  (* The acc' terms are now syntactically equal *)
  reflexivity.
Qed.
*)

Ltac f_fin :=
  try (apply fin_eq');
  try (apply fin_neq');
  try (apply fle_eq);
  try (apply fle2nat_fle_self);
  autorewrite with fcore;auto with fcore;
  try lia.

Require Import Coq.Logic.ProofIrrelevance.


Require Import String.


(* Demonstration: H3 and H4 produce two distinct paths at runtime. *)  
Lemma different_assignments_are_not_equal :  
  (* We will fix x=0 so that S x=1, S(S x)=2. *)  
  let x := 0 in  
  (* We pick x1: fin (S x)=fin 1 => 0<1, H3: 0<2, H4: 0<1. All trivially true. *)  
  let x1 := (exist (fun k => k < 1) 0 (Nat.lt_0_succ 0)) in  
  let H3 := Nat.lt_0_succ 1 in  (* 0<2 *)  
  let H4 := Nat.lt_0_succ 0 in  (* 0<1 *)  
  let a1 := "A"%string in        (* Some path name *)  
  let v : exp num := INR 42 in         (* Some numeric value to store *)  
  (* LHS path: n = 2 at top, e.g. "AryIdx (n := 2) ..."   
     For the demo we just represent it as: "A--2" *)  
  let pL : path := Var "A--2"  in  
  (* RHS path: n = 1 at top, e.g. "AryIdx (n := 1) ..."   
     We'll call it "A--1" *)  
  let pR : path := Var "A--1" in  
  let cmdL : comm := acc' pL |:= v in  
  let cmdR : comm := acc' pR |:= v in
  let eta0 : env := env_empty in  
  let etaL := cmdL eta0 in  
  let etaR := cmdR eta0 in  
    etaL pL <> etaR pL.
Proof.  
  intros.
  (* Show they differ by checking pL or pR. *)  
  assert (etaL pL = Some v) as HL.  
  { simpl. unfold pL, v. unfold etaL. unfold cmdL. reflexivity. }  
  assert (etaR pL = None) as HR.  
  { simpl. unfold pL, v. unfold etaR. unfold cmdL. reflexivity. } 
  congruence. 
Qed.  


Lemma assign_eq_disproof :
  exists (d : data) (x : nat) (x1 : nat) (a1 : path) 
 (a : exp (ary (fle_self (S x)) d)) (H3 : x1 < x) (H4 : x1 < S x),
  acc' (AryIdx F[H3] a1) |:= v_nth (exp_default d) a x1 <>
  acc' (AryIdx F[H4] a1) |:= v_nth (exp_default d) a x1.
Proof.
  (* Concretely define each witness. *)
  pose (d := num : data). (* dummy “data” *)
  pose (x := 1).                    (* S x = 1 *)
  pose (x1 := 0). (* 0 < 1 *)
  pose (a1 := (Var "A") : path ). (* some path name *)
  pose (a := (exp_default (ary (fle_self (S x)) d)
                        : exp (ary (fle_self (S x)) d))).
  assert (H4 : x1 < S x) by (unfold x1, x; simpl; auto with arith). (* 0<2 *)
  assert (H3 : x1 < x) by ( unfold x1, x; simpl; auto with arith).  (* 0<1 *)
  exists d, x, x1, a1, a, H3, H4.
  Set Printing All.
(*
(* fin n -> fin (S n) *)
Definition fin2finS {n:nat} (i : fin n) : fin (S n):=
  exist _ (fin2nat i) (fin_finS_eq n i).
old:
  @acc' d (AryIdx O (@nat2fin O (@fin2nat (S x) (@nat2fin (S x) (@fin2nat (S x) (@fin2finS x x1))))) a1))
new:
  @acc' d (@AryIdx (S (S x)) (@nat2fin (S (S x)) x1 H3) a1)
*)
  (* Show these two env-producing commands differ. *)
  intros Heq.
  (* Evaluate each command in an empty environment and compare at path
     associated with AryIdx F[H3] a1, which we might informally call "A--2." *)
  set (eta0 := env_empty).
  set (lhsEnv := (acc' (AryIdx F[H3] a1) |:= v_nth (exp_default d) a x1) eta0).
  set (rhsEnv := (acc' (AryIdx F[H4] a1) |:= v_nth (exp_default d) a x1) eta0).

  (* Focus on the path “AryIdx F[H3] a1” in lhs vs. the same path in rhs. *)
  assert (lhsEnv (AryIdx F[H3] a1) = Some (v_nth (exp_default d) a x1)) as L.
  { unfold lhsEnv, acc', eta0; simpl.
    (* By definition, storing at “AryIdx F[H3] a1”makes that path map to Some(...) *)
    reflexivity.
  }
  assert (rhsEnv (AryIdx F[H3] a1) = None) as R.
  { unfold rhsEnv, acc', eta0; simpl.
   (* The path we’re looking up is “AryIdx F[H3] a1,”
      but we stored at “AryIdx F[H4] a1,” which is a different path
      because H3 (0<2) ≠ H4 (0<1) under the code that physically
       encodes “n=2” vs. “n=1.” *)
   reflexivity.
  }
 
  (* Now we can show that lhsEnv and rhsEnv are different *)  
  unfold lhsEnv, rhsEnv in *.
  rewrite Heq in L.
  rewrite<- Heq in R.
  discriminate R.  
Qed.

Lemma neq_lt : forall (x x0 : nat),
  x < x0 -> (x =? x0)%nat = false.
Proof.
  intros x x0 H0.
  (* Use the fact that x0 < x implies x0 ≠ x *)
  apply Nat.eqb_neq.  lia.
Qed.

Definition finLt {n x:nat} (H:x < n) (i:fin x) : fin n.
Proof.
  (* Decompose i into its value and proof *)
  destruct i as [i0 Hi].
  (* Construct the new value i0 + (n - x) *)
  apply (exist _ i0).
  (* Prove that i0 < n *)
  assert (x + (n - x) = n) as Heq by lia.
  (* Rewrite using the equality *)
  rewrite <- Heq.
  (* Use transitivity to prove i0 < n *)
  apply Nat.lt_le_trans with (m := x).
  - exact Hi.
  - lia. 
Defined.

Definition Sx_lt_n_implies_x_lt_n : forall x n, S x < n -> x < n :=
  fun x n H => Nat.lt_trans x (S x) n (Nat.lt_succ_diag_r x) H.

Definition c_idx {n:nat} {t:data} (v:acc (ary '{n} t)) (i: fin n) 
  : acc t := v_idx (acc_default t) v i.

(* 根据变量访问表达式的值 *)
(* 当d是向量类型时，acc d相当于这个向量的首地址以及向量长度信息，
   access d rho a 范围这个地址上的完整的向量，如果这个向量的存储空间
   中有一个元素没有分配，也就是该地址位的访问结果返回None，那么
   整个向量就是None。
Fixpoint access {d:data}(rho:env): acc d -> option (exp d):=
  match d with
  | num => fun (p:acc num) => rho p
  | @ary n m d1 => fun (p:acc (@ary n m d1)) => 
     mkoptvec (fun (i:fin m) => access rho p|{i})
  end.
*) 
Fixpoint access {d:data}(rho:env): acc d -> option (exp d):=
  match d with
  | num => fun (p:acc num) => rho p
  | @ary n m d1 => fun (p:acc (@ary n m d1)) => 
     mkoptvec (fun (i:fin m) => @access d1 rho (c_idx p i))
  end.

Lemma access_num : forall (rho:env) (p:acc num) ,
  @access num rho p = rho p.
Proof. intros. reflexivity. Qed.

Lemma access_ary : forall (d:data) (rho:env) (n:nat) (m:fle n) 
  (p:acc (@ary n m d)) ,
  @access (@ary n m d) rho p = 
  mkoptvec (fun (i:fin m) => @access d rho (c_idx p i)).
Proof. intros. reflexivity. Qed.

Definition not_empty_ary (d:data) : Prop :=
  match d with
   | @ary n m _ => (fle2nat m <> 0) (* m=0 *)
   | _ => True
  end.
Definition d2opt {d:data} (e:exp d) : option (exp d) :=
  match d with
    | @ary n m _ => if ((fle_0 n) =? m)%nat then None else Some e
    | num => Some e
  end.   
 
(* Purpose of the lemma:
 For distinct paths a1 and a2 (a1 ≠ a2), performing a bulk assignment to all 
 elements of the array accessed via a1 (using seqfor) does not alter the value
 retrieved when accessing a different array via a2. This holds provided that 
 individual element assignments to a1 preserve the value of a2 
 (non-interference condition).
Definition new {d:data} (p: acc d -> comm) (a: acc d): comm := 
  p a '; vrm a.
*)

Lemma update_basic : forall (m:env) (x : path) (v : exp num) (x' : path),
  @update m x v x' = if x =? x' then Some v else m x'.
Proof. intros. reflexivity. Qed.

Lemma assign_num : forall (rho:env) (p:acc num) (e:exp num),
   @assign num p e rho = update rho p e. (* a !-> e; rho *)
Proof. intros. reflexivity. Qed.

Lemma assign_ary : forall (d:data) (n:nat) (m:fle n) 
   (a:acc (@ary n m d)) (e:exp (ary m d)),
   @assign (@ary n m d) a e = 
   seqfor (fun i : fin m => @assign d a |{ i} e |[ i]).
Proof. intros. reflexivity. Qed.

Lemma acc'_num : forall (p:path) ,  @acc' num p = p.
Proof. intros. reflexivity. Qed.

Lemma acc'_ary : forall (d:data) (n:nat) (m:fle n) (p:path) ,
  @acc' (@ary n m d) p = 
  mk_vec (fun i : fin m => @acc' d (AryIdx i p)).
Proof. intros; reflexivity. Qed.

Lemma idxAcc_acc'_eq : forall (d:data) (n:nat) (f:fle n) (a:path) (i:fin (fle2nat f)),
  idxAcc (@acc' (@ary (fle2nat f) (fle_self (fle2nat f)) d) a) i = @acc' d (@AryIdx (fle2nat f) i a).
Proof.
  intros. unfold idxAcc, acc'. apply v_idx_mk_vec.
Qed.

About "_ |{ _ }". (* idxAcc : forall {n : nat} {t : data}, acc (ary '{ n} t) -> fin n -> acc t *)
About "_ |[ _ ]". (* idx    : forall {n : nat} {t : data}, exp (ary '{ n} t) -> fin n -> exp t *)
About "_ |:= _". (* assign : forall {d : data}, acc d -> exp d -> comm *)
About "_ !-> _ ; _". (* update : env -> path -> exp num -> path -> option (exp num) *)

Lemma seqfor_extensionality : forall m (f g : fin m -> comm),
  (forall i, f i = g i) -> seqfor f = seqfor g.
Proof.
  induction m as [ | m' IHm ]; intros f g H.
  - reflexivity.
  - simpl. f_equal.
    + apply IHm. intro i. apply H.
    + apply H.
Qed.

Lemma mkoptvec_dependence : forall m d (u1 u2 : fin m -> option (exp d)),
  (forall i, u1 i = u2 i) -> mkoptvec u1 = mkoptvec u2.
Proof. intros. unfold mkoptvec. apply mkoptvec4_dependence. exact H. Qed.

Lemma access_seqfor_ary_eq_general :
  forall d (a:path) (x:env) (n m:nat) (f: fin n -> fin m) (e:vector (exp d) m),
  (forall j k, f j = f k -> j = k) ->
  (forall p1 p2 (e':exp d) x', p1 <> p2 -> @access d ((acc' p1 |:= e') x') (acc' p2) = @access d x' (acc' p2)) ->
  (forall p1 (e':exp d) x', @access d ((acc' p1 |:= e') x') (acc' p1) = Some e') ->
  forall (i:fin n),
    access (seqfor (fun j => assign (@acc' d (AryIdx (f j) a)) (e|[f j])) x) (@acc' d (AryIdx (f i) a)) = Some (e|[f i]).
Proof.
  induction n as [ | n' IHn ]; intros.
  - destruct i as [x0 Hx0]. exfalso. lia.
  - assert (Hseq := seqfor_Sn (fun j : fin (S n') => assign (@acc' d (AryIdx (f j) a)) (e|[f j]))).
    rewrite Hseq. unfold seq.
    destruct (fin_case i) as [[j Hj] | Hj].
    + rewrite Hj.
      assert (Hskip: @access d (assign (acc' (AryIdx (f '[n']) a)) (e|[f '[n']]) (seqfor (fun k : fin n' => assign (acc' (AryIdx (f FS[k]) a)) (e|[f FS[k]])) x)) (acc' (AryIdx (f (FS[j])) a)) = @access d (seqfor (fun k : fin n' => assign (acc' (AryIdx (f FS[k]) a)) (e|[f FS[k]])) x) (acc' (AryIdx (f (FS[j])) a))).
      { apply H0. intro Hcontra. apply AryIdx_eq in Hcontra. destruct Hcontra as [_ [H2 _]].
        apply fin2nat_inj in H2. apply H in H2. assert (Hn: n' = fin2nat j).
        { assert (H3: fin2nat '[n'] = fin2nat (FS[j])). { f_equal. auto. }
          unfold ltS in H3. rewrite fin2nat_exist in H3. rewrite fin2nat_fin2finS in H3. exact H3. }
        assert (Hj_lt: fin2nat j < n') by apply fin_correct. lia. }
      rewrite Hskip.
      change (access (seqfor (fun j0 : fin n' => assign (acc' (AryIdx ((fun k => f (FS[k])) j0) a)) (e|[(fun k => f (FS[k])) j0])) x) (acc' (AryIdx ((fun k => f (FS[k])) j) a)) = Some (e|[(fun k => f (FS[k])) j])).
      apply IHn.
      * intros j0 k Hneq. apply H in Hneq. apply fin2nat_inj. rewrite <- (fin2nat_fin2finS j0). rewrite <- (fin2nat_fin2finS k). f_equal. auto.
      * exact H0.
      * exact H1.
    + rewrite Hj.
      apply H1.
Qed.

Lemma access_seqfor_ary_neq_general :
  forall d (a1 a2:path) (x:env) (n m:nat) (f: fin n -> fin m) (e:vector (exp d) m),
  a1 <> a2 ->
  (forall j k, f j = f k -> j = k) ->
  (forall p1 p2 (e':exp d) x', p1 <> p2 -> @access d ((acc' p1 |:= e') x') (acc' p2) = @access d x' (acc' p2)) ->
  forall (i:fin m),
    access (seqfor (fun j => assign (@acc' d (AryIdx (f j) a1)) (e|[f j])) x) (@acc' d (AryIdx i a2)) = access x (@acc' d (AryIdx i a2)).
Proof.
  induction n as [ | n' IHn ]; intros.
  - simpl. reflexivity.
  - assert (Hseq := seqfor_Sn (fun j : fin (S n') => assign (@acc' d (AryIdx (f j) a1)) (e|[f j]))).
    rewrite Hseq. unfold seq.
    assert (Hskip: @access d (assign (acc' (AryIdx (f '[n']) a1)) (e|[f '[n']]) (seqfor (fun k : fin n' => assign (acc' (AryIdx (f FS[k]) a1)) (e|[f FS[k]])) x)) (acc' (AryIdx i a2)) = @access d (seqfor (fun k : fin n' => assign (acc' (AryIdx (f FS[k]) a1)) (e|[f FS[k]])) x) (acc' (AryIdx i a2))).
    { apply H1. intro Hcontra. apply H. apply AryIdx_eq in Hcontra. destruct Hcontra as [_ [_ H3]]. exact H3. }
    rewrite Hskip.
    apply IHn; auto.
    intros j0 k Hneq. assert (Hfs: FS[j0] = FS[k]).
    { apply H0 in Hneq. exact Hneq. }
    apply fin2nat_inj. rewrite <- (fin2nat_fin2finS j0). rewrite <- (fin2nat_fin2finS k). f_equal. exact Hfs.
Qed.

Lemma access_assign :forall d (a1 a2: path)(e:exp d)(x:env),
  access ((acc' a1 |:= e) x) (acc' a2) = 
  if a1=?a2 then Some e else access x (acc' a2).
Proof.
  induction d as [ | n m d1 IHd ]; simpl; intros; destruct (a1=?a2) eqn:E.
  - p_simpl. apply update_eq.
  - p_simpl. apply update_neq. auto.
  - (* ary, a1 = a2 *)
    assert (Ha: a1 = a2) by (apply path_eqb_eq; exact E).
    subst a2.
    remember (fle2nat m) as n0 eqn:Heq.
    destruct n0.
    + (* m = 0 *)
      destruct e. reflexivity.
    + (* m = S n0 *)
      assert (Hpt: forall i:fin (S n0),
        access (seqfor (fun j => assign (@idxAcc (S n0) d1 (mk_vec (fun i1 => acc' (AryIdx i1 a1))) j) (e|[j])) x)
               (@c_idx (S n0) d1 (mk_vec (fun i0 => acc' (AryIdx i0 a1))) i) = Some (e|[i])).
      { intro i.
        assert (Hc: @c_idx (S n0) d1 (mk_vec (fun i0 => acc' (AryIdx i0 a1))) i = acc' (AryIdx i a1)).
        { unfold c_idx. rewrite v_idx_mk_vec. reflexivity. }
        rewrite Hc.
        assert (Hseq: seqfor (fun j => assign (@idxAcc (S n0) d1 (mk_vec (fun i1 => acc' (AryIdx i1 a1))) j) (e|[j]))
                 = seqfor (fun j => assign (acc' (AryIdx j a1)) (e|[j]))).
        { apply seqfor_extensionality. intro j. unfold idxAcc. rewrite v_idx_mk_vec. reflexivity. }
        rewrite Hseq.
        apply access_seqfor_ary_eq_general with (f := fun j => j).
        { intros j k Hneq. exact Hneq. }
        { intros p1 p2 e' x' Hneq'.
          transitivity (if path_eqb p1 p2 then Some e' else @access d1 x' (acc' p2)).
          - exact (IHd p1 p2 e' x').
          - destruct (path_eqb p1 p2) eqn:Hb.
            + exfalso. apply path_eqb_eq in Hb. contradiction.
            + reflexivity. }
        { intros p1 e' x'.
          rewrite IHd.
          rewrite path_eqb_refl.
          reflexivity. } }
      rewrite mkoptvec_dependence with (u2 := liftf (fun i:fin (S n0) => e|[i])).
      * assert (Heq_vec: e = mk_vec (fun i:fin (S n0) => e|[i])).
        { apply vector_eq_v_idx with (x0 := exp_default d1). intro i.
          rewrite v_idx_mk_vec. reflexivity. }
        assert (Hmk: mkoptvec (liftf (fun i:fin (S n0) => e|[i])) = Some e).
        { transitivity (Some (mk_vec (fun i:fin (S n0) => e|[i]))).
          - apply mkoptvec_mk_vec.
          - f_equal. symmetry. apply Heq_vec. }
        apply Hmk.
      * intro i. unfold liftf. apply Hpt.
  - (* ary, a1 <> a2 *)
    assert (Hneq: a1 <> a2) by (apply path_eqb_neq; exact E).
    remember (fle2nat m) as n0 eqn:Heq.
    destruct n0.
    + (* m = 0 *)
      destruct e. reflexivity.
    + (* m = S n0 *)
      assert (Hpt: forall i:fin (S n0),
        access (seqfor (fun j => assign (@idxAcc (S n0) d1 (mk_vec (fun i1 => acc' (AryIdx i1 a1))) j) (e|[j])) x)
               (@c_idx (S n0) d1 (mk_vec (fun i0 => acc' (AryIdx i0 a2))) i) = access x (@c_idx (S n0) d1 (mk_vec (fun i0 => acc' (AryIdx i0 a2))) i)).
      { intro i.
        assert (Hc: @c_idx (S n0) d1 (mk_vec (fun i0 => acc' (AryIdx i0 a2))) i = acc' (AryIdx i a2)).
        { unfold c_idx. rewrite v_idx_mk_vec. reflexivity. }
        rewrite Hc at 1 2.
        assert (Hseq: seqfor (fun j => assign (@idxAcc (S n0) d1 (mk_vec (fun i1 => acc' (AryIdx i1 a1))) j) (e|[j]))
                 = seqfor (fun j => assign (acc' (AryIdx j a1)) (e|[j]))).
        { apply seqfor_extensionality. intro j. unfold idxAcc. rewrite v_idx_mk_vec. reflexivity. }
        rewrite Hseq.
        apply access_seqfor_ary_neq_general with (f := fun j => j).
        { exact Hneq. }
        { intros j k Hneq'. exact Hneq'. }
        { intros p1 p2 e' x' Hneq'.
          transitivity (if path_eqb p1 p2 then Some e' else @access d1 x' (acc' p2)).
          - exact (IHd p1 p2 e' x').
          - destruct (path_eqb p1 p2) eqn:Hb.
            + exfalso. apply path_eqb_eq in Hb. contradiction.
            + reflexivity. } }
      rewrite mkoptvec_dependence with (u2 := fun i:fin (S n0) => access x (@c_idx (S n0) d1 (mk_vec (fun i0 => acc' (AryIdx i0 a2))) i)).
      * reflexivity.
      * intro i. apply Hpt.
Qed.

(* access_assign_aux: seqfor assignment to distinct paths does not affect access to other paths. *)

Lemma access_assign_eq: forall d (a1:path) (a2:path) (e:exp d) (x:env),
  a1 = a2 ->
  access (((acc' a1)|:= e) x) (acc' a2) = Some e.
Proof.
  intros. subst. rewrite access_assign. rewrite path_eqb_refl. auto.
Qed.

Lemma access_assign_neq: forall d (a1:path) (a2:path) (e:exp d) (x:env), 
  a1<> a2 ->
  @access d (((acc' a1)|:= e) x) (acc' a2) = access x (acc' a2).
Proof.
  intros. rewrite access_assign. replace (a1 =? a2) with false.
  auto. symmetry. apply path_eqb_neq;auto.
Qed.


Lemma seqfor_comm_c: forall n (f:fin n -> comm) (g:comm),
  (forall i , f i '; g = g '; f i ) ->
  (forall i j , i <> j -> f i '; f j = f j '; f i ) ->
  seqfor f '; g = g '; seqfor f.
Proof.
  induction n;auto. intros.
  rewrite seqfor_Sn. rewrite <- seq_assoc. rewrite H.
  induction n;auto. rewrite IHn;auto.
  rewrite <- seq_assoc. f_equal. rewrite IHn;auto.
  intros. rewrite H0;f_simpl. assert(i<S n);f_simpl;try lia.
  intros. rewrite H0;auto. f_simpl.
  intros. rewrite seq_assoc. rewrite H.
  rewrite <- seq_assoc. rewrite H0;f_simpl.
  assert(i<S n);f_simpl;try lia.
  intros. rewrite H0;f_simpl.
Qed.

Lemma seqfor_comm: forall m n (f:fin m -> comm) (g: fin n -> comm),
  ( forall i j, f i '; g j = g j '; f i ) ->
  (forall i j , i <> j -> f i '; f j = f j '; f i ) ->
  (forall i j , i <> j -> g i '; g j = g j '; g i ) ->
  seqfor f '; seqfor g = seqfor g '; seqfor f.
Proof.
  induction m;auto. induction n;auto.
  intros. rewrite ?seqfor_Sn. 
  rewrite <- seq_assoc.
  rewrite seq_assoc with (c1:= f '[m]).
  rewrite <- seqfor_comm_c;intros;try apply H1;auto;f_simpl.
  rewrite <- seq_assoc. rewrite seq_assoc.
  rewrite IHm;intros;try apply H1;try apply H0;auto;f_simpl.
  rewrite <- ?seq_assoc. f_equal.
  rewrite seq_assoc with(c1:= g '[n]). 
  rewrite <- seqfor_comm_c;intros;try (apply H);try (apply H0);auto;f_simpl.
  rewrite <- seq_assoc. f_equal. apply H.
Qed.

Lemma seqfor_comm_single :
  forall n (f : fin n -> comm) (g : comm),
    (forall i, f i '; g = g '; f i) ->
    seqfor f '; g = g '; seqfor f.
Proof.
  induction n as [ | n' IHn ]; intros f g Hcomm.
  - reflexivity.
  - rewrite seqfor_Sn.
    rewrite <- seq_assoc.
    rewrite Hcomm.
    rewrite seq_assoc.
    rewrite IHn.
    + rewrite <- seq_assoc. reflexivity.
    + intros i. apply Hcomm.
Qed.

Lemma seqfor_shadow :
  forall n (f g : fin n -> comm),
    (forall i, f i '; g i = g i) ->
    (forall i j, i <> j -> f i '; g j = g j '; f i) ->
    (forall i j, i <> j -> g i '; g j = g j '; g i) ->
    seqfor f '; seqfor g = seqfor g.
Proof.
  induction n as [ | n' IHn ]; intros f g Hshadow Hfg Hg.
  - reflexivity.
  - fun_ext.
    rewrite !seqfor_Sn.
    rewrite <- seq_assoc.
    replace (f '[n'] '; (seqfor (fun i => g FS[i]) '; g '[n'])) with ((f '[n'] '; seqfor (fun i => g FS[i])) '; g '[n']).
    + replace (f '[n'] '; seqfor (fun i => g FS[i])) with (seqfor (fun i => g FS[i]) '; f '[n']).
      * rewrite <- seq_assoc.
        rewrite seq_assoc.
        assert (Heq: seqfor (fun i => f FS[i]) '; seqfor (fun i => g FS[i]) = seqfor (fun i => g FS[i])).
        { apply IHn.
          - intros i. apply Hshadow.
          - intros i j Hij. apply Hfg. intro Hcontra. apply Hij. apply fin2nat_inj.
            assert (H3: fin2nat (FS[i]) = fin2nat (FS[j])) by (f_equal; auto).
            rewrite !fin2nat_fin2finS in H3. exact H3.
          - intros i j Hij. apply Hg. intro Hcontra. apply Hij. apply fin2nat_inj.
            assert (H3: fin2nat (FS[i]) = fin2nat (FS[j])) by (f_equal; auto).
            rewrite !fin2nat_fin2finS in H3. exact H3. }
        rewrite Heq.
        rewrite Hshadow. reflexivity.
      * apply seqfor_comm_single.
        intros i. symmetry. apply Hfg. intro Hcontra.
        assert (H: fin2nat (ltS n') = n') by (unfold ltS; rewrite fin2nat_exist; auto).
        assert (H3: fin2nat (FS[i]) = n').
        { rewrite <- H. rewrite Hcontra. reflexivity. }
        rewrite fin2nat_fin2finS in H3.
        assert (H2: fin2nat i < n') by apply fin_correct.
        rewrite H3 in H2.
        apply Nat.lt_irrefl in H2. contradiction.
    + rewrite seq_assoc. reflexivity.
Qed.

Lemma assign_assign: forall d (a1 a2:path) (e1 e2:exp d),
  acc' a2|:= e2 '; acc' a1 |:= e1 = 
  if a1 =? a2 then acc' a1 |:= e1 
  else acc' a1|:= e1 '; acc' a2 |:= e2.
Proof.
  induction d as [ | n m d0 IHd ]; simpl; intros; destruct (a1=?a2)eqn:E.
  - unfold seq. fun_ext. p_simpl. apply update_shadow.
  - unfold seq. fun_ext. p_simpl. apply update_permute;auto.
  - (* a1 = a2, ary case *)
    assert (Ha: a1 = a2) by (apply path_eqb_eq; exact E).
    subst a2.
    repeat rewrite assign_ary.
    apply seqfor_shadow.
    + intros i. unfold idxAcc. simpl. rewrite v_idx_mk_vec.
      rewrite IHd. rewrite path_eqb_refl. reflexivity.
    + intros i j Hij.
      assert (Hneq: AryIdx i a1 <> AryIdx j a1).
      { intro H. apply Hij. apply AryIdx_eq in H. destruct H as [_ [H2 _]]. apply fin2nat_inj. exact H2. }
        unfold idxAcc. simpl. rewrite !v_idx_mk_vec.
      rewrite IHd.
      remember (path_eqb (AryIdx j a1) (AryIdx i a1)) as b eqn:Hb.
      destruct b.
      * exfalso. apply Hneq. symmetry in Hb. apply path_eqb_eq in Hb. symmetry. exact Hb.
      * reflexivity.
    + intros i j Hij.
      assert (Hneq: AryIdx i a1 <> AryIdx j a1).
      { intro H. apply Hij. apply AryIdx_eq in H. destruct H as [_ [H2 _]]. apply fin2nat_inj. exact H2. }
      unfold idxAcc. simpl. rewrite !v_idx_mk_vec.
      rewrite IHd.
      remember (path_eqb (AryIdx j a1) (AryIdx i a1)) as b eqn:Hb.
      destruct b.
      * exfalso. apply Hneq. symmetry in Hb. apply path_eqb_eq in Hb. symmetry. exact Hb.
      * reflexivity.
  - (* a1 <> a2, ary case *)
    assert (Hneq: a1 <> a2) by (apply path_eqb_neq; exact E).
    repeat rewrite assign_ary.
    apply seqfor_comm.
    + intros i j.
      assert (Hneq': AryIdx i a2 <> AryIdx j a1).
      { intro H. apply Hneq. apply AryIdx_eq in H. destruct H as [_ [_ H3]]. symmetry. exact H3. }
      unfold idxAcc. simpl. rewrite !v_idx_mk_vec.
      rewrite IHd.
      remember (path_eqb (AryIdx j a1) (AryIdx i a2)) as b eqn:Hb.
      destruct b.
      * exfalso. apply Hneq'. symmetry in Hb. apply path_eqb_eq in Hb. symmetry. exact Hb.
      * reflexivity.
    + intros i j Hij.
      assert (Hneq2: AryIdx i a2 <> AryIdx j a2).
      { intro H. apply Hij. apply AryIdx_eq in H. destruct H as [_ [H2 _]]. apply fin2nat_inj. exact H2. }
      unfold idxAcc. simpl. rewrite !v_idx_mk_vec.
      rewrite IHd.
      remember (path_eqb (AryIdx j a2) (AryIdx i a2)) as b eqn:Hb.
      destruct b.
      * exfalso. apply Hneq2. symmetry in Hb. apply path_eqb_eq in Hb. symmetry. exact Hb.
      * reflexivity.
    + intros i j Hij.
      assert (Hneq2: AryIdx i a1 <> AryIdx j a1).
      { intro H. apply Hij. apply AryIdx_eq in H. destruct H as [_ [H2 _]]. apply fin2nat_inj. exact H2. }
      unfold idxAcc. simpl. rewrite !v_idx_mk_vec.
      rewrite IHd.
      remember (path_eqb (AryIdx j a1) (AryIdx i a1)) as b eqn:Hb.
      destruct b.
      * exfalso. apply Hneq2. symmetry in Hb. apply path_eqb_eq in Hb. symmetry. exact Hb.
      * reflexivity.
Qed. 

Lemma assign_assign_eq: forall d (a1 a2:path) (e1 e2:exp d),
  a1 = a2 ->
  acc' a2 |:= e2 '; acc' a1 |:= e1  = 
  acc' a1 |:= e1 .
Proof.
  intros. subst. rewrite assign_assign. rewrite path_eqb_refl;auto.
Qed.

Lemma assign_assign_neq: forall d (a1 a2:path) (e1 e2:exp d),
  a1 <> a2 ->
  acc' a2 |:= e2 '; acc' a1 |:= e1  = 
  acc' a1 |:= e1 '; acc' a2 |:= e2 .
Proof.
  intros. rewrite assign_assign. replace (a1 =? a2) with false.
  auto. symmetry. apply path_eqb_neq;auto.
Qed.


(* 定义结构化数据类型的Undefined，变量a不在env中 *)
Definition Undefined_data{d}(a:acc d) (rho:env) : Prop :=
  access rho a = Some (exp_default d).

Lemma undefined_next: forall (d:data) (x: nat)(a: path) (rho: env),
  True -> True.
Proof. auto. Qed.

Lemma S_nat: forall x,
  (x =? S x)%nat = false.
Proof.
  intros. induction x. auto. simpl. auto.
Qed.


(* 已知eta: a[0] = exp_default d ,...,a[x-1] = exp_default d, a[x] = exp_default d.
   目标：(a[0] = v[0], ..., a[x-1] = v[x-1], rho) a[x] = exp_default d. *)


Lemma undefined_Sx: forall (d:data) (x n: nat)(a: path) (rho: env)(v: vector (exp d) x)(e: exp d),
  True -> True.
Proof. auto. Qed.



(* StructUndefined: a variable and all its sub-elements are None in rho *)
Fixpoint StructUndefined {d} (a : acc d) (rho : env) : Prop :=
  match d as d0 return acc d0 -> Prop with
  | num => fun a0 => rho a0 = None
  | @ary n m d1 => fun a0 => forall (i : fin m), @StructUndefined d1 (a0|{i}) rho
  end a.

(* in_acc: path p is in the leaf set of accessor a *)
Fixpoint in_acc {d} (p : path) (a : acc d) : Prop :=
  match d as d0 return acc d0 -> Prop with
  | num => fun a0 => a0 = p
  | @ary n m d1 => fun a0 => exists i : fin m, in_acc p (a0|{i})
  end a.

(* Pointwise characterization of for_rev and seqfor. *)
Lemma for_rev_pointwise : forall n (f : fin n -> comm) rho p,
  (forall i rho', f i rho' p = rho' p) ->
  for_rev f rho p = rho p.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl. transitivity (f (ltS n) rho p).
    + apply IHn. intros. apply H.
    + apply H.
Qed.

Lemma seqfor_pointwise : forall n (f : fin n -> comm) rho p,
  (forall i rho', f i rho' p = rho' p) ->
  seqfor f rho p = rho p.
Proof.
  induction n; intros.
  - reflexivity.
  - simpl.
    transitivity (seqfor (fun i : fin n => f FS[i]) rho p).
    + apply H.
    + apply IHn. intro i. apply H.
Qed.

(* If every f i either sets p to None or leaves it, then for_rev preserves None. *)
Lemma for_rev_preserves_None : forall n (f : fin n -> comm) rho p,
  rho p = None ->
  (forall i rho', f i rho' p = None \/ f i rho' p = rho' p) ->
  for_rev f rho p = None.
Proof.
  induction n; intros.
  - simpl. rewrite H. reflexivity.
  - simpl.
    assert (Hfs: f '[n] rho p = None).
    { destruct (H0 '[n] rho) as [Hfs | Hfs]; auto.
      rewrite Hfs. auto. }
    apply IHn; auto.
Qed.

Lemma fin_ne_ltS : forall n (i : fin (S n)), i <> ltS n -> fin2nat i <> n.
Proof.
  intros n i H Hc.
  apply H. apply fin_eq.
  simpl. unfold ltS. simpl.
  exact Hc.
Qed.
About fin_ne_ltS.

(* If some f i always sets p to None and others either set p to None or leave it,
   then seqfor sets p to None. *)
Lemma seqfor_preserves_None : forall n (f : fin n -> comm) rho p,
  rho p = None ->
  (forall i rho', f i rho' p = None \/ f i rho' p = rho' p) ->
  seqfor f rho p = None.
Proof.
  induction n; intros.
  - auto.
  - simpl. unfold seq.
    destruct (H0 (ltS n) (seqfor (fun i => f FS[i]) rho)) as [Hfs | Hfs].
    + exact Hfs.
    + rewrite Hfs.
      apply IHn.
      exact H.
      intros i eta0. apply H0.
Qed.

Lemma seqfor_pointwise_None : forall n (f : fin n -> comm) rho p,
  (exists i, forall rho', f i rho' p = None) ->
  (forall j rho', f j rho' p = None \/ f j rho' p = rho' p) ->
  seqfor f rho p = None.
Proof.
  induction n; intros.
  - exfalso. destruct H as [i _]. apply (fin0_empty i).
  - simpl. unfold seq.
    destruct H as [i Hi].
    destruct (fin_eq_dec i (ltS n)) as [E | E].
    + subst. apply Hi.
    + assert (Hj : exists j : fin n, i = FS[j]).
      { exists (finS2fin i (fin_ne_ltS E)).
        symmetry. apply finS2fin_fin2finS. }
      destruct Hj as [j Hj']. subst.
      assert (Hseq: seqfor (fun i : fin n => f FS[i]) rho p = None).
      { apply IHn.
        - exists j. intros. apply Hi.
        - intros j0 rho'. apply H0. }
      destruct (H0 (ltS n) (seqfor (fun i : fin n => f FS[i]) rho)) as [Hfs | Hfs]; auto.
      rewrite Hfs. auto.
Qed.

(* If some f i always sets p to None and others either set p to None or leave it,
   then for_rev sets p to None. *)
Lemma for_rev_pointwise_None : forall n (f : fin n -> comm) rho p,
  (exists i, forall rho', f i rho' p = None) ->
  (forall j rho', f j rho' p = None \/ f j rho' p = rho' p) ->
  for_rev f rho p = None.
Proof.
  induction n; intros.
  - exfalso. destruct H as [i _]. apply (fin0_empty i).
  - simpl.
    destruct H as [i Hi].
    destruct (fin_eq_dec i (ltS n)) as [E | E].
    + subst. apply for_rev_preserves_None.
      * apply Hi.
      * intro j. apply H0.
    + assert (Hj : exists j : fin n, i = FS[j]).
      { exists (finS2fin i (fin_ne_ltS E)).
        symmetry. apply finS2fin_fin2finS. }
      destruct Hj as [j Hj']. subst.
      apply IHn.
      * exists j. intros. apply Hi.
      * intros j0 rho'. apply H0.
Qed.

Lemma StructUndefined_num : forall (a : path) rho,
  @StructUndefined num a rho <-> rho a = None.
Proof. intros. simpl. reflexivity. Qed.

(* vrm only affects paths in its subtree: if p is not in a, vrm leaves p unchanged. *)
Lemma vrm_not_in_acc : forall d (a : acc d) rho p,
  ~ in_acc p a -> vrm a rho p = rho p.
Proof.
  induction d; simpl; intros.
  - unfold remove. destruct (path_eqb a p) eqn:E.
    + apply path_eqb_eq in E. subst. exfalso. auto.
    + reflexivity.
  - apply seqfor_pointwise. intro i. intro rho'.
    apply (IHd (a|{i}) rho' p).
    intro Hc. apply H. exists i. auto.
Qed.

(* If p is in a's subtree, vrm sets p to None. *)
Lemma vrm_in_acc : forall d (a : acc d) rho p,
  in_acc p a -> vrm a rho p = None.
Proof.
  induction d; simpl; intros.
  - subst. unfold remove. rewrite path_eqb_refl. reflexivity.
  - destruct H as [i Hi].
    apply seqfor_pointwise_None.
    + exists i. intros rho'. apply IHd. apply Hi.
    + intros j rho'. destruct (classic (in_acc p (a|{j}))) as [Hj | Hj].
      * left. apply IHd. auto.
      * right. apply vrm_not_in_acc. auto.
Qed.

(* assign only affects paths in its subtree. *)
Lemma assign_not_in_acc : forall d (a : acc d) e rho p,
  ~ in_acc p a -> assign a e rho p = rho p.
Proof.
  induction d; simpl; intros.
  - unfold update. destruct (path_eqb a p) eqn:E.
    + apply path_eqb_eq in E. subst. exfalso. auto.
    + reflexivity.
  - apply seqfor_pointwise. intro i. intro rho'.
    apply (IHd (a|{i}) (e|[i]) rho' p).
    intro Hc. apply H. exists i. auto.
Qed.
About assign_not_in_acc.

(* StructUndefined means every leaf path is None. *)
Lemma StructUndefined_implies_None : forall d (a : acc d) rho p,
  StructUndefined a rho -> in_acc p a -> rho p = None.
Proof.
  induction d; simpl; intros.
  - subst. auto.
  - destruct H0 as [i Hi].
    eapply IHd; [| apply Hi].
    apply H.
Qed.

(* vrm_id: if all sub-elements are None, then vrm is identity. *)
Lemma vrm_id : forall d (a : acc d) rho,
  StructUndefined a rho ->
  vrm a rho = rho.
Proof.
  induction d; simpl; intros.
  - unfold remove. apply functional_extensionality. intro p.
    destruct (path_eqb a p) eqn:E.
    + apply path_eqb_eq in E. subst. auto.
    + reflexivity.
  - apply functional_extensionality. intro p.
    destruct (classic (@in_acc (ary f d) p a)) as [Hp | Hp].
    + destruct Hp as [i Hi].
      assert (rho p = None) by (eapply (StructUndefined_implies_None _ _ _ _ _ Hi); simpl; exact H).
      rewrite H0.
      apply seqfor_pointwise_None.
      * exists i. intros rho'. apply (vrm_in_acc _ _ _ _ Hi).
      * intros j rho'. destruct (classic (@in_acc d p (a|{j}))) as [Hj | Hj].
        -- left. apply (vrm_in_acc _ _ _ _ Hj).
        -- right. apply (vrm_not_in_acc _ _ _ _ Hj).
    + apply seqfor_pointwise. intro i. intro rho'.
      apply (vrm_not_in_acc _ _ _ _).
      intro Hc. apply Hp. exists i. exact Hc.
  Unshelve. all: apply H.
Qed.

(* vrm_assign: if variable a and all sub-elements are initially None,
   then assigning e to a and then removing a yields the original rho. *)
Lemma vrm_assign: forall d (a:path) (e:exp d) eta,
  @StructUndefined d (acc' a) eta ->
  (acc' a |:= e '; @vrm d (acc' a)) eta = eta.
Proof.
  induction d; simpl; intros.
  - unfold seq. rewrite remove_update_same.
    apply functional_extensionality. intro p.
    unfold remove. destruct (path_eqb a p) eqn:E.
    + apply path_eqb_eq in E. subst. apply StructUndefined_num in H. auto.
    + reflexivity.
  - apply functional_extensionality. intro p.
    destruct (classic (exists i : fin (fle2nat f), @in_acc d p (acc' (AryIdx i a)))) as [Hex | Hnex].
    + assert (eta p = None).
      { destruct Hex as [i Hi].
        eapply StructUndefined_implies_None; [| apply Hi].
        assert (H' : @StructUndefined d (@acc' d (AryIdx i a)) eta).
        { replace (@StructUndefined d (@acc' d (AryIdx i a)) eta)
            with (@StructUndefined d (idxAcc (mk_vec (fun j => @acc' d (AryIdx j a))) i) eta).
          - apply (H i).
          - f_equal. simpl. rewrite <- (v_idx_mk_vec i (fun j => @acc' d (AryIdx j a)) (acc_default d)). reflexivity. }
        apply H'. }
      rewrite H0.
      cbn [vrm assign]. unfold seq.
      assert (Hidx : forall j, idxAcc (mk_vec (fun k => @acc' d (@AryIdx (@fle2nat n f) k a))) j = @acc' d (@AryIdx (@fle2nat n f) j a))
        by (intros j0; simpl; rewrite <- (v_idx_mk_vec j0 (fun k => @acc' d (@AryIdx (@fle2nat n f) k a)) (acc_default d)); reflexivity).
      apply seqfor_pointwise_None.
      * destruct Hex as [i0 Hi0].
        rewrite <- (Hidx i0) in Hi0.
        exists i0. intros eta'. apply (vrm_in_acc _ _ _ _ Hi0).
      * intros j eta'. destruct (classic (@in_acc d p (acc' (@AryIdx (fle2nat f) j a)))) as [Hj | Hj].
        -- left.
           replace (idxAcc (mk_vec (fun k => @acc' d (@AryIdx (fle2nat f) k a))) j) with (@acc' d (@AryIdx (fle2nat f) j a))
             by (symmetry; simpl; rewrite <- (v_idx_mk_vec j (fun k => @acc' d (@AryIdx (fle2nat f) k a)) (acc_default d)); reflexivity).
           apply (vrm_in_acc _ _ _ _ Hj).
        -- right.
           replace (idxAcc (mk_vec (fun k => @acc' d (@AryIdx (fle2nat f) k a))) j) with (@acc' d (@AryIdx (fle2nat f) j a))
             by (symmetry; simpl; rewrite <- (v_idx_mk_vec j (fun k => @acc' d (@AryIdx (fle2nat f) k a)) (acc_default d)); reflexivity).
           replace (idxAcc (mk_vec (fun k => @acc' d (@AryIdx (fle2nat f) k a))) j) with (@acc' d (@AryIdx (fle2nat f) j a)) in Hj
             by (symmetry; simpl; rewrite <- (v_idx_mk_vec j (fun k => @acc' d (@AryIdx (fle2nat f) k a)) (acc_default d)); reflexivity).
           apply (vrm_not_in_acc _ _ _ _ Hj).
    + cbn [vrm assign]. unfold seq.
      assert (Hinner: seqfor (fun i => assign (idxAcc (acc' a) i) (e|[i])) eta p = eta p).
      { apply seqfor_pointwise. intro i. intro eta'.
        apply (assign_not_in_acc d (idxAcc (acc' a) i) (e|[i]) eta' p).
        intro Hc.
        rewrite idxAcc_acc'_eq in Hc.
        apply Hnex. exists i. exact Hc. }
      rewrite <- Hinner.
      apply seqfor_pointwise. intro i. intro eta'.
      apply (vrm_not_in_acc d (idxAcc (acc' a) i) eta' p).
      intro Hc.
      rewrite idxAcc_acc'_eq in Hc.
      apply Hnex. exists i. exact Hc.
Qed.
  

(* Lemma env_undefined: forall d (a:path)(rho:env)(c:comm),
  @Undefined_data d (acc' a) rho  ->
  @Undefined_data d (acc' a) (c rho).
Proof.
  induction d. intros. simpl. 
Abort. *)



Lemma vrm_access_c: forall d (a:path) (e:exp d) (rho:env)(c:comm),
  @StructUndefined d (acc' a) rho ->
  @StructUndefined d (acc' a) (c rho) ->
  (forall p, ~@in_acc d p (acc' a) -> c rho p = rho p) ->
  (forall p eta, ~@in_acc d p (acc' a) -> eta p = rho p -> c eta p = rho p) ->
  (acc' a |:= e '; c '; @vrm d (acc' a)) rho = c rho.
Proof.
  induction d; simpl; intros.
  - apply functional_extensionality. intro p.
    destruct (a =? p) eqn:E.
    + apply path_eqb_eq in E. subst.
      simpl in H, H0.
      unfold seq, remove.
      assert (path_eqb p p = true) by apply path_eqb_refl.
      rewrite H3. symmetry. rewrite H0. reflexivity.
    + assert (Hne : a <> p) by (apply path_eqb_neq; exact E).
      unfold remove.
      destruct (path_eqb a p) eqn:E2.
      * exfalso. apply path_eqb_eq in E2. contradiction.
      * assert (Hup: update rho a e p = rho p).
        { unfold update. rewrite E2. reflexivity. }
        unfold seq, remove.
        rewrite E2. simpl.
        assert (Hc1: c (update rho a e) p = rho p) by (apply H2; [exact Hne | exact Hup]).
        assert (Hc2: c rho p = rho p) by (apply H1; exact Hne).
        rewrite Hc1. rewrite Hc2. reflexivity.
  - apply functional_extensionality. intro p.
    destruct (classic (exists i : fin (fle2nat f), @in_acc d p (acc' (AryIdx i a)))) as [Hex | Hnex].
    + assert (Hnone: c rho p = None).
      { destruct Hex as [i Hi].
        eapply StructUndefined_implies_None; [| apply Hi].
        assert (H' : @StructUndefined d (@acc' d (AryIdx i a)) (c rho)).
        { replace (@StructUndefined d (@acc' d (AryIdx i a)) (c rho))
            with (@StructUndefined d (idxAcc (mk_vec (fun j => @acc' d (AryIdx j a))) i) (c rho)).
          - apply (H0 i).
          - f_equal. simpl. rewrite <- (v_idx_mk_vec i (fun j => @acc' d (AryIdx j a)) (acc_default d)). reflexivity. }
        apply H'. }
      rewrite Hnone.
      cbn [vrm assign]. unfold seq.
      assert (Hidx : forall j, idxAcc (mk_vec (fun k => @acc' d (@AryIdx (@fle2nat n f) k a))) j = @acc' d (@AryIdx (@fle2nat n f) j a))
        by (intros j0; simpl; rewrite <- (v_idx_mk_vec j0 (fun k => @acc' d (@AryIdx (@fle2nat n f) k a)) (acc_default d)); reflexivity).
      apply seqfor_pointwise_None.
      * destruct Hex as [i0 Hi0].
        rewrite <- (Hidx i0) in Hi0.
        exists i0. intros eta'. apply (vrm_in_acc _ _ _ _ Hi0).
      * intros j eta'. destruct (classic (@in_acc d p (acc' (@AryIdx (fle2nat f) j a)))) as [Hj | Hj].
        -- left.
           replace (idxAcc (mk_vec (fun k => @acc' d (@AryIdx (fle2nat f) k a))) j) with (@acc' d (@AryIdx (fle2nat f) j a))
             by (symmetry; simpl; rewrite <- (v_idx_mk_vec j (fun k => @acc' d (@AryIdx (fle2nat f) k a)) (acc_default d)); reflexivity).
           apply (vrm_in_acc _ _ _ _ Hj).
        -- right.
           replace (idxAcc (mk_vec (fun k => @acc' d (@AryIdx (fle2nat f) k a))) j) with (@acc' d (@AryIdx (fle2nat f) j a))
             by (symmetry; simpl; rewrite <- (v_idx_mk_vec j (fun k => @acc' d (@AryIdx (fle2nat f) k a)) (acc_default d)); reflexivity).
           replace (idxAcc (mk_vec (fun k => @acc' d (@AryIdx (fle2nat f) k a))) j) with (@acc' d (@AryIdx (fle2nat f) j a)) in Hj
             by (symmetry; simpl; rewrite <- (v_idx_mk_vec j (fun k => @acc' d (@AryIdx (fle2nat f) k a)) (acc_default d)); reflexivity).
           apply (vrm_not_in_acc _ _ _ _ Hj).
    + assert (Hassign: @assign (ary f d) (acc' a) e rho p = rho p).
      { assert (Heq: @assign (ary f d) (acc' a) e = seqfor (fun i => assign (@acc' d (AryIdx i a)) (e|[i]))).
        { cbn [assign]. apply seqfor_extensionality. intro i.
          f_equal.
          assert (Hacc: @acc' (ary f d) a = mk_vec (fun k => @acc' d (AryIdx k a))). { apply acc'_ary. }
          rewrite Hacc.
          simpl. rewrite <- (v_idx_mk_vec i (fun k => @acc' d (AryIdx k a)) (acc_default d)). reflexivity. }
        rewrite Heq. unfold seq.
        apply seqfor_pointwise. intro i. intro eta'.
        apply (assign_not_in_acc d (@acc' d (AryIdx i a)) (e|[i]) eta' p).
        intro Hc. apply Hnex. exists i. exact Hc. }
      assert (Hcrho: c rho p = rho p).
      { apply H1. intro Hc. apply Hnex.
        destruct Hc as [i Hi].
        exists i. rewrite <- idxAcc_acc'_eq. exact Hi. }
      assert (Hcassign: c (@assign (ary f d) (acc' a) e rho) p = rho p).
      { apply H2. intro Hc. apply Hnex.
        destruct Hc as [i Hi].
        exists i. rewrite <- idxAcc_acc'_eq. exact Hi.
        rewrite Hassign. reflexivity. }
      unfold seq.
      cbn [vrm].
      transitivity (c (@assign (ary f d) (acc' a) e rho) p).
      { apply seqfor_pointwise. intro i. intro eta'.
        apply (vrm_not_in_acc d (@idxAcc (@fle2nat n f) d (acc' a) i) eta' p).
        intro Hc.
        rewrite idxAcc_acc'_eq in Hc.
        apply Hnex. exists i. exact Hc. }
      { rewrite Hcassign, Hcrho. reflexivity. }
Qed.








