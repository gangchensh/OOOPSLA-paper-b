From Stdlib Require Import Reals String Nat List Bool Arith Lra.
Require Export DataExp.
Open Scope string_scope.
Set Implicit Arguments.

(* ======================= Tensor Types ======================= *)

Definition Tensor1 (m : nat) := exp (ary '{m} num).
Definition Tensor2 (m n : nat) := exp (ary '{m} (ary '{n} num)).
Definition Tensor3 (m n p : nat) := exp (ary '{m} (ary '{n} (ary '{p} num))).
Definition Tensor4 (m n p q : nat) := exp (ary '{m} (ary '{n} (ary '{p} (ary '{q} num)))).

Definition mkTensor1 (m:nat) : Tensor1 m :=
  mk_vec (fun _ => REconst R0 "0").

Definition mkTensor2 (m1 m2:nat) : Tensor2 m1 m2 :=
  mk_vec (fun _ => mkTensor1 m2).

Definition mkTensor3 (channel m1 m2:nat) : Tensor3 channel m1 m2 :=
  mk_vec (fun _ => mkTensor2 m1 m2).

Definition mkTensor4 (batch channel m1 m2:nat) : Tensor4 batch channel m1 m2 :=
  mk_vec (fun _ => mkTensor3 channel m1 m2).

(* ======================= Scalar Operations ======================= *)

Definition zero : exp num := REconst R0 "0".
Arguments zero : simpl never.
Definition one : exp num := REconst R1 "1".
Arguments one : simpl never.
Definition negate (x: exp num) : exp num := REopp x.
Definition add (x y: exp num) : exp num := REadd x y.
Definition mul (x y: exp num) : exp num := REmul x y.
Definition scal (r: R) (x: exp num) : exp num := REscal r x.
Definition div (x y: exp num) : exp num := REdiv x y.
Definition div_n (x: exp num) (n :nat) : exp num := REdiv_n x n.
Definition sub (x y: exp num) : exp num := REsub x y.
Definition pow (x: exp num) (n :nat) : exp num := REpow x n.
Definition log (x:exp num) : exp num := REln x.

(* Boolean expression constructors.  The type [bexp] and its static evaluator
   [bexp2bool] now live in [DataExp]; they are re-exported here for
   convenience. *)
Definition leExp (x y : exp num) : bexp := BLe x y.
Definition gtExp (x y : exp num) : bexp := BGt x y.
Arguments leExp : simpl never.
Arguments gtExp : simpl never.

(* Runtime-conditional maximum over a vector of real expressions.  The result
   is an [REif] expression that, when evaluated in an environment, selects the
   actual maximum element according to that environment. *)
Fixpoint v_max_bexp {n : nat} (f : rexp -> rexp -> bexp) (init_val : rexp)
  : vector rexp n -> rexp :=
  match n with
  | O => fun (v : vector rexp 0) => init_val
  | S n' => fun (v : vector rexp (S n')) =>
            REif (f (snd v) (v_max_bexp f init_val (fst v)))
                 (snd v)
                 (v_max_bexp f init_val (fst v))
  end.

Definition pExp (x: exp num) : exp num := REexp x.

Definition sqrt (x:exp num) : exp num := REsqrt x.

(* ======================= Let Binding ======================= *)

Definition let_binding {s t} (e: exp s)(f:exp s -> exp t) : exp t := f e.

(* ======================================================================== *)
(* Runtime-safe indexing with explicit Nat.ltb_spec0 boundary check.
   Used when a static fin proof is not available (e.g. arithmetic expressions
   whose safety depends on implicit CNN preconditions, or dynamic indices). *)
Definition safe_idx_nat {n t} (e : exp (ary '{n} t)) (i : nat) : exp t :=
  match Nat.ltb_spec0 i n with
  | ReflectT _ H_lt => e|[nat2fin H_lt]
  | ReflectF _ _ => exp_default t
  end.
Arguments safe_idx_nat {n t} e i.

(* When the index is known to be in bounds, safe_idx_nat reduces to ordinary idx.
   This is the primary rewrite rule for code generation: after proving the bound
   from CNN preconditions, safe_idx_nat disappears and CGidx applies directly. *)
Lemma safe_idx_nat_lt : forall {n t} (e : exp (ary '{n} t)) (i : nat) (H : i < n),
  safe_idx_nat e i = e|[nat2fin H].
Proof.
  intros. unfold safe_idx_nat.
  destruct (Nat.ltb_spec0 i n) as [H1|H1].
  - f_equal. apply fin_eq. rewrite fin2nat_nat2fin. auto.
  - contradiction.
Qed.
(* ======================================================================== *)

(* ======================= Array Reshape ======================= *)

Definition join {t:data} {n m:nat} (e: exp (ary '{m} (ary '{n} t))) 
  : exp (ary '{(m*n)} t) := v_join (exp_default t) e.

Definition split {t:data} {n m:nat} (e:exp (ary '{(m*n)} t))
  : exp (ary '{m} (ary '{n} t)) := v_split (exp_default t) e.

Definition concat {d m n} (e1: exp (ary '{m} d)) (e2: exp (ary '{n} d))
  : exp (ary '{(m+n)} d) := mkvSeq (fun i : fin (m + n) =>
    if bexp2bool (BLt (fin2nat i) m) then safe_idx_nat e1 (fin2nat i)
    else safe_idx_nat e2 (fin2nat i - m)).

(* ======================= Padding & Truncation ======================= *)

Definition padl {d n} (k : nat) (e: exp (ary '{n} d))
  : exp (ary '{(k+n)} d) := mkvSeq (fun i : fin (k + n) =>
    if bexp2bool (BLt (fin2nat i) k) then (exp_default d)
    else safe_idx_nat e (fin2nat i - k)).

Definition padr {d n} (k : nat) (e: exp (ary '{n} d))
  : exp (ary '{(n+k)} d) := mkvSeq (fun i : fin (n + k) =>
    if bexp2bool (BLt (fin2nat i) n) then safe_idx_nat e (fin2nat i)
    else (exp_default d)).

Definition truncl {d n} (k : nat) (e: exp (ary '{n} d))
  (H_le : k <= n) : exp (ary '{k} d) := @v_truncl (exp d) n (exp_default d) k H_le e.

Definition truncr {d n} (k : nat) (e: exp (ary '{n} d))
  (H_le : k <= n) : exp (ary '{k} d) := @v_truncr (exp d) n (exp_default d) k H_le e.

(* ======================= Transpose ======================= *)

Definition trans {d m n} (e: exp (ary '{m} (ary '{n} d))) 
  : exp (ary '{n} (ary '{m} d)) := v_trans (exp_default d) e.

(* ======================= Notations & Parameters ======================= *)

Notation "'tlet' x ':=' e 'in' y" := (let_binding e (fun x => y)) (at level 81).

Parameter rand : exp num.

(* ======================= Array Reduction ======================= *)

Definition reduce {n:nat} {s t:data}
  (f: exp s -> exp t -> exp t) (a:exp t) (v:exp (ary '{n} s)) : exp t :=
  v_reduce f a v.

Definition sum {n:nat} (e : exp (ary '{n} num)) : exp num :=
  v_reduce add zero e.

Definition max {n:nat} (e : exp (ary '{n} num)) : exp num := v_max_bexp gtExp zero e.
