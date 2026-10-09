(* Route-A migration of the pointwise (elementwise) operators from
   Ionia.CNN_OP (lines 127-145, 167-236) to the R-based Proof_CodeGen model.

   Each operator comes as a triple:
   - a functional definition ([mkvSeq] + [idx] + Coq [bool] conditions),
   - an imperative counterpart ([*_comm], [seqfor] / [mkvSeql] style),
   - a Leibniz equivalence lemma [A_<op>] proved with the DPIA rewrite
     rules from Ionia.DPIA_Rules (all closed with [Qed]).

   All array accesses use the explicit [idx]/[idxAcc] functions, following
   Ionia.LeNet5_Functional / Ionia.LeNet5_Imperative, to avoid the [|]
   keyword conflict with the safe-indexing [match] in Ionia.LeNet5_Utils. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* ReLU4d (batch dimension; 4 nested mkvSeq)                                   *)
(* -------------------------------------------------------------------------- *)

Definition ReLU4d {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      if leExp (idx (idx (idx (idx input b) c) i) j) zero
        then zero
        else idx (idx (idx (idx input b) c) i) j)))).

Definition ReLU4d_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      If (leExp (idx (idx (idx (idx input b) c) i) j) zero)
        (idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:= zero)
        (idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
          idx (idx (idx (idx input b) c) i) j))))).

Lemma A_ReLU4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, ReLU4d input) = ReLU4d_comm input output.
Proof.
  intros. unfold ReLU4d, ReLU4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Sigmoid2d / Sigmoid4d : 1 / (1 + exp(-x))                                   *)
(* -------------------------------------------------------------------------- *)

Definition Sigmoid2d {m1 m2 : nat}
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    div one (add one (pExp (negate (idx (idx input i) j)))))).

Definition Sigmoid2d_comm {m1 m2 : nat}
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:=
      div one (add one (pExp (negate (idx (idx input i) j)))))).

Lemma A_Sigmoid2d : forall (m1 m2 : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Sigmoid2d input) = Sigmoid2d_comm input output.
Proof.
  intros. unfold Sigmoid2d, Sigmoid2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Sigmoid4d {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      div one (add one (pExp (negate (idx (idx (idx (idx input b) c) i) j)))))))).

Definition Sigmoid4d_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        div one (add one (pExp (negate (idx (idx (idx (idx input b) c) i) j)))))))).

Lemma A_Sigmoid4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, Sigmoid4d input) = Sigmoid4d_comm input output.
Proof.
  intros. unfold Sigmoid4d, Sigmoid4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tanh2d / Tanh4d : (exp x - exp(-x)) / (exp x + exp(-x))                     *)
(* -------------------------------------------------------------------------- *)

Definition Tanh2d {m1 m2 : nat}
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    div (sub (pExp (idx (idx input i) j)) (pExp (negate (idx (idx input i) j))))
        (add (pExp (idx (idx input i) j)) (pExp (negate (idx (idx input i) j)))))).

Definition Tanh2d_comm {m1 m2 : nat}
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:=
      div (sub (pExp (idx (idx input i) j)) (pExp (negate (idx (idx input i) j))))
          (add (pExp (idx (idx input i) j)) (pExp (negate (idx (idx input i) j)))))).

Lemma A_Tanh2d : forall (m1 m2 : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Tanh2d input) = Tanh2d_comm input output.
Proof.
  intros. unfold Tanh2d, Tanh2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Tanh4d {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      div (sub (pExp (idx (idx (idx (idx input b) c) i) j))
               (pExp (negate (idx (idx (idx (idx input b) c) i) j))))
          (add (pExp (idx (idx (idx (idx input b) c) i) j))
               (pExp (negate (idx (idx (idx (idx input b) c) i) j)))))))).

Definition Tanh4d_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        div (sub (pExp (idx (idx (idx (idx input b) c) i) j))
                 (pExp (negate (idx (idx (idx (idx input b) c) i) j))))
            (add (pExp (idx (idx (idx (idx input b) c) i) j))
                 (pExp (negate (idx (idx (idx (idx input b) c) i) j)))))))).

Lemma A_Tanh4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, Tanh4d input) = Tanh4d_comm input output.
Proof.
  intros. unfold Tanh4d, Tanh4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* LeakyReLU4d : x > 0 ? x : slope * x                                         *)
(* -------------------------------------------------------------------------- *)

Definition LeakyReLU4d {batch channel m1 m2 : nat}
  (negative_slope : exp num)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      if gtExp (idx (idx (idx (idx input b) c) i) j) zero
        then idx (idx (idx (idx input b) c) i) j
        else mul negative_slope (idx (idx (idx (idx input b) c) i) j))))).

Definition LeakyReLU4d_comm {batch channel m1 m2 : nat}
  (negative_slope : exp num)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      If (gtExp (idx (idx (idx (idx input b) c) i) j) zero)
        (idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
          idx (idx (idx (idx input b) c) i) j)
        (idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
          mul negative_slope (idx (idx (idx (idx input b) c) i) j)))))).

Lemma A_LeakyReLU4d : forall (batch channel m1 m2 : nat)
  (negative_slope : exp num)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, LeakyReLU4d negative_slope input) =
    LeakyReLU4d_comm negative_slope input output.
Proof.
  intros. unfold LeakyReLU4d, LeakyReLU4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Binary pointwise: Add2d / Add3d / Add4d / Sub2d / Mul2d                     *)
(* -------------------------------------------------------------------------- *)

Definition Add2d {m1 m2 : nat}
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    add (idx (idx x i) j) (idx (idx y i) j))).

Definition Add2d_comm {m1 m2 : nat}
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:= add (idx (idx x i) j) (idx (idx y i) j))).

Lemma A_Add2d : forall (m1 m2 : nat)
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Add2d x y) = Add2d_comm x y output.
Proof.
  intros. unfold Add2d, Add2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Sub2d {m1 m2 : nat}
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    sub (idx (idx x i) j) (idx (idx y i) j))).

Definition Sub2d_comm {m1 m2 : nat}
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:= sub (idx (idx x i) j) (idx (idx y i) j))).

Lemma A_Sub2d : forall (m1 m2 : nat)
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Sub2d x y) = Sub2d_comm x y output.
Proof.
  intros. unfold Sub2d, Sub2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Mul2d {m1 m2 : nat}
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    mul (idx (idx x i) j) (idx (idx y i) j))).

Definition Mul2d_comm {m1 m2 : nat}
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:= mul (idx (idx x i) j) (idx (idx y i) j))).

Lemma A_Mul2d : forall (m1 m2 : nat)
  (x : exp (ary '{m1} (ary '{m2} num)))
  (y : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Mul2d x y) = Mul2d_comm x y output.
Proof.
  intros. unfold Mul2d, Mul2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Add3d {channel m1 m2 : nat}
  (x : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (y : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{channel} (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun c : fin channel => mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    add (idx (idx (idx x c) i) j) (idx (idx (idx y c) i) j)))).

Definition Add3d_comm {channel m1 m2 : nat}
  (x : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (y : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{channel} (ary '{m1} (ary '{m2} num)))) : comm :=
  seqfor (fun c : fin channel => seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc (idxAcc output c) i) j |:=
      add (idx (idx (idx x c) i) j) (idx (idx (idx y c) i) j)))).

Lemma A_Add3d : forall (channel m1 m2 : nat)
  (x : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (y : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{channel} (ary '{m1} (ary '{m2} num)))),
  A(output, Add3d x y) = Add3d_comm x y output.
Proof.
  intros. unfold Add3d, Add3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Add4d {batch channel m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      add (idx (idx (idx (idx x b) c) i) j)
          (idx (idx (idx (idx y b) c) i) j))))).

Definition Add4d_comm {batch channel m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        add (idx (idx (idx (idx x b) c) i) j)
            (idx (idx (idx (idx y b) c) i) j))))).

Lemma A_Add4d : forall (batch channel m1 m2 : nat)
  (x : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, Add4d x y) = Add4d_comm x y output.
Proof.
  intros. unfold Add4d, Add4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scalar pointwise: Addc2d / Mulc2d                                           *)
(* -------------------------------------------------------------------------- *)

Definition Addc2d {m1 m2 : nat} (e : exp num)
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    add (idx (idx input i) j) e)).

Definition Addc2d_comm {m1 m2 : nat} (e : exp num)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:= add (idx (idx input i) j) e)).

Lemma A_Addc2d : forall (m1 m2 : nat) (e : exp num)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Addc2d e input) = Addc2d_comm e input output.
Proof.
  intros. unfold Addc2d, Addc2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

Definition Mulc2d {m1 m2 : nat} (v : exp num)
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    mul (idx (idx input i) j) v)).

Definition Mulc2d_comm {m1 m2 : nat} (v : exp num)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:= mul (idx (idx input i) j) v)).

Lemma A_Mulc2d : forall (m1 m2 : nat) (v : exp num)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Mulc2d v input) = Mulc2d_comm v input output.
Proof.
  intros. unfold Mulc2d, Mulc2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Exp2d : pointwise pExp                                                      *)
(* -------------------------------------------------------------------------- *)

Definition Exp2d {m1 m2 : nat}
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
    pExp (idx (idx input i) j))).

Definition Exp2d_comm {m1 m2 : nat}
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
    idxAcc (idxAcc output i) j |:= pExp (idx (idx input i) j))).

Lemma A_Exp2d : forall (m1 m2 : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, Exp2d input) = Exp2d_comm input output.
Proof.
  intros. unfold Exp2d, Exp2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Fill2d : constant fill (input array ignored, as in the legacy definition)   *)
(* -------------------------------------------------------------------------- *)

Definition Fill2d {batch m : nat} (e : exp num)
  (input : exp (ary '{batch} (ary '{m} num)))
  : exp (ary '{batch} (ary '{m} num)) :=
  mkvSeq (fun i : fin batch => mkvSeq (fun j : fin m => e)).

Definition Fill2d_comm {batch m : nat} (e : exp num)
  (input : exp (ary '{batch} (ary '{m} num)))
  (output : acc (ary '{batch} (ary '{m} num))) : comm :=
  seqfor (fun i : fin batch => seqfor (fun j : fin m =>
    idxAcc (idxAcc output i) j |:= e)).

Lemma A_Fill2d : forall (batch m : nat) (e : exp num)
  (input : exp (ary '{batch} (ary '{m} num)))
  (output : acc (ary '{batch} (ary '{m} num))),
  A(output, Fill2d e input) = Fill2d_comm e input output.
Proof.
  intros. unfold Fill2d, Fill2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.
