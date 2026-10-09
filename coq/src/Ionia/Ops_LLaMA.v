(* DPIA-style Leibniz equivalence proofs for the modern LLM component
   operators (milestone N3a of the NLP/LLM extension, cf.
   doc/NLP与LLM扩展开发规划_20260911.md §2-N3) in the route-A R-based
   expression model.

   Operators delivered (functional definition + imperative counterpart
   [*_comm] + Leibniz equality [A_*], all closed with [Qed]):

   - RMSNorm2d/3d: root-mean-square normalisation
     y_j = x_j / sqrt(mean_i(x_i^2) + eps) * gamma_j.
     Simpler than LayerNorm (Ionia.Ops_Transformer): no mean centring, so a
     single [suml] reduction per row suffices; the per-element cell
     [A_RMScell] is a direct [C_sum_post_acc] instance (the one-reduction
     special case of [A_LNcell]).

   - SwiGLU2d/3d: the gated FFN component Swish(xW) * (xV) on the two
     already-projected inputs, with Swish(x) = x * sigmoid(x).  The scalar
     rules [A_sigmoid1] / [A_swish] are reflexivity-shaped like [A_pExp];
     the array lemmas follow the pointwise template of Ionia.Ops_Elementwise.
     (The projections xW / xV themselves are the already-proved
     [Linear2d] / [MatMul2d].)

   - RoPE1d/3d: rotary position embedding.  sin/cos enter as the new scalar
     functions [sinE] / [cosE] wrapping the standard reals' [sin] / [cos],
     with reflexivity-shaped rules [A_sinE] / [A_cosE] exactly as [A_sqrt]
     (Ionia.Ops_BatchNorm) wraps [Rsqrt].  The rotation angle is
     theta(pos, i) = pos * base^(-2i/d), d = 2*half, expressed with [Rpower].
     The pair rotation reads the (2i, 2i+1) dimension pair through the
     [idx_1d_to_2d] / [idx_2d_to_1d] index pair of the SplitHeads family:
     output index x decomposes as (pair, component), the component selects
     the two rotation formulas
       y_{2i}   = x_{2i} cos th_i - x_{2i+1} sin th_i
       y_{2i+1} = x_{2i} sin th_i + x_{2i+1} cos th_i
     with the component test on the Coq [bool] level (via [fin2nat] +
     [Nat.eqb]) and [Aif1], as in [CausalMask2d].  The per-element cell
     [A_rope_cell] is shared by the 1d and the batched 3d forms.

   - GQAExpand: grouped-query attention KV-head sharing.  Query head hh of
     h = hk * g reads KV head hh / g (the [fst] of [idx_1d_to_2d], i.e. the
     contiguous-group map) — the Gather family pattern with a pure fin/fin
     index map, broadcast from (b, hk, s, d) to (b, hk*g, s, d).

   Small-instance computation checks close the file (symbolic base/eps
   parameters where possible, to keep normalisation cheap), followed by the
   axiom audit. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Scalar functions: sigmoid / Swish / sin / cos                               *)
(* -------------------------------------------------------------------------- *)

Definition sigmoid1 (x : exp num) : exp num :=
  div one (add one (pExp (negate x))).

(* Swish(x) = x * sigmoid(x), the gate of SwiGLU. *)
Definition swish (x : exp num) : exp num := mul x (sigmoid1 x).

(* Trigonometric scalars for RoPE, wrapping the standard reals' [sin]/[cos]
   the way [Proof_CodeGen.sqrt] wraps [Rsqrt]. *)
Definition sinE (x : exp num) : exp num := sin x.

Definition cosE (x : exp num) : exp num := cos x.

(* Reflexivity-shaped scalar rules, modelled on [A_pExp] / [A_sqrt]. *)
Lemma A_sigmoid1 : forall (a : acc num) (e : exp num),
  A(a, sigmoid1 e) = C(e, fun r => a |:= sigmoid1 r).
Proof. reflexivity. Qed.

Lemma A_swish : forall (a : acc num) (e : exp num),
  A(a, swish e) = C(e, fun r => a |:= swish r).
Proof. reflexivity. Qed.

Lemma A_sinE : forall (a : acc num) (e : exp num),
  A(a, sinE e) = C(e, fun r => a |:= sinE r).
Proof. reflexivity. Qed.

Lemma A_cosE : forall (a : acc num) (e : exp num),
  A(a, cosE e) = C(e, fun r => a |:= cosE r).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* RMSNorm (no mean centring: one reduction per row)                          *)
(* -------------------------------------------------------------------------- *)

(* Summand array of the mean of squares: elementwise squares. *)
Definition RMSsqSum {d : nat} (v : exp (ary '{d} num))
  : exp (ary '{d} num) :=
  mkvSeq (fun i : fin d => mul (idx v i) (idx v i)).

(* Single normalised element: x / sqrt(ms + eps) * gamma, where [ms] is the
   mean of squares over the row. *)
Definition RMScell (x ms gamma eps : exp num) : exp num :=
  mul (div x (sqrt (add ms eps))) gamma.

(* Per-element cell: the mean-of-squares sum is computed on the element
   accumulator itself; the single-reduction case of [A_LNcell]
   (Ionia.Ops_Transformer), via [C_sum_post_acc]. *)
Lemma A_RMScell : forall (d : nat) (v : exp (ary '{d} num))
  (x gamma eps : exp num) (o : acc num),
  A(o, RMScell x (div (sum (RMSsqSum v)) (INR d)) gamma eps)
  = suml (RMSsqSum v)
         (fun r => o |:= RMScell x (div r (INR d)) gamma eps) o.
Proof.
  intros.
  replace (A(o, RMScell x (div (sum (RMSsqSum v)) (INR d)) gamma eps))
    with (C(sum (RMSsqSum v),
            fun r => o |:= RMScell x (div r (INR d)) gamma eps))
    by reflexivity.
  rewrite C_sum_post_acc. reflexivity.
Qed.

(* RMSNorm2d (n x d, normalisation over the last axis). *)
Definition RMSNorm2d {n d : nat}
  (input : exp (ary '{n} (ary '{d} num)))
  (gamma : exp (ary '{d} num))
  (eps : exp num)
  : exp (ary '{n} (ary '{d} num)) :=
  mkvSeq (fun i : fin n => mkvSeq (fun j : fin d =>
    RMScell (idx (idx input i) j)
            (div (sum (RMSsqSum (idx input i))) (INR d))
            (idx gamma j) eps)).

Definition RMSNorm2d_comm {n d : nat}
  (input : exp (ary '{n} (ary '{d} num)))
  (gamma : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{n} (ary '{d} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (RMSsqSum (idx input i)) (fun r =>
      oj |:= RMScell (idx (idx input i) j) (div r (INR d))
                     (idx gamma j) eps) oj) oi) output.

Lemma A_RMSNorm2d : forall (n d : nat)
  (input : exp (ary '{n} (ary '{d} num)))
  (gamma : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{n} (ary '{d} num))),
  A(output, RMSNorm2d input gamma eps)
  = RMSNorm2d_comm input gamma eps output.
Proof.
  intros. unfold RMSNorm2d, RMSNorm2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_RMScell. reflexivity.
Qed.

(* RMSNorm3d (b x s x d, normalisation over the last axis; the LLaMA block
   form, mirroring [LayerNorm3d]). *)
Definition RMSNorm3d {b s d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (gamma : exp (ary '{d} num))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{d} num))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s => mkvSeq (fun j : fin d =>
    RMScell (idx (idx (idx input bb) ss) j)
            (div (sum (RMSsqSum (idx (idx input bb) ss))) (INR d))
            (idx gamma j) eps))).

Definition RMSNorm3d_comm {b s d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (gamma : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun ss os => mkvSeql (fun j oj =>
    suml (RMSsqSum (idx (idx input bb) ss)) (fun r =>
      oj |:= RMScell (idx (idx (idx input bb) ss) j) (div r (INR d))
                     (idx gamma j) eps) oj) os) ob) output.

Lemma A_RMSNorm3d : forall (b s d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (gamma : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))),
  A(output, RMSNorm3d input gamma eps)
  = RMSNorm3d_comm input gamma eps output.
Proof.
  intros. unfold RMSNorm3d, RMSNorm3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_RMScell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* SwiGLU (gated FFN component on the projected inputs)                       *)
(* -------------------------------------------------------------------------- *)

Definition SwiGLU2d {n d : nat}
  (u v : exp (ary '{n} (ary '{d} num)))
  : exp (ary '{n} (ary '{d} num)) :=
  mkvSeq (fun i : fin n => mkvSeq (fun j : fin d =>
    mul (swish (idx (idx u i) j)) (idx (idx v i) j))).

Definition SwiGLU2d_comm {n d : nat}
  (u v : exp (ary '{n} (ary '{d} num)))
  (output : acc (ary '{n} (ary '{d} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    oj |:= mul (swish (idx (idx u i) j)) (idx (idx v i) j)) oi) output.

Lemma A_SwiGLU2d : forall (n d : nat)
  (u v : exp (ary '{n} (ary '{d} num)))
  (output : acc (ary '{n} (ary '{d} num))),
  A(output, SwiGLU2d u v) = SwiGLU2d_comm u v output.
Proof.
  intros. unfold SwiGLU2d, SwiGLU2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* Batched form (b x s x d), the LLaMA block shape. *)
Definition SwiGLU3d {b s d : nat}
  (u v : exp (ary '{b} (ary '{s} (ary '{d} num))))
  : exp (ary '{b} (ary '{s} (ary '{d} num))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s => mkvSeq (fun j : fin d =>
    mul (swish (idx (idx (idx u bb) ss) j))
        (idx (idx (idx v bb) ss) j)))).

Definition SwiGLU3d_comm {b s d : nat}
  (u v : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun ss os => mkvSeql (fun j oj =>
    oj |:= mul (swish (idx (idx (idx u bb) ss) j))
               (idx (idx (idx v bb) ss) j)) os) ob) output.

Lemma A_SwiGLU3d : forall (b s d : nat)
  (u v : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))),
  A(output, SwiGLU3d u v) = SwiGLU3d_comm u v output.
Proof.
  intros. unfold SwiGLU3d, SwiGLU3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* RoPE (rotary position embedding)                                           *)
(* -------------------------------------------------------------------------- *)

(* The two components of a rotated pair. *)
Definition rope_c0 : fin 2 := @nat2fin 2 0 (ltac:(lia)).
Definition rope_c1 : fin 2 := @nat2fin 2 1 (ltac:(lia)).

(* Rotation angle theta(pos, i) = pos * base^(-2i/d) with d = 2*half. *)
Definition rope_theta (base : exp num) (half : nat) (pos : nat)
  (i : fin half) : exp num :=
  mul (INR pos)
      (Rpower base (negate (div (INR (2 * fin2nat i)%nat)
                                (INR (2 * half)%nat)))).

(* One rotated element: output index [x] of the length-(half*2) vector
   decomposes as (pair i, component c) via [idx_1d_to_2d]; component 0 and 1
   carry the two rotation formulas. *)
Definition rope_cell (base : exp num) (half pos : nat)
  (v : exp (ary '{half * 2} num)) (x : fin (half * 2)) : exp num :=
  if (fin2nat (snd (idx_1d_to_2d x)) =? 0)%nat
    then sub (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c0))
                  (cosE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x)))))
             (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c1))
                  (sinE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x)))))
    else add (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c0))
                  (sinE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x)))))
             (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c1))
                  (cosE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x))))).

Definition rope_cell_comm (base : exp num) (half pos : nat)
  (v : exp (ary '{half * 2} num)) (x : fin (half * 2)) (o : acc num) : comm :=
  If (fin2nat (snd (idx_1d_to_2d x)) =? 0)%nat
    (o |:= sub (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c0))
                    (cosE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x)))))
               (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c1))
                    (sinE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x))))))
    (o |:= add (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c0))
                    (sinE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x)))))
               (mul (idx v (idx_2d_to_1d (fst (idx_1d_to_2d x)) rope_c1))
                    (cosE (rope_theta (half:=half) base pos (fst (idx_1d_to_2d x)))))).

(* Per-element cell: the component test is a Coq [bool], so [Aif1] +
   [A_num] close it, as in [A_CausalMask2d]. *)
Lemma A_rope_cell : forall (base : exp num) (half pos : nat)
  (v : exp (ary '{half * 2} num)) (x : fin (half * 2)) (o : acc num),
  A(o, rope_cell base half pos v x) = rope_cell_comm base half pos v x o.
Proof.
  intros. unfold rope_cell, rope_cell_comm.
  rewrite Aif1. rewrite !A_num.
  reflexivity.
Qed.

(* RoPE1d: one length-(half*2) head-dimension vector at position [pos]. *)
Definition RoPE1d {half : nat} (base : exp num) (pos : nat)
  (input : exp (ary '{half * 2} num)) : exp (ary '{half * 2} num) :=
  mkvSeq (fun x : fin (half * 2) => rope_cell base half pos input x).

Definition RoPE1d_comm {half : nat} (base : exp num) (pos : nat)
  (input : exp (ary '{half * 2} num))
  (output : acc (ary '{half * 2} num)) : comm :=
  mkvSeql (fun x ox => rope_cell_comm base half pos input x ox) output.

Lemma A_RoPE1d : forall (half : nat) (base : exp num) (pos : nat)
  (input : exp (ary '{half * 2} num))
  (output : acc (ary '{half * 2} num)),
  A(output, RoPE1d base pos input) = RoPE1d_comm base pos input output.
Proof.
  intros. unfold RoPE1d, RoPE1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro x.
  rewrite A_rope_cell. reflexivity.
Qed.

(* RoPE3d: the batched form (b x s x half*2); the position of a token is its
   sequence index [ss]. *)
Definition RoPE3d {b s half : nat} (base : exp num)
  (input : exp (ary '{b} (ary '{s} (ary '{half * 2} num))))
  : exp (ary '{b} (ary '{s} (ary '{half * 2} num))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s =>
    mkvSeq (fun x : fin (half * 2) =>
      rope_cell base half (fin2nat ss) (idx (idx input bb) ss) x))).

Definition RoPE3d_comm {b s half : nat} (base : exp num)
  (input : exp (ary '{b} (ary '{s} (ary '{half * 2} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{half * 2} num)))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun ss os => mkvSeql (fun x ox =>
    rope_cell_comm base half (fin2nat ss) (idx (idx input bb) ss) x ox)
      os) ob) output.

Lemma A_RoPE3d : forall (b s half : nat) (base : exp num)
  (input : exp (ary '{b} (ary '{s} (ary '{half * 2} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{half * 2} num)))),
  A(output, RoPE3d base input) = RoPE3d_comm base input output.
Proof.
  intros. unfold RoPE3d, RoPE3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro x.
  rewrite A_rope_cell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* GQA (grouped-query attention): KV-head sharing                             *)
(* -------------------------------------------------------------------------- *)

(* Broadcast the (b, hk, s, d) KV tensor to (b, hk*g, s, d): query head hh
   of the h = hk*g heads reads KV head hh / g (the contiguous-group map,
   [fst] of [idx_1d_to_2d]). *)
Definition GQAExpand {b hk g s d : nat}
  (kv : exp (ary '{b} (ary '{hk} (ary '{s} (ary '{d} num)))))
  : exp (ary '{b} (ary '{hk * g} (ary '{s} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin (hk * g) =>
    mkvSeq (fun ss : fin s => mkvSeq (fun dd : fin d =>
      idx (idx (idx (idx kv bb) (fst (idx_1d_to_2d hh))) ss) dd)))).

Definition GQAExpand_comm {b hk g s d : nat}
  (kv : exp (ary '{b} (ary '{hk} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{hk * g} (ary '{s} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh => mkvSeql (fun ss os =>
    mkvSeql (fun dd od =>
      od |:= idx (idx (idx (idx kv bb) (fst (idx_1d_to_2d hh))) ss) dd)
      os) oh) ob) output.

Lemma A_GQAExpand : forall (b hk g s d : nat)
  (kv : exp (ary '{b} (ary '{hk} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{hk * g} (ary '{s} (ary '{d} num))))),
  A(output, GQAExpand kv) = GQAExpand_comm kv output.
Proof.
  intros. unfold GQAExpand, GQAExpand_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro dd.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Small-instance computation checks                                          *)
(* -------------------------------------------------------------------------- *)

Definition ll_i0_1 : fin 1 := @nat2fin 1 0 (ltac:(lia)).
Definition ll_i0_2 : fin 2 := @nat2fin 2 0 (ltac:(lia)).
Definition ll_i1_2 : fin 2 := @nat2fin 2 1 (ltac:(lia)).
Definition ll_i2_3 : fin 3 := @nat2fin 3 2 (ltac:(lia)).
Definition ll_i2_4 : fin 4 := @nat2fin 4 2 (ltac:(lia)).
Definition ll_i3_4 : fin 4 := @nat2fin 4 3 (ltac:(lia)).

(* 2x2 test matrix, entry (i,j) = 2i + j + 1. *)
Definition X2 : exp (ary '{2} (ary '{2} num)) :=
  mkvSeq (fun i : fin 2 => mkvSeq (fun j : fin 2 =>
    (INR (2 * fin2nat i + fin2nat j + 1)%nat : exp num))).

(* RMSNorm, row 0 = [1, 2]: element (0,1) normalises x = 2 against the mean
   of squares of its row. *)
Example check_rmsnorm2d_cell : forall (gamma : exp (ary '{2} num))
  (eps : exp num),
  idx (idx (RMSNorm2d X2 gamma eps) ll_i0_2) ll_i1_2
  = RMScell (INR 2) (div (sum (RMSsqSum (idx X2 ll_i0_2))) (INR 2))
            (idx gamma ll_i1_2) eps.
Proof. reflexivity. Qed.

(* Second 2x2 matrix, entry (i,j) = 10i + j. *)
Definition V2 : exp (ary '{2} (ary '{2} num)) :=
  mkvSeq (fun i : fin 2 => mkvSeq (fun j : fin 2 =>
    (INR (10 * fin2nat i + fin2nat j)%nat : exp num))).

(* SwiGLU at (1,0): swish(3) * 10. *)
Example check_swiglu2d_cell :
  idx (idx (SwiGLU2d X2 V2) ll_i1_2) ll_i0_2
  = mul (swish (INR 3)) (INR 10).
Proof. vm_compute. reflexivity. Qed.

(* Length-4 head vector (half = 2), entry x = x+1, i.e. [1, 2, 3, 4]. *)
Definition R4 : exp (ary '{2 * 2} num) :=
  mkvSeq (fun x : fin 4 => (INR (S (fin2nat x)) : exp num)).

(* RoPE, position 1, pair 1 (elements 2 and 3), component 0:
   x2 * cos(theta) - x3 * sin(theta). *)
Example check_rope_pair1_c0 : forall (base : exp num),
  idx (RoPE1d (half:=2) base 1 R4) ll_i2_4
  = sub (mul (INR 3) (cosE (rope_theta (half:=2) base 1 ll_i1_2)))
        (mul (INR 4) (sinE (rope_theta (half:=2) base 1 ll_i1_2))).
Proof. vm_compute. reflexivity. Qed.

(* Same pair, component 1: x2 * sin(theta) + x3 * cos(theta). *)
Example check_rope_pair1_c1 : forall (base : exp num),
  idx (RoPE1d (half:=2) base 1 R4) ll_i3_4
  = add (mul (INR 3) (sinE (rope_theta (half:=2) base 1 ll_i1_2)))
        (mul (INR 4) (cosE (rope_theta (half:=2) base 1 ll_i1_2))).
Proof. vm_compute. reflexivity. Qed.

(* GQA: hk = 2 KV heads, group size g = 2, so h = 4 query heads; query head
   3 belongs to group 1 and shares KV head 1.  Entry encoding:
   100*hh + 10*ss + dd, so head 1, row 2, col 1 gives 121. *)
Definition KV1232 : exp (ary '{1} (ary '{2} (ary '{3} (ary '{2} num)))) :=
  mkvSeq (fun bb : fin 1 => mkvSeq (fun hh : fin 2 =>
    mkvSeq (fun ss : fin 3 => mkvSeq (fun dd : fin 2 =>
      (INR (100 * fin2nat hh + 10 * fin2nat ss + fin2nat dd)%nat
        : exp num))))).

Example check_gqa_share :
  idx (idx (idx (idx (GQAExpand (g:=2) KV1232) ll_i0_1) ll_i3_4) ll_i2_3)
      ll_i1_2
  = INR 121.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_sigmoid1.
Print Assumptions A_swish.
Print Assumptions A_sinE.
Print Assumptions A_cosE.
Print Assumptions A_RMScell.
Print Assumptions A_RMSNorm2d.
Print Assumptions A_RMSNorm3d.
Print Assumptions A_SwiGLU2d.
Print Assumptions A_SwiGLU3d.
Print Assumptions A_rope_cell.
Print Assumptions A_RoPE1d.
Print Assumptions A_RoPE3d.
Print Assumptions A_GQAExpand.
