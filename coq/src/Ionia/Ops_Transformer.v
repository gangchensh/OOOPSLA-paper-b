(* DPIA-style Leibniz equivalence proofs for the Transformer operator batch
   (milestone T1 of the Transformer extension, cf.
   doc/Transformer扩展开发规划_20260829.md) in the route-A R-based expression
   model.

   Operators delivered (functional definition + imperative counterpart
   [*_comm] + Leibniz equality [A_*], all closed with [Qed]):
   - LayerNorm2d/3d (last-axis normalisation, the form used by the
     Transformer blocks of milestones T2/T3) and LayerNorm4d (per-position
     channel-axis normalisation of a batch x channel x h x w tensor);
     mean/variance are recomputed per element exactly as in BatchNorm
     (Ionia.Ops_BatchNorm), so the [BNcell] normalisation cell and the
     two-chained-reduction lemmas [C_sum_post2_acc] / [suml_cont_congr] are
     reused directly.
   - GELU4d: the tanh approximation 0.5*x*(1+tanh(sqrt(2/pi)*(x+0.044715*x^3))).
     The standard reals have no erf, so tanh is expressed through [pExp]/[div]
     (cf. Tanh2d in Ionia.Ops_Elementwise); the scalar rules [A_gelu_tanh] /
     [A_gelu] are reflexivity-shaped like [A_pExp] / [A_sqrt].
   - Gather1d/Gather2d: index-based table lookup
     [mkvSeq (fun i => table|[idxs i])]; the index map [idxs] is a fin/fin
     index expression (a pure Coq function), not an R-valued data vector.
   - Transpose2d / SplitHeads / MergeHeads: the index-permutation family for
     multi-head attention, (b, s, h*d) <-> (b, h, s, d), built on the
     [idx_2d_to_1d] / [idx_1d_to_2d] pair used by the Flatten family
     (Ionia.LeNet5_DPIA.A_Flatten3d, Ionia.AlexNet_DPIA.A_Flatten4d).
   - CausalMask2d/4d: [if j <= i then x else NEGINF] with the index comparison
     on the Coq [bool] level (via [fin2nat] + [Nat.leb]) and [Aif1].
     Route A has no infinity in [R]; [NEGINF] is the constant -1e30, which
     acts as "-infinity" for softmax masking purposes (exp(-1e30) = 0 in any
     floating-point realisation; inside the R-model it is simply a large
     negative constant).
   - MatMul2d: plain matrix product with the [suml] reduction skeleton.
     The batched [Linear2d] of Ionia.Ops_PoolPad already covers
     matrix-times-transposed-weight plus bias ([A_Linear2d], Qed);
     [Linear2d_as_MatMul2d] records the precise alias.

   All array accesses use the explicit [idx]/[idxAcc] functions (cf.
   Ionia.Ops_Elementwise). *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* Reduction chaining lemmas ([C_sum_post2_acc], [suml_cont_congr]) and the
   normalisation cell [BNcell]. *)
Require Import Ionia.Ops_BatchNorm.
(* [Linear2d] / [A_Linear2d] for the MatMul2d alias lemma. *)
Require Import Ionia.Ops_PoolPad.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* GELU (tanh approximation)                                                   *)
(* -------------------------------------------------------------------------- *)

(* tanh x = (exp x - exp(-x)) / (exp x + exp(-x)); the standard reals have no
   erf, so the tanh approximation is the only expressible route. *)
Definition gelu_tanh (x : exp num) : exp num :=
  div (sub (pExp x) (pExp (negate x)))
      (add (pExp x) (pExp (negate x))).

Definition gelu_half : exp num := div one (add one one).              (* 1/2 *)
Definition gelu_sqrt_2_pi : exp num := sqrt (div (add one one) PI).   (* sqrt(2/pi) *)
Definition gelu_cubic_coef : exp num := div (INR 44715) (INR 1000000). (* 0.044715 *)

(* gelu x = 0.5 * x * (1 + tanh (sqrt(2/pi) * (x + 0.044715 * x^3))). *)
Definition gelu (x : exp num) : exp num :=
  mul (mul gelu_half x)
      (add one
           (gelu_tanh (mul gelu_sqrt_2_pi
                           (add x (mul gelu_cubic_coef (mul (mul x x) x)))))).

(* Reflexivity-shaped scalar rules, modelled on [A_pExp] / [A_sqrt]. *)
Lemma A_gelu_tanh : forall (a : acc num) (e : exp num),
  A(a, gelu_tanh e) = C(e, fun r => a |:= gelu_tanh r).
Proof. reflexivity. Qed.

Lemma A_gelu : forall (a : acc num) (e : exp num),
  A(a, gelu e) = C(e, fun r => a |:= gelu r).
Proof. reflexivity. Qed.

Definition GELU4d {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      gelu (idx (idx (idx (idx input b) c) i) j))))).

Definition GELU4d_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        gelu (idx (idx (idx (idx input b) c) i) j))))).

Lemma A_GELU4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, GELU4d input) = GELU4d_comm input output.
Proof.
  intros. unfold GELU4d, GELU4d_comm.
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
(* LayerNorm building blocks (statistics over a single 1d axis)               *)
(* -------------------------------------------------------------------------- *)

(* Mean of a length-[d] vector. *)
Definition LNmean {d : nat} (v : exp (ary '{d} num)) : exp num :=
  div (sum v) (INR d).

(* Summand array for the variance: squared deviations from [mean]. *)
Definition LNvarSum {d : nat} (v : exp (ary '{d} num)) (mean : exp num)
  : exp (ary '{d} num) :=
  mkvSeq (fun i : fin d =>
    mul (sub (idx v i) mean) (sub (idx v i) mean)).

(* Variance of a length-[d] vector. *)
Definition LNvar {d : nat} (v : exp (ary '{d} num)) (mean : exp num) : exp num :=
  div (sum (LNvarSum v mean)) (INR d).

(* Per-element cell: variance sum and mean sum chained on the element
   accumulator itself; mirrors [A_BNcell] in Ionia.Ops_BatchNorm, with the
   mean reduction taken over the vector itself (no partial row sums). *)
Lemma A_LNcell : forall (d : nat) (v : exp (ary '{d} num))
  (x gamma beta eps : exp num) (o : acc num),
  A(o, BNcell x (LNmean v) (LNvar v (LNmean v)) gamma beta eps)
  = suml (LNvarSum v (LNmean v)) (fun sv =>
      suml v (fun sm =>
        o |:= BNcell x (div sm (INR d)) (div sv (INR d)) gamma beta eps) o) o.
Proof.
  intros.
  replace (A(o, BNcell x (LNmean v) (LNvar v (LNmean v)) gamma beta eps))
    with (C(sum (LNvarSum v (LNmean v)),
            fun sv => C(sum v,
                        fun sm => o |:= BNcell x (div sm (INR d))
                                                  (div sv (INR d))
                                                  gamma beta eps)))
    by reflexivity.
  rewrite C_sum_post2_acc.
  apply suml_cont_congr. intro sv.
  rewrite C_sum_post_acc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* LayerNorm2d (n x d, normalisation over the last axis)                       *)
(* -------------------------------------------------------------------------- *)

Definition LayerNorm2d {n d : nat}
  (input : exp (ary '{n} (ary '{d} num)))
  (gamma beta : exp (ary '{d} num))
  (eps : exp num)
  : exp (ary '{n} (ary '{d} num)) :=
  mkvSeq (fun i : fin n => mkvSeq (fun j : fin d =>
    BNcell (idx (idx input i) j)
           (LNmean (idx input i))
           (LNvar (idx input i) (LNmean (idx input i)))
           (idx gamma j) (idx beta j) eps)).

Definition LayerNorm2d_comm {n d : nat}
  (input : exp (ary '{n} (ary '{d} num)))
  (gamma beta : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{n} (ary '{d} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (LNvarSum (idx input i) (LNmean (idx input i))) (fun sv =>
      suml (idx input i) (fun sm =>
        oj |:= BNcell (idx (idx input i) j)
                      (div sm (INR d)) (div sv (INR d))
                      (idx gamma j) (idx beta j) eps) oj) oj) oi) output.

Lemma A_LayerNorm2d : forall (n d : nat)
  (input : exp (ary '{n} (ary '{d} num)))
  (gamma beta : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{n} (ary '{d} num))),
  A(output, LayerNorm2d input gamma beta eps)
  = LayerNorm2d_comm input gamma beta eps output.
Proof.
  intros. unfold LayerNorm2d, LayerNorm2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_LNcell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* LayerNorm3d (b x s x d, normalisation over the last axis; the Transformer   *)
(* block form)                                                                 *)
(* -------------------------------------------------------------------------- *)

Definition LayerNorm3d {b s d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (gamma beta : exp (ary '{d} num))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{d} num))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s => mkvSeq (fun j : fin d =>
    BNcell (idx (idx (idx input bb) ss) j)
           (LNmean (idx (idx input bb) ss))
           (LNvar (idx (idx input bb) ss) (LNmean (idx (idx input bb) ss)))
           (idx gamma j) (idx beta j) eps))).

Definition LayerNorm3d_comm {b s d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (gamma beta : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun ss os => mkvSeql (fun j oj =>
    suml (LNvarSum (idx (idx input bb) ss) (LNmean (idx (idx input bb) ss)))
         (fun sv =>
      suml (idx (idx input bb) ss) (fun sm =>
        oj |:= BNcell (idx (idx (idx input bb) ss) j)
                      (div sm (INR d)) (div sv (INR d))
                      (idx gamma j) (idx beta j) eps) oj) oj) os) ob) output.

Lemma A_LayerNorm3d : forall (b s d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (gamma beta : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))),
  A(output, LayerNorm3d input gamma beta eps)
  = LayerNorm3d_comm input gamma beta eps output.
Proof.
  intros. unfold LayerNorm3d, LayerNorm3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_LNcell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* LayerNorm4d (b x c x h x w, per-position normalisation over the channel     *)
(* axis)                                                                       *)
(* -------------------------------------------------------------------------- *)

(* The channel-axis vector at spatial position (b, i, j). *)
Definition LNchanVec {batch channel h w : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num)))))
  (b : fin batch) (i : fin h) (j : fin w) : exp (ary '{channel} num) :=
  mkvSeq (fun c : fin channel => idx (idx (idx (idx input b) c) i) j).

Definition LayerNorm4d {batch channel h w : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num)))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin h => mkvSeq (fun j : fin w =>
      BNcell (idx (idx (idx (idx input b) c) i) j)
             (LNmean (LNchanVec input b i j))
             (LNvar (LNchanVec input b i j) (LNmean (LNchanVec input b i j)))
             (idx gamma c) (idx beta c) eps)))).

Definition LayerNorm4d_comm {batch channel h w : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num)))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun c oc => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (LNvarSum (LNchanVec input b i j) (LNmean (LNchanVec input b i j)))
         (fun sv =>
      suml (LNchanVec input b i j) (fun sm =>
        oj |:= BNcell (idx (idx (idx (idx input b) c) i) j)
                      (div sm (INR channel)) (div sv (INR channel))
                      (idx gamma c) (idx beta c) eps) oj) oj) oi) oc) ob) output.

Lemma A_LayerNorm4d : forall (batch channel h w : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num)))))
  (gamma beta : exp (ary '{channel} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{channel} (ary '{h} (ary '{w} num))))),
  A(output, LayerNorm4d input gamma beta eps)
  = LayerNorm4d_comm input gamma beta eps output.
Proof.
  intros. unfold LayerNorm4d, LayerNorm4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_LNcell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Gather / Embedding (index-based table lookup)                               *)
(*                                                                             *)
(* The index map [idxs] is a pure fin/fin index expression: in the R-based     *)
(* route-A model the data elements are reals, so indices cannot be read from   *)
(* a data vector; embedding tables are indexed by a host-level index function. *)
(* -------------------------------------------------------------------------- *)

Definition Gather1d {v n : nat} (idxs : fin n -> fin v)
  (table : exp (ary '{v} num))
  : exp (ary '{n} num) :=
  mkvSeq (fun i : fin n => idx table (idxs i)).

Definition Gather1d_comm {v n : nat} (idxs : fin n -> fin v)
  (table : exp (ary '{v} num))
  (output : acc (ary '{n} num)) : comm :=
  mkvSeql (fun i oi => oi |:= idx table (idxs i)) output.

Lemma A_Gather1d : forall (v n : nat) (idxs : fin n -> fin v)
  (table : exp (ary '{v} num))
  (output : acc (ary '{n} num)),
  A(output, Gather1d idxs table) = Gather1d_comm idxs table output.
Proof.
  intros. unfold Gather1d, Gather1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_num.
  reflexivity.
Qed.

(* Token embedding: each index selects a length-[d] row of the table. *)
Definition Gather2d {v d n : nat} (idxs : fin n -> fin v)
  (table : exp (ary '{v} (ary '{d} num)))
  : exp (ary '{n} (ary '{d} num)) :=
  mkvSeq (fun i : fin n => mkvSeq (fun k : fin d =>
    idx (idx table (idxs i)) k)).

Definition Gather2d_comm {v d n : nat} (idxs : fin n -> fin v)
  (table : exp (ary '{v} (ary '{d} num)))
  (output : acc (ary '{n} (ary '{d} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun k ok =>
    ok |:= idx (idx table (idxs i)) k) oi) output.

Lemma A_Gather2d : forall (v d n : nat) (idxs : fin n -> fin v)
  (table : exp (ary '{v} (ary '{d} num)))
  (output : acc (ary '{n} (ary '{d} num))),
  A(output, Gather2d idxs table) = Gather2d_comm idxs table output.
Proof.
  intros. unfold Gather2d, Gather2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro k.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Transpose / head reshape (index permutations of the Flatten family)         *)
(* -------------------------------------------------------------------------- *)

Definition Transpose2d {m n : nat}
  (input : exp (ary '{m} (ary '{n} num)))
  : exp (ary '{n} (ary '{m} num)) :=
  mkvSeq (fun j : fin n => mkvSeq (fun i : fin m => idx (idx input i) j)).

Definition Transpose2d_comm {m n : nat}
  (input : exp (ary '{m} (ary '{n} num)))
  (output : acc (ary '{n} (ary '{m} num))) : comm :=
  mkvSeql (fun j oj => mkvSeql (fun i oi =>
    oi |:= idx (idx input i) j) oj) output.

Lemma A_Transpose2d : forall (m n : nat)
  (input : exp (ary '{m} (ary '{n} num)))
  (output : acc (ary '{n} (ary '{m} num))),
  A(output, Transpose2d input) = Transpose2d_comm input output.
Proof.
  intros. unfold Transpose2d, Transpose2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_num.
  reflexivity.
Qed.

(* Multi-head split: (b, s, h*d) -> (b, h, s, d).  The merged feature index is
   [idx_2d_to_1d hh dd = hh * d + dd], the same pairing used by [join]/[split]
   and the Flatten family. *)
Definition SplitHeads {batch seqlen heads dim : nat}
  (input : exp (ary '{batch} (ary '{seqlen} (ary '{heads * dim} num))))
  : exp (ary '{batch} (ary '{heads} (ary '{seqlen} (ary '{dim} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun hh : fin heads =>
    mkvSeq (fun ss : fin seqlen => mkvSeq (fun dd : fin dim =>
      idx (idx (idx input b) ss) (idx_2d_to_1d hh dd))))).

Definition SplitHeads_comm {batch seqlen heads dim : nat}
  (input : exp (ary '{batch} (ary '{seqlen} (ary '{heads * dim} num))))
  (output : acc (ary '{batch} (ary '{heads} (ary '{seqlen} (ary '{dim} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun hh oh => mkvSeql (fun ss os => mkvSeql (fun dd od =>
    od |:= idx (idx (idx input b) ss) (idx_2d_to_1d hh dd)) os) oh) ob) output.

Lemma A_SplitHeads : forall (batch seqlen heads dim : nat)
  (input : exp (ary '{batch} (ary '{seqlen} (ary '{heads * dim} num))))
  (output : acc (ary '{batch} (ary '{heads} (ary '{seqlen} (ary '{dim} num))))),
  A(output, SplitHeads input) = SplitHeads_comm input output.
Proof.
  intros. unfold SplitHeads, SplitHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro dd.
  rewrite A_num.
  reflexivity.
Qed.

(* Inverse merge: (b, h, s, d) -> (b, s, h*d), using [idx_1d_to_2d] to
   decompose the merged feature index. *)
Definition MergeHeads {batch seqlen heads dim : nat}
  (input : exp (ary '{batch} (ary '{heads} (ary '{seqlen} (ary '{dim} num)))))
  : exp (ary '{batch} (ary '{seqlen} (ary '{heads * dim} num))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun ss : fin seqlen =>
    mkvSeq (fun x : fin (heads * dim) =>
      idx (idx (idx (idx input b) (fst (idx_1d_to_2d x))) ss)
              (snd (idx_1d_to_2d x))))).

Definition MergeHeads_comm {batch seqlen heads dim : nat}
  (input : exp (ary '{batch} (ary '{heads} (ary '{seqlen} (ary '{dim} num)))))
  (output : acc (ary '{batch} (ary '{seqlen} (ary '{heads * dim} num)))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun ss os => mkvSeql (fun x ox =>
    ox |:= idx (idx (idx (idx input b) (fst (idx_1d_to_2d x))) ss)
               (snd (idx_1d_to_2d x))) os) ob) output.

Lemma A_MergeHeads : forall (batch seqlen heads dim : nat)
  (input : exp (ary '{batch} (ary '{heads} (ary '{seqlen} (ary '{dim} num)))))
  (output : acc (ary '{batch} (ary '{seqlen} (ary '{heads * dim} num)))),
  A(output, MergeHeads input) = MergeHeads_comm input output.
Proof.
  intros. unfold MergeHeads, MergeHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro x.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Causal mask                                                                 *)
(* -------------------------------------------------------------------------- *)

(* Stand-in for -infinity: the route-A reals have no infinite element, so the
   mask writes the constant -1e30.  For the softmax that consumes the masked
   scores this behaves as -inf (exp(-1e30) underflows to 0 in any
   floating-point realisation); within the R-model it is simply a very large
   negative constant. *)
Definition NEGINF : exp num := negate (INR (10 ^ 30)%nat).

(* Causal (lower-triangular) mask on an s x s score matrix:
   position (i, j) keeps the score iff j <= i. *)
Definition CausalMask2d {s : nat}
  (input : exp (ary '{s} (ary '{s} num)))
  : exp (ary '{s} (ary '{s} num)) :=
  mkvSeq (fun i : fin s => mkvSeq (fun j : fin s =>
    if (fin2nat j <=? fin2nat i)%nat
      then idx (idx input i) j
      else NEGINF)).

Definition CausalMask2d_comm {s : nat}
  (input : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{s} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    If (fin2nat j <=? fin2nat i)%nat
       (oj |:= idx (idx input i) j)
       (oj |:= NEGINF)) oi) output.

Lemma A_CausalMask2d : forall (s : nat)
  (input : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{s} num))),
  A(output, CausalMask2d input) = CausalMask2d_comm input output.
Proof.
  intros. unfold CausalMask2d, CausalMask2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

(* Batched multi-head form: (b, h, s, s), mask on the last two axes. *)
Definition CausalMask4d {batch heads s : nat}
  (input : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))))
  : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun hh : fin heads =>
    mkvSeq (fun i : fin s => mkvSeq (fun j : fin s =>
      if (fin2nat j <=? fin2nat i)%nat
        then idx (idx (idx (idx input b) hh) i) j
        else NEGINF)))).

Definition CausalMask4d_comm {batch heads s : nat}
  (input : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))))
  (output : acc (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun hh oh => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    If (fin2nat j <=? fin2nat i)%nat
       (oj |:= idx (idx (idx (idx input b) hh) i) j)
       (oj |:= NEGINF)) oi) oh) ob) output.

Lemma A_CausalMask4d : forall (batch heads s : nat)
  (input : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))))
  (output : acc (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num))))),
  A(output, CausalMask4d input) = CausalMask4d_comm input output.
Proof.
  intros. unfold CausalMask4d, CausalMask4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* MatMul2d (plain matrix product)                                             *)
(* -------------------------------------------------------------------------- *)

Definition MatMul2d {m n p : nat}
  (a : exp (ary '{m} (ary '{n} num)))
  (b : exp (ary '{n} (ary '{p} num)))
  : exp (ary '{m} (ary '{p} num)) :=
  mkvSeq (fun i : fin m => mkvSeq (fun j : fin p =>
    sum (mkvSeq (fun k : fin n => mul (idx (idx a i) k) (idx (idx b k) j))))).

Definition MatMul2d_comm {m n p : nat}
  (a : exp (ary '{m} (ary '{n} num)))
  (b : exp (ary '{n} (ary '{p} num)))
  (output : acc (ary '{m} (ary '{p} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (mkvSeq (fun k : fin n => mul (idx (idx a i) k) (idx (idx b k) j)))
         (fun r => oj |:= r)
         oj) oi) output.

Lemma A_MatMul2d : forall (m n p : nat)
  (a : exp (ary '{m} (ary '{n} num)))
  (b : exp (ary '{n} (ary '{p} num)))
  (output : acc (ary '{m} (ary '{p} num))),
  A(output, MatMul2d a b) = MatMul2d_comm a b output.
Proof.
  intros. unfold MatMul2d, MatMul2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* Alias: the batched [Linear2d] of Ionia.Ops_PoolPad (whose [A_Linear2d] is
   already proved) is matrix multiplication against the transposed weight
   matrix plus the per-unit bias. *)
Lemma Linear2d_as_MatMul2d : forall (batch m outnum : nat)
  (Hb : batch > 0) (Hm : m > 0) (Ho : outnum > 0)
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{batch} (ary '{m} num))),
  Ops_PoolPad.Linear2d w bias input =
  mkvSeq (fun b : fin batch => mkvSeq (fun out : fin outnum =>
    add (idx (idx (MatMul2d input (Transpose2d w)) b) out) (idx bias out))).
Proof.
  intros. unfold Ops_PoolPad.Linear2d, MatMul2d, Transpose2d.
  f_equal. apply functional_extensionality. intro b.
  f_equal. apply functional_extensionality. intro out.
  f_equal.
  rewrite !idx_mkvSeq by assumption.
  f_equal. f_equal. apply functional_extensionality. intro k.
  rewrite !idx_mkvSeq by assumption.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_gelu_tanh.
Print Assumptions A_gelu.
Print Assumptions A_GELU4d.
Print Assumptions A_LNcell.
Print Assumptions A_LayerNorm2d.
Print Assumptions A_LayerNorm3d.
Print Assumptions A_LayerNorm4d.
Print Assumptions A_Gather1d.
Print Assumptions A_Gather2d.
Print Assumptions A_Transpose2d.
Print Assumptions A_SplitHeads.
Print Assumptions A_MergeHeads.
Print Assumptions A_CausalMask2d.
Print Assumptions A_CausalMask4d.
Print Assumptions A_MatMul2d.
Print Assumptions Linear2d_as_MatMul2d.
