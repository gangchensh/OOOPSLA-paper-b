(* DPIA-style Leibniz equivalence proofs for three low-difficulty mainstream
   LLM operator variants (milestone M-a of the mainstream-LLM coverage plan,
   cf. doc/主流大模型覆盖规划_20260914.md §2 items 1-2) in the route-A
   R-based expression model.

   Operators delivered (functional definition + imperative counterpart
   [*_comm] + Leibniz equality [A_*], all closed with [Qed]):

   - SlidingWindowMask2d/4d (Mistral sliding window attention): the mask
     condition of [CausalMask2d] (Ionia.Ops_Transformer) changes from
     [j <= i] to [i - w < j <= i].  Over [nat] the strict left inequality is
     written without truncated subtraction as [i <= j + w], so the keep
     condition is the Coq [bool] conjunction
       (fin2nat j <=? fin2nat i) && (fin2nat i <=? fin2nat j + w)
     handled by [Aif1] exactly as in [A_CausalMask2d].  The "-infinity"
     stand-in [NEGINF] of Ionia.Ops_Transformer is reused.

   - QKNormAttention (Gemma/Qwen3 QK-norm): the query and key matrices are
     each passed through the already-proved [RMSNorm2d] (Ionia.Ops_LLaMA,
     normalisation over the head-dimension axis, per position) before
     entering the attention cell of Ionia.Attention_DPIA:
       softmax(CausalMask(RMS(Q) RMS(K)^T / sqrt(d))) V.
     The cell command writes only [output] (the composed-input style of
     [attention_cell_comm]), so [A_QKNorm] is a direct [A_Attention_cell]
     instance — the normalisation computations are folded into the score
     expression, following the route-A recompute-per-element philosophy.

   - softcap / Softcap1d / Softcap2d (Gemma logit soft-capping): the
     elementwise soft clip softcap(x) = c * tanh(x / c), applied either to
     the attention logits (s x s, [Softcap2d]) or to a final logit vector
     ([Softcap1d]).  tanh is the already-introduced [gelu_tanh] of
     Ionia.Ops_Transformer; the scalar rule [A_softcap] is
     reflexivity-shaped like [A_gelu], and the array lemmas follow the
     pointwise template of [A_GELU4d].

   Small-instance computation checks close the file, followed by the axiom
   audit. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* [NEGINF], [CausalMask2d] (template), [gelu_tanh] (tanh for softcap). *)
Require Import Ionia.Ops_Transformer.
(* [RMSNorm2d]. *)
Require Import Ionia.Ops_LLaMA.
(* [Attention_cell] / [attention_cell_comm] / [A_Attention_cell]. *)
Require Import Ionia.Attention_DPIA.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Sliding window attention mask (Mistral)                                     *)
(* -------------------------------------------------------------------------- *)

(* Keep condition of the windowed causal mask, window size [w]:
   position (i, j) keeps the score iff i - w < j <= i.  Over [nat] the left
   inequality is written as [i <= j + w], which agrees with the integer
   reading of [i - w < j] also when i < w (truncated subtraction would
   wrongly exclude j = 0 there). *)
Definition swm_keep (w : nat) (i j : nat) : bool :=
  andb (j <=? i)%nat (i <=? j + w)%nat.

(* Sliding-window mask on an s x s score matrix. *)
Definition SlidingWindowMask2d (w : nat) {s : nat}
  (input : exp (ary '{s} (ary '{s} num)))
  : exp (ary '{s} (ary '{s} num)) :=
  mkvSeq (fun i : fin s => mkvSeq (fun j : fin s =>
    if swm_keep w (fin2nat i) (fin2nat j)
      then idx (idx input i) j
      else NEGINF)).

Definition SlidingWindowMask2d_comm (w : nat) {s : nat}
  (input : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{s} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    If (swm_keep w (fin2nat i) (fin2nat j))
       (oj |:= idx (idx input i) j)
       (oj |:= NEGINF)) oi) output.

Lemma A_SlidingWindowMask2d : forall (w s : nat)
  (input : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{s} num))),
  A(output, SlidingWindowMask2d w input)
  = SlidingWindowMask2d_comm w input output.
Proof.
  intros. unfold SlidingWindowMask2d, SlidingWindowMask2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

(* Batched multi-head form: (b, h, s, s), windowed mask on the last two
   axes. *)
Definition SlidingWindowMask4d (w : nat) {batch heads s : nat}
  (input : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))))
  : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun hh : fin heads =>
    mkvSeq (fun i : fin s => mkvSeq (fun j : fin s =>
      if swm_keep w (fin2nat i) (fin2nat j)
        then idx (idx (idx (idx input b) hh) i) j
        else NEGINF)))).

Definition SlidingWindowMask4d_comm (w : nat) {batch heads s : nat}
  (input : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))))
  (output : acc (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun hh oh => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    If (swm_keep w (fin2nat i) (fin2nat j))
       (oj |:= idx (idx (idx (idx input b) hh) i) j)
       (oj |:= NEGINF)) oi) oh) ob) output.

Lemma A_SlidingWindowMask4d : forall (w batch heads s : nat)
  (input : exp (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num)))))
  (output : acc (ary '{batch} (ary '{heads} (ary '{s} (ary '{s} num))))),
  A(output, SlidingWindowMask4d w input)
  = SlidingWindowMask4d_comm w input output.
Proof.
  intros. unfold SlidingWindowMask4d, SlidingWindowMask4d_comm.
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
(* QK-norm (Gemma/Qwen3): RMSNorm on Q and K before the attention cell        *)
(* -------------------------------------------------------------------------- *)

(* Each of Q and K is normalised over the head-dimension axis (per position)
   by the already-proved [RMSNorm2d] (with separate gains, shared eps), then
   fed to the causal attention cell of Ionia.Attention_DPIA:
     softmax(CausalMask(RMSNorm(Q) RMSNorm(K)^T / sqrt(d))) V. *)
Definition QKNormAttention {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (gamma_q gamma_k : exp (ary '{d} num))
  (eps : exp num)
  : exp (ary '{s} (ary '{d} num)) :=
  Attention_cell (RMSNorm2d q gamma_q eps) (RMSNorm2d k gamma_k eps) v.

(* The cell command writes only [output]; the RMSNorm reductions are folded
   into the composed score expression (the recompute-per-element style of
   [attention_cell_comm]). *)
Definition QKNormAttention_comm {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (gamma_q gamma_k : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{s} (ary '{d} num))) : comm :=
  attention_cell_comm (RMSNorm2d q gamma_q eps) (RMSNorm2d k gamma_k eps)
                      v output.

(* Composition equality: normalising Q and K inside the attention cell
   commutes with the command-level reading — a direct [A_Attention_cell]
   instance at the normed inputs. *)
Lemma A_QKNorm : forall (s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (gamma_q gamma_k : exp (ary '{d} num))
  (eps : exp num)
  (output : acc (ary '{s} (ary '{d} num))),
  A(output, QKNormAttention q k v gamma_q gamma_k eps)
  = QKNormAttention_comm q k v gamma_q gamma_k eps output.
Proof.
  intros. unfold QKNormAttention, QKNormAttention_comm.
  apply A_Attention_cell.
Qed.

(* -------------------------------------------------------------------------- *)
(* Logit softcap (Gemma): softcap(x) = c * tanh(x / c)                         *)
(* -------------------------------------------------------------------------- *)

(* tanh is [gelu_tanh] of Ionia.Ops_Transformer; the cap [c] enters as an
   expression so that the same operator covers the attention-logit cap and
   the final-logit cap. *)
Definition softcap (c x : exp num) : exp num :=
  mul c (gelu_tanh (div x c)).

(* Reflexivity-shaped scalar rule, modelled on [A_gelu]. *)
Lemma A_softcap : forall (a : acc num) (c e : exp num),
  A(a, softcap c e) = C(e, fun r => a |:= softcap c r).
Proof. reflexivity. Qed.

(* Softcap1d: elementwise soft clip of a logit vector (final logits). *)
Definition Softcap1d {n : nat} (c : exp num)
  (input : exp (ary '{n} num)) : exp (ary '{n} num) :=
  mkvSeq (fun i : fin n => softcap c (idx input i)).

Definition Softcap1d_comm {n : nat} (c : exp num)
  (input : exp (ary '{n} num))
  (output : acc (ary '{n} num)) : comm :=
  mkvSeql (fun i oi => oi |:= softcap c (idx input i)) output.

Lemma A_Softcap1d : forall (n : nat) (c : exp num)
  (input : exp (ary '{n} num))
  (output : acc (ary '{n} num)),
  A(output, Softcap1d c input) = Softcap1d_comm c input output.
Proof.
  intros. unfold Softcap1d, Softcap1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_num.
  reflexivity.
Qed.

(* Softcap2d: elementwise soft clip of an m x n logit matrix (the attention
   logits form, applied before softmax). *)
Definition Softcap2d {m n : nat} (c : exp num)
  (input : exp (ary '{m} (ary '{n} num)))
  : exp (ary '{m} (ary '{n} num)) :=
  mkvSeq (fun i : fin m => mkvSeq (fun j : fin n =>
    softcap c (idx (idx input i) j))).

Definition Softcap2d_comm {m n : nat} (c : exp num)
  (input : exp (ary '{m} (ary '{n} num)))
  (output : acc (ary '{m} (ary '{n} num))) : comm :=
  mkvSeql (fun i oi => mkvSeql (fun j oj =>
    oj |:= softcap c (idx (idx input i) j)) oi) output.

Lemma A_Softcap2d : forall (m n : nat) (c : exp num)
  (input : exp (ary '{m} (ary '{n} num)))
  (output : acc (ary '{m} (ary '{n} num))),
  A(output, Softcap2d c input) = Softcap2d_comm c input output.
Proof.
  intros. unfold Softcap2d, Softcap2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Small-instance computation checks                                          *)
(* -------------------------------------------------------------------------- *)

Definition sw_i0_4 : fin 4 := @nat2fin 4 0 (ltac:(lia)).
Definition sw_i1_4 : fin 4 := @nat2fin 4 1 (ltac:(lia)).
Definition sw_i2_4 : fin 4 := @nat2fin 4 2 (ltac:(lia)).
Definition sw_i3_4 : fin 4 := @nat2fin 4 3 (ltac:(lia)).

(* 4x4 test matrix, entry (i,j) = 10i + j. *)
Definition M4 : exp (ary '{4} (ary '{4} num)) :=
  mkvSeq (fun i : fin 4 => mkvSeq (fun j : fin 4 =>
    (INR (fin2nat i * 10 + fin2nat j)%nat : exp num))).

(* Window w = 1, row 3: the diagonal (3,3) and the previous position (3,2)
   are inside the window; (3,1) and the future (2,3) are masked.  The mask
   checks use plain conversion rather than [vm_compute], as in
   [check_mask_keep] of Ionia.Attention_DPIA (NEGINF carries 10^30). *)
Example check_swm_keep_diag :
  idx (idx (SlidingWindowMask2d 1 M4) sw_i3_4) sw_i3_4 = INR 33.
Proof. reflexivity. Qed.

Example check_swm_keep_inwin :
  idx (idx (SlidingWindowMask2d 1 M4) sw_i3_4) sw_i2_4 = INR 32.
Proof. reflexivity. Qed.

Example check_swm_drop_outwin :
  idx (idx (SlidingWindowMask2d 1 M4) sw_i3_4) sw_i1_4 = NEGINF.
Proof. reflexivity. Qed.

Example check_swm_drop_future :
  idx (idx (SlidingWindowMask2d 1 M4) sw_i2_4) sw_i3_4 = NEGINF.
Proof. reflexivity. Qed.

(* Small i (i < w): with w = 2, row 1 keeps everything up to the diagonal —
   the [i <= j + w] form does not exclude j = 0. *)
Example check_swm_small_i_keeps_zero :
  idx (idx (SlidingWindowMask2d 2 M4) sw_i1_4) sw_i0_4 = INR 10.
Proof. reflexivity. Qed.

(* Softcap cell structure: softcap(c, x) = c * tanh(x / c). *)
Example check_softcap_cell : forall (c : exp num),
  idx (Softcap1d c (mkvSeq (fun i : fin 4 => (INR (fin2nat i) : exp num))))
      sw_i2_4
  = softcap c (INR 2).
Proof. reflexivity. Qed.

(* QK-norm composition structure: the attention cell reads the RMS-normed
   Q and K. *)
Example check_qknorm_structure : forall (s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (gq gk : exp (ary '{d} num)) (eps : exp num),
  QKNormAttention q k v gq gk eps
  = Attention_cell (RMSNorm2d q gq eps) (RMSNorm2d k gk eps) v.
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_SlidingWindowMask2d.
Print Assumptions A_SlidingWindowMask4d.
Print Assumptions A_QKNorm.
Print Assumptions A_softcap.
Print Assumptions A_Softcap1d.
Print Assumptions A_Softcap2d.
