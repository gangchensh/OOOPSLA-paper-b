(* DPIA-style Leibniz equivalence proofs for MoE (Mixture-of-Experts) routing —
   milestone M-b of the mainstream-LLM coverage plan
   (doc/主流大模型覆盖规划_20260914.md §3), in the route-A R-based expression
   model.  Target shape: Mixtral (gate -> top-k -> per-expert SwiGLU FFN ->
   weighted sum).

   Operators delivered (functional definition + imperative counterpart
   [*_comm] + Leibniz equality [A_*], all closed with [Qed]):

   - Indexed argmax reduction [ArgMax]: one pass of [reduce] over the
     (score, INR index) pair vector [ScoreIdx], accumulator type
     [ary '{2} num] — the LSTM dual-state pair encoding of Ionia.Ops_RNN
     ([sel2]/[st_c]/[st_h]), folded by the general accumulator rule
     [A_reduce_gen] (Ops_RNN).  [ArgMaxVal]/[ArgMaxIdx] project the pair.
     This is the "indexed reduction" (value, index) option of the plan;
     the k-times max+mask chain is the iterated use of [ArgMax] + [MaskExpert]
     ([MaskChain]/[TopKIdx]: TopKIdx k = index of the (k+1)-th largest score).

   - [MaskExpert]: set the selected expert's score to [NEGINF] (the masking
     step of the argmax chain).  The selected index is a VALUE (a real, the
     [INR (fin2nat i)] stored by [ArgMax]), so the mask test is the real
     boolean equality [R_beq] against the index encodings — a value-level
     guard handled by [Aif1], as in [CausalMask2d].

   - [Top2]: top-2 threshold fold (Mixtral k=2).  Accumulator (m1, m2) with
     m1 the running max and m2 the running second max, again the ary-2 pair
     encoding via [A_reduce_gen].  [Top2Threshold] = the m2 projection; expert
     e is selected iff m2 <= score_e ([moe_sel], a value-level [leExp] guard).

   - [TopKGate]: top-k softmax gating weights
       w_e = if m2 <= s_e then exp(s_e) / sum_{e': m2 <= s_e'} exp(s_e')
             else 0,
     i.e. softmax restricted to the selected experts (ties at the threshold
     are all selected).  The per-element cell [A_moe_weight_cell] recomputes
     the normalisation sum on the element accumulator, the [A_RMScell]
     (Ionia.Ops_LLaMA) single-reduction template via [C_sum_post_acc].

   - Expert dispatch and aggregation: [moe_term] = the If-guarded weighted
     expert term (if sel e then w_e * out_e_j else 0), [A_moe_term] = the
     dispatch rule: the expert term is computed ONLY under the guard
     ([Aif1] + [A_num]).  [MoE_combine] = the weighted aggregation
     out_j = sum_e moe_term(e, j), per-element [suml] reduction
     ([A_sum_acc]), the MatMul2d template.  Note the expert identity e in
     the seqfor is STATIC (the branch targets are the statically known
     experts); the guard is value-dependent, which is inherent to
     data-dependent MoE routing.

   - [MoEFeedForward]: the end-to-end Mixtral block
       scores = Wg x;  m2 = Top2Threshold scores;  w = TopKGate scores;
       out_j = sum_e (if sel e then w_e * (W2_e (Swish(x W1_e) * (x W3_e)))_j
                      else 0)
     with the expert FFN [ExpertFFN] = the already-proved SwiGLU composition
     ([swish] of Ionia.Ops_LLaMA).  [A_MoEFeedForward] is the Ops-level block
     equation: the command side is the direct mkvSeql/suml nest that
     recomputes the gate/threshold per element (the LayerNorm recompute
     precedent of Ionia.Ops_Transformer); buffer-sharing (compute the gate
     once) is a further refinement layer (cf. LLaMAMini_DPIA).

   Small-instance computation checks (E = 4 experts, k = 2) close the file,
   followed by the axiom audit. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* [A_reduce_gen] (general-accumulator reduction rule) and the ary-2 pair
   encoding [sel2]/[st_c]/[st_h]. *)
Require Import Ionia.Ops_RNN.
(* [swish] for the expert SwiGLU FFN. *)
Require Import Ionia.Ops_LLaMA.
(* [NEGINF], the "-infinity" stand-in used for masking. *)
Require Import Ionia.Ops_Transformer.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Pair encoding helpers (the LSTM ary-2 precedent)                            *)
(* -------------------------------------------------------------------------- *)

(* A pair (u, v) of scalars as a length-2 array; slot [st_c] (= 0) holds the
   first component (score/max), slot [st_h] (= 1) the second (index/2nd max). *)
Definition pair2 (u v : exp num) : exp (ary '{2} num) := mkvSeq (sel2 u v).

Lemma pair2_fst : forall (u v : exp num), idx (pair2 u v) st_c = u.
Proof. intros. unfold pair2. rewrite idx_mkvSeq by lia. apply sel2_c. Qed.

Lemma pair2_snd : forall (u v : exp num), idx (pair2 u v) st_h = v.
Proof. intros. unfold pair2. rewrite idx_mkvSeq by lia. apply sel2_h. Qed.

(* -------------------------------------------------------------------------- *)
(* Indexed argmax reduction (one pass over (value, index) pairs)               *)
(* -------------------------------------------------------------------------- *)

(* Attach to every score its index encoded as a real. *)
Definition ScoreIdx {E : nat} (scores : exp (ary '{E} num))
  : exp (ary '{E} (ary '{2} num)) :=
  mkvSeq (fun i : fin E => pair2 (idx scores i) (INR (fin2nat i))).

(* Keep the pair with the larger first component (strict: the EARLIER index
   wins ties, since the accumulator is kept on equality). *)
Definition argmax_step (x acc : exp (ary '{2} num)) : exp (ary '{2} num) :=
  if gtExp (idx x st_c) (idx acc st_c) then x else acc.

(* One reduction pass computing the (max score, its index) pair. *)
Definition ArgMax {E : nat} (scores : exp (ary '{E} num))
  : exp (ary '{2} num) :=
  reduce argmax_step (pair2 NEGINF zero) (ScoreIdx scores).

Definition ArgMaxVal {E : nat} (scores : exp (ary '{E} num)) : exp num :=
  idx (ArgMax scores) st_c.

Definition ArgMaxIdx {E : nat} (scores : exp (ary '{E} num)) : exp num :=
  idx (ArgMax scores) st_h.

Definition ArgMax_comm {E : nat} (scores : exp (ary '{E} num))
  (out : acc (ary '{2} num)) : comm :=
  reducel argmax_step (pair2 NEGINF zero) (ScoreIdx scores)
          (fun r => A(out, r)) out.

(* The indexed reduction rule: a direct [A_reduce_gen] instance with
   accumulator type t := ary '{2} num. *)
Lemma A_ArgMax : forall (E : nat) (scores : exp (ary '{E} num)) (p : path),
  A(acc' p, ArgMax scores) = ArgMax_comm scores (acc' p).
Proof. intros. unfold ArgMax, ArgMax_comm. apply A_reduce_gen. Qed.

(* -------------------------------------------------------------------------- *)
(* Masking (the "mask out the winner" step of the argmax chain)                *)
(* -------------------------------------------------------------------------- *)

(* Zero out (NEGINF) the expert whose index encoding equals [selidx]. *)
Definition MaskExpert {E : nat} (scores : exp (ary '{E} num)) (selidx : exp num)
  : exp (ary '{E} num) :=
  mkvSeq (fun e : fin E =>
    if R_beq (INR (fin2nat e)) selidx then NEGINF else idx scores e).

Definition MaskExpert_comm {E : nat} (scores : exp (ary '{E} num))
  (selidx : exp num) (output : acc (ary '{E} num)) : comm :=
  mkvSeql (fun e oe =>
    If (R_beq (INR (fin2nat e)) selidx)
       (oe |:= NEGINF)
       (oe |:= idx scores e)) output.

Lemma A_MaskExpert : forall (E : nat) (scores : exp (ary '{E} num))
  (selidx : exp num) (output : acc (ary '{E} num)),
  A(output, MaskExpert scores selidx) = MaskExpert_comm scores selidx output.
Proof.
  intros. unfold MaskExpert, MaskExpert_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro e.
  rewrite Aif1. rewrite !A_num.
  reflexivity.
Qed.

(* The k-times max+mask chain: [MaskChain k scores] masks the top-k winners,
   so [TopKIdx k] is the index of the (k+1)-th largest score. *)
Fixpoint MaskChain {E : nat} (k : nat) (scores : exp (ary '{E} num))
  : exp (ary '{E} num) :=
  match k with
  | 0 => scores
  | S k' => MaskExpert (MaskChain k' scores) (ArgMaxIdx (MaskChain k' scores))
  end.

Definition TopKIdx {E : nat} (k : nat) (scores : exp (ary '{E} num))
  : exp num :=
  ArgMaxIdx (MaskChain k scores).

(* -------------------------------------------------------------------------- *)
(* Top-2 threshold fold (Mixtral k = 2)                                        *)
(* -------------------------------------------------------------------------- *)

(* Accumulator (m1, m2): m1 = running max, m2 = running second max. *)
Definition top2_step (x : exp num) (acc : exp (ary '{2} num))
  : exp (ary '{2} num) :=
  if gtExp x (idx acc st_c)
    then pair2 x (idx acc st_c)
    else if gtExp x (idx acc st_h)
      then pair2 (idx acc st_c) x
      else acc.

Definition Top2 {E : nat} (scores : exp (ary '{E} num))
  : exp (ary '{2} num) :=
  reduce top2_step (pair2 NEGINF NEGINF) scores.

Definition Top2_comm {E : nat} (scores : exp (ary '{E} num))
  (out : acc (ary '{2} num)) : comm :=
  reducel top2_step (pair2 NEGINF NEGINF) scores (fun r => A(out, r)) out.

Lemma A_Top2 : forall (E : nat) (scores : exp (ary '{E} num)) (p : path),
  A(acc' p, Top2 scores) = Top2_comm scores (acc' p).
Proof. intros. unfold Top2, Top2_comm. apply A_reduce_gen. Qed.

(* The selection threshold: the second-largest score. *)
Definition Top2Threshold {E : nat} (scores : exp (ary '{E} num)) : exp num :=
  idx (Top2 scores) st_h.

(* -------------------------------------------------------------------------- *)
(* Top-k softmax gating weights                                                *)
(* -------------------------------------------------------------------------- *)

(* Selection guard: expert e is selected iff its score reaches the threshold
   (value-level comparison on reals, so ties at the threshold are all in). *)
Definition moe_sel {E : nat} (scores : exp (ary '{E} num)) (m2 : exp num)
  (e : fin E) : bool :=
  leExp m2 (idx scores e).

(* Guarded softmax numerator: exp(s_e) if selected, else 0. *)
Definition moe_gexp {E : nat} (scores : exp (ary '{E} num)) (m2 : exp num)
  (e : fin E) : exp num :=
  if moe_sel scores m2 e then pExp (idx scores e) else zero.

(* Normalisation denominator: sum of the guarded numerators. *)
Definition moe_denom {E : nat} (scores : exp (ary '{E} num)) (m2 : exp num)
  : exp num :=
  sum (mkvSeq (fun e : fin E => moe_gexp scores m2 e)).

(* Normalised top-k weight (softmax over the selected experts). *)
Definition moe_weight {E : nat} (scores : exp (ary '{E} num)) (m2 : exp num)
  (e : fin E) : exp num :=
  if moe_sel scores m2 e
    then div (pExp (idx scores e)) (moe_denom scores m2)
    else zero.

(* Per-element cell: the denominator sum is computed on the element
   accumulator itself; the [A_RMScell] (Ionia.Ops_LLaMA) single-reduction
   template via [C_sum_post_acc], with the selection guard pushed to the
   command level by [Aif1]. *)
Lemma A_moe_weight_cell : forall (E : nat) (scores : exp (ary '{E} num))
  (m2 : exp num) (e : fin E) (o : acc num),
  A(o, moe_weight scores m2 e)
  = If (moe_sel scores m2 e)
       (suml (mkvSeq (fun e' : fin E => moe_gexp scores m2 e'))
             (fun rdenom => o |:= div (pExp (idx scores e)) rdenom)
             o)
       (o |:= zero).
Proof.
  intros. unfold moe_weight.
  rewrite Aif1. f_equal.
  unfold moe_denom.
  replace (A(o, div (pExp (idx scores e))
                    (sum (mkvSeq (fun e' : fin E => moe_gexp scores m2 e')))))
    with (C(sum (mkvSeq (fun e' : fin E => moe_gexp scores m2 e')),
            fun r => o |:= div (pExp (idx scores e)) r))
    by reflexivity.
  rewrite C_sum_post_acc. reflexivity.
Qed.

(* The gating weight vector: w = TopKGate scores. *)
Definition TopKGate {E : nat} (scores : exp (ary '{E} num))
  : exp (ary '{E} num) :=
  mkvSeq (fun e : fin E => moe_weight scores (Top2Threshold scores) e).

Definition TopKGate_comm {E : nat} (scores : exp (ary '{E} num))
  (output : acc (ary '{E} num)) : comm :=
  mkvSeql (fun e oe =>
    If (moe_sel scores (Top2Threshold scores) e)
       (suml (mkvSeq (fun e' : fin E =>
                moe_gexp scores (Top2Threshold scores) e'))
             (fun rdenom => oe |:= div (pExp (idx scores e)) rdenom)
             oe)
       (oe |:= zero)) output.

Lemma A_TopKGate : forall (E : nat) (scores : exp (ary '{E} num))
  (output : acc (ary '{E} num)),
  A(output, TopKGate scores) = TopKGate_comm scores output.
Proof.
  intros. unfold TopKGate, TopKGate_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro e.
  rewrite A_moe_weight_cell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Expert dispatch and weighted aggregation                                    *)
(* -------------------------------------------------------------------------- *)

(* The If-guarded weighted expert term: selected experts contribute
   w_e * out_e_j, others contribute 0. *)
Definition moe_term {E d : nat} (sel : fin E -> bool)
  (w : exp (ary '{E} num)) (eo : exp (ary '{E} (ary '{d} num)))
  (e : fin E) (j : fin d) : exp num :=
  if sel e then mul (idx w e) (idx (idx eo e) j) else zero.

(* Dispatch rule: the expert term is computed ONLY under the guard — the
   imperative form skips the unselected expert's contribution entirely
   ([Aif1] instance; cf. [A_CausalMask2d]). *)
Lemma A_moe_term : forall (E d : nat) (sel : fin E -> bool)
  (w : exp (ary '{E} num)) (eo : exp (ary '{E} (ary '{d} num)))
  (e : fin E) (j : fin d) (o : acc num),
  A(o, moe_term sel w eo e j)
  = If (sel e) (o |:= mul (idx w e) (idx (idx eo e) j)) (o |:= zero).
Proof.
  intros. unfold moe_term. rewrite Aif1. rewrite !A_num. reflexivity.
Qed.

(* Weighted aggregation: out_j = sum_e moe_term(e, j). *)
Definition MoE_combine {E d : nat} (sel : fin E -> bool)
  (w : exp (ary '{E} num)) (eo : exp (ary '{E} (ary '{d} num)))
  : exp (ary '{d} num) :=
  mkvSeq (fun j : fin d =>
    sum (mkvSeq (fun e : fin E => moe_term sel w eo e j))).

Definition MoE_combine_comm {E d : nat} (sel : fin E -> bool)
  (w : exp (ary '{E} num)) (eo : exp (ary '{E} (ary '{d} num)))
  (output : acc (ary '{d} num)) : comm :=
  mkvSeql (fun j oj =>
    suml (mkvSeq (fun e : fin E => moe_term sel w eo e j))
         (fun r => oj |:= r) oj) output.

Lemma A_MoE_combine : forall (E d : nat) (sel : fin E -> bool)
  (w : exp (ary '{E} num)) (eo : exp (ary '{E} (ary '{d} num)))
  (output : acc (ary '{d} num)),
  A(output, MoE_combine sel w eo) = MoE_combine_comm sel w eo output.
Proof.
  intros. unfold MoE_combine, MoE_combine_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Expert FFN (SwiGLU, the Mixtral expert)                                     *)
(* -------------------------------------------------------------------------- *)

(* Matrix-vector product, the [MatMul2d] row form. *)
Definition MatVec {m n : nat} (M : exp (ary '{m} (ary '{n} num)))
  (v : exp (ary '{n} num)) : exp (ary '{m} num) :=
  mkvSeq (fun i : fin m =>
    sum (mkvSeq (fun k : fin n => mul (idx (idx M i) k) (idx v k)))).

Definition MatVec_comm {m n : nat} (M : exp (ary '{m} (ary '{n} num)))
  (v : exp (ary '{n} num)) (output : acc (ary '{m} num)) : comm :=
  mkvSeql (fun i oi =>
    suml (mkvSeq (fun k : fin n => mul (idx (idx M i) k) (idx v k)))
         (fun r => oi |:= r) oi) output.

Lemma A_MatVec : forall (m n : nat) (M : exp (ary '{m} (ary '{n} num)))
  (v : exp (ary '{n} num)) (output : acc (ary '{m} num)),
  A(output, MatVec M v) = MatVec_comm M v output.
Proof.
  intros. unfold MatVec, MatVec_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* The SwiGLU gate: Swish(x W1) * (x W3) on the projected inputs. *)
Definition ExpertGate {d df : nat}
  (W1 : exp (ary '{df} (ary '{d} num)))
  (W3 : exp (ary '{df} (ary '{d} num)))
  (x : exp (ary '{d} num)) : exp (ary '{df} num) :=
  mkvSeq (fun i : fin df =>
    mul (swish (idx (MatVec W1 x) i)) (idx (MatVec W3 x) i)).

Definition ExpertGate_comm {d df : nat}
  (W1 : exp (ary '{df} (ary '{d} num)))
  (W3 : exp (ary '{df} (ary '{d} num)))
  (x : exp (ary '{d} num)) (output : acc (ary '{df} num)) : comm :=
  mkvSeql (fun i oi =>
    oi |:= mul (swish (idx (MatVec W1 x) i)) (idx (MatVec W3 x) i)) output.

Lemma A_ExpertGate : forall (d df : nat)
  (W1 : exp (ary '{df} (ary '{d} num)))
  (W3 : exp (ary '{df} (ary '{d} num)))
  (x : exp (ary '{d} num)) (output : acc (ary '{df} num)),
  A(output, ExpertGate W1 W3 x) = ExpertGate_comm W1 W3 x output.
Proof.
  intros. unfold ExpertGate, ExpertGate_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_num.
  reflexivity.
Qed.

(* One expert: down-projection of the gated hidden vector. *)
Definition ExpertFFN {d df : nat}
  (W1 : exp (ary '{df} (ary '{d} num)))
  (W3 : exp (ary '{df} (ary '{d} num)))
  (W2 : exp (ary '{d} (ary '{df} num)))
  (x : exp (ary '{d} num)) : exp (ary '{d} num) :=
  MatVec W2 (ExpertGate W1 W3 x).

Definition ExpertFFN_comm {d df : nat}
  (W1 : exp (ary '{df} (ary '{d} num)))
  (W3 : exp (ary '{df} (ary '{d} num)))
  (W2 : exp (ary '{d} (ary '{df} num)))
  (x : exp (ary '{d} num)) (output : acc (ary '{d} num)) : comm :=
  MatVec_comm W2 (ExpertGate W1 W3 x) output.

Lemma A_ExpertFFN : forall (d df : nat)
  (W1 : exp (ary '{df} (ary '{d} num)))
  (W3 : exp (ary '{df} (ary '{d} num)))
  (W2 : exp (ary '{d} (ary '{df} num)))
  (x : exp (ary '{d} num)) (output : acc (ary '{d} num)),
  A(output, ExpertFFN W1 W3 W2 x) = ExpertFFN_comm W1 W3 W2 x output.
Proof. intros. unfold ExpertFFN, ExpertFFN_comm. apply A_MatVec. Qed.

(* The family of expert outputs, indexed by the (static) expert identity. *)
Definition moe_expert_outputs {E d df : nat}
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num)) : exp (ary '{E} (ary '{d} num)) :=
  mkvSeq (fun e : fin E => ExpertFFN (idx W1s e) (idx W3s e) (idx W2s e) x).

Definition moe_expert_outputs_comm {E d df : nat}
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num))
  (output : acc (ary '{E} (ary '{d} num))) : comm :=
  mkvSeql (fun e oe =>
    ExpertFFN_comm (idx W1s e) (idx W3s e) (idx W2s e) x oe) output.

Lemma A_moe_expert_outputs : forall (E d df : nat)
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num))
  (output : acc (ary '{E} (ary '{d} num))),
  A(output, moe_expert_outputs W1s W3s W2s x)
  = moe_expert_outputs_comm W1s W3s W2s x output.
Proof.
  intros. unfold moe_expert_outputs, moe_expert_outputs_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro e.
  rewrite A_ExpertFFN. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The MoE feed-forward block (Mixtral shape)                                  *)
(* -------------------------------------------------------------------------- *)

(* Gate projection -> top-2 threshold -> top-k softmax weights -> per-expert
   SwiGLU FFN -> If-guarded weighted sum. *)
Definition MoEFeedForward {E d df : nat}
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num)) : exp (ary '{d} num) :=
  MoE_combine (moe_sel (MatVec Wg x) (Top2Threshold (MatVec Wg x)))
              (TopKGate (MatVec Wg x))
              (moe_expert_outputs W1s W3s W2s x).

Definition MoEFeedForward_comm {E d df : nat}
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num))
  (output : acc (ary '{d} num)) : comm :=
  MoE_combine_comm (moe_sel (MatVec Wg x) (Top2Threshold (MatVec Wg x)))
                   (TopKGate (MatVec Wg x))
                   (moe_expert_outputs W1s W3s W2s x) output.

(* End-to-end block equation (Ops level): the command is the direct
   mkvSeql/suml nest; gate scores, threshold and weights are recomputed per
   output element exactly as LayerNorm recomputes the mean (the
   [A_LayerNorm2d] precedent). *)
Lemma A_MoEFeedForward : forall (E d df : nat)
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num))
  (output : acc (ary '{d} num)),
  A(output, MoEFeedForward Wg W1s W3s W2s x)
  = MoEFeedForward_comm Wg W1s W3s W2s x output.
Proof.
  intros. unfold MoEFeedForward, MoEFeedForward_comm.
  apply A_MoE_combine.
Qed.

(* -------------------------------------------------------------------------- *)
(* Small-instance computation checks (E = 4 experts, k = 2)                    *)
(* -------------------------------------------------------------------------- *)

Definition moe_f0 : fin 4 := @nat2fin 4 0 (ltac:(lia)).
Definition moe_f1 : fin 4 := @nat2fin 4 1 (ltac:(lia)).
Definition moe_f2 : fin 4 := @nat2fin 4 2 (ltac:(lia)).
Definition moe_f3 : fin 4 := @nat2fin 4 3 (ltac:(lia)).

(* The pair encoding really pairs. *)
Example check_pair2_proj : forall (u v : exp num),
  idx (pair2 u v) st_c = u /\ idx (pair2 u v) st_h = v.
Proof.
  intros. split; [apply pair2_fst | apply pair2_snd].
Qed.

(* E = 4: the top-2 fold unrolls to the 4-step nest, oldest score innermost. *)
Example check_top2_unroll4 : forall (s0 s1 s2 s3 : exp num),
  Top2 (((((tt, s0), s1), s2), s3) : exp (ary '{4} num))
  = top2_step s3 (top2_step s2 (top2_step s1
        (top2_step s0 (pair2 NEGINF NEGINF)))).
Proof. reflexivity. Qed.

(* E = 4: the indexed argmax fold unrolls the same way over (value, index)
   pairs. *)
Example check_argmax_unroll4 : forall (p0 p1 p2 p3 : exp (ary '{2} num)),
  reduce argmax_step (pair2 NEGINF zero)
    (((((tt, p0), p1), p2), p3) : exp (ary '{4} (ary '{2} num)))
  = argmax_step p3 (argmax_step p2 (argmax_step p1
        (argmax_step p0 (pair2 NEGINF zero)))).
Proof. reflexivity. Qed.

(* ScoreIdx attaches the INR index encoding to each score. *)
Example check_scoreidx_entry_E4 : forall (scores : exp (ary '{4} num))
  (i : fin 4),
  idx (ScoreIdx scores) i = pair2 (idx scores i) (INR (fin2nat i)).
Proof.
  intros. unfold ScoreIdx. rewrite idx_mkvSeq by lia. reflexivity.
Qed.

(* The k-times max+mask chain, second step: index of the second-largest
   score = argmax of the once-masked vector. *)
Example check_topk_chain_step2 : forall (scores : exp (ary '{4} num)),
  TopKIdx 1 scores = ArgMaxIdx (MaskExpert scores (ArgMaxIdx scores)).
Proof. reflexivity. Qed.

(* E = 4, expert 0: the gating weight is the guarded softmax over the
   threshold-selected experts. *)
Example check_gate_weight_E4 : forall (scores : exp (ary '{4} num))
  (m2 : exp num),
  moe_weight scores m2 moe_f0
  = if leExp m2 (idx scores moe_f0)
    then div (pExp (idx scores moe_f0))
             (sum (mkvSeq (fun e' : fin 4 =>
                if leExp m2 (idx scores e')
                  then pExp (idx scores e')
                  else zero)))
    else zero.
Proof. reflexivity. Qed.

(* The gate vector entry is the per-expert weight. *)
Example check_topkgate_entry_E4 : forall (scores : exp (ary '{4} num))
  (e : fin 4),
  idx (TopKGate scores) e = moe_weight scores (Top2Threshold scores) e.
Proof.
  intros. unfold TopKGate. rewrite idx_mkvSeq by lia. reflexivity.
Qed.

(* E = 4, dispatch: the combine summand of expert e at output j is the
   If-guarded weighted expert term. *)
Example check_combine_summand_E4 : forall (d : nat) (sel : fin 4 -> bool)
  (w : exp (ary '{4} num)) (eo : exp (ary '{4} (ary '{d} num)))
  (j : fin d) (e : fin 4),
  idx (mkvSeq (fun e0 : fin 4 => moe_term sel w eo e0 j)) e
  = (if sel e then mul (idx w e) (idx (idx eo e) j) else zero).
Proof.
  intros. rewrite idx_mkvSeq by lia. reflexivity.
Qed.

(* E = 4 block entry: output element j of the MoE feed-forward block is the
   guarded weighted sum over the 4 experts. *)
Example check_moeff_entry_E4 : forall (d df : nat)
  (Wg : exp (ary '{4} (ary '{d} num)))
  (W1s : exp (ary '{4} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{4} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{4} (ary '{d} (ary '{df} num))))
  (x : exp (ary '{d} num)) (j : fin d),
  idx (MoEFeedForward (E:=4) Wg W1s W3s W2s x) j
  = sum (mkvSeq (fun e : fin 4 =>
       moe_term (moe_sel (MatVec Wg x) (Top2Threshold (MatVec Wg x)))
                (TopKGate (MatVec Wg x))
                (moe_expert_outputs W1s W3s W2s x) e j)).
Proof.
  intros. unfold MoEFeedForward, MoE_combine.
  destruct d as [|d']. { destruct j as [? H]; lia. }
  rewrite idx_mkvSeq by lia. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions pair2_fst.
Print Assumptions pair2_snd.
Print Assumptions A_ArgMax.
Print Assumptions A_MaskExpert.
Print Assumptions A_Top2.
Print Assumptions A_moe_weight_cell.
Print Assumptions A_TopKGate.
Print Assumptions A_moe_term.
Print Assumptions A_MoE_combine.
Print Assumptions A_MatVec.
Print Assumptions A_ExpertGate.
Print Assumptions A_ExpertFFN.
Print Assumptions A_moe_expert_outputs.
Print Assumptions A_MoEFeedForward.
Print Assumptions check_top2_unroll4.
Print Assumptions check_argmax_unroll4.
Print Assumptions check_moeff_entry_E4.
