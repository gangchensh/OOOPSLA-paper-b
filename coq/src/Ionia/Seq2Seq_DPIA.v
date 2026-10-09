(* Seq2seq with Bahdanau (additive) attention — milestone N1c of the NLP/LLM
   extension plan (doc/NLP与LLM扩展开发规划_20260911.md), in the route-A
   R-based expression model.

   Network (all sizes symbolic: source length Ts, source embedding dx,
   hidden dh, decoder steps Td, classes nc):

     encoder: LSTM over prefixes of xs, giving ALL encoder hidden states
              (H[t] = hidden of LSTM(x_0..x_t)); the prefix read uses
              [take_upto] (bool-free index map, no spec0 in sight);
     attention: Bahdanau additive score
                score_i(h) = sum_k va_k * tanh((W1 H_i)_k + (W2 h)_k),
                weights = softmax(scores), context = sum_i w_i * H_i
              — [A_tanh1] (Ionia.Ops_RNN) + suml/mkvSeql templates +
                [Softmax1d] (Ionia.LeNet5_Functional);
     decoder: GRU over Td teacher-forced steps, the cell at step t reads
              Concat1d(y_t, context(h_{t-1})) — the autoregressive loop is
              the FIXED-step state fold [reduce (DecCell H) h0D ys], so no
              while/dynamic-loop primitive is needed (that is milestone N4);
     output:  Linear1d -> Softmax1d over the final decoder state.

   The attention context lives INSIDE the decoder cell as a pure
   expression, so the sequence-level correctness is again a direct
   instance of [A_reduce_gen] (Ionia.Ops_RNN).  The end-to-end theorem
   [A_Seq2SeqAttn] follows the buffer/bind_read discipline of
   [A_TextCNN] (Ionia.TextCNN_DPIA). *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* LSTM/GRU cells, sequence folds, [matvecdot]/[tanh1]. *)
Require Import Ionia.Ops_RNN.
(* [Concat1d]. *)
Require Import Ionia.TextCNN_DPIA.
(* [bind_read] elimination; [Linear1d]/[Softmax1d]. *)
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Prefix of a sequence (positions 0 .. t)                                     *)
(* -------------------------------------------------------------------------- *)

Lemma take_bound : forall (T : nat) (t : fin T) (i : fin (fin2nat t + 1)),
  (fin2nat i < T)%nat.
Proof.
  intros T t i. pose proof (fin_proof t). pose proof (fin_proof i). lia.
Qed.

(* The length-(t+1) prefix of xs. *)
Definition take_upto {T : nat} {s : data} (t : fin T) (xs : exp (ary '{T} s))
  : exp (ary '{fin2nat t + 1} s) :=
  mkvSeq (fun i : fin (fin2nat t + 1) => idx xs (nat2fin (take_bound t i))).

(* -------------------------------------------------------------------------- *)
(* Bahdanau additive attention                                                 *)
(* -------------------------------------------------------------------------- *)

(* score_i(h) = va . tanh(W1 H_i + W2 h)   (dot over the hidden axis). *)
Definition BahdanauScore {Ts dh : nat}
  (va : exp (ary '{dh} num))
  (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
  (H : exp (ary '{Ts} (ary '{dh} num))) (h : exp (ary '{dh} num))
  : exp (ary '{Ts} num) :=
  mkvSeq (fun i : fin Ts => sum (mkvSeq (fun k : fin dh =>
    mul (idx va k) (tanh1 (add (matvecdot W1 (idx H i) k)
                               (matvecdot W2 h k)))))).

Definition BahdanauScore_comm {Ts dh : nat}
  (va : exp (ary '{dh} num))
  (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
  (H : exp (ary '{Ts} (ary '{dh} num))) (h : exp (ary '{dh} num))
  (out : acc (ary '{Ts} num)) : comm :=
  mkvSeql (fun i oi => suml (mkvSeq (fun k : fin dh =>
    mul (idx va k) (tanh1 (add (matvecdot W1 (idx H i) k)
                               (matvecdot W2 h k)))))
            (fun r => oi |:= r) oi) out.

Lemma A_BahdanauScore : forall (Ts dh : nat)
  (va : exp (ary '{dh} num))
  (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
  (H : exp (ary '{Ts} (ary '{dh} num))) (h : exp (ary '{dh} num))
  (out : acc (ary '{Ts} num)),
  A(out, BahdanauScore va W1 W2 H h) = BahdanauScore_comm va W1 W2 H h out.
Proof.
  intros. unfold BahdanauScore, BahdanauScore_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_sum_acc. reflexivity.
Qed.

(* context(h) = sum_i softmax(score(h))_i * H_i   (weighted sum over time). *)
Definition BahdanauContext {Ts dh : nat}
  (va : exp (ary '{dh} num))
  (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
  (H : exp (ary '{Ts} (ary '{dh} num))) (h : exp (ary '{dh} num))
  : exp (ary '{dh} num) :=
  mkvSeq (fun k : fin dh => sum (mkvSeq (fun i : fin Ts =>
    mul (idx (Softmax1d (BahdanauScore va W1 W2 H h)) i)
        (idx (idx H i) k)))).

Definition BahdanauContext_comm {Ts dh : nat}
  (va : exp (ary '{dh} num))
  (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
  (H : exp (ary '{Ts} (ary '{dh} num))) (h : exp (ary '{dh} num))
  (out : acc (ary '{dh} num)) : comm :=
  mkvSeql (fun k ok => suml (mkvSeq (fun i : fin Ts =>
    mul (idx (Softmax1d (BahdanauScore va W1 W2 H h)) i)
        (idx (idx H i) k)))
            (fun r => ok |:= r) ok) out.

Lemma A_BahdanauContext : forall (Ts dh : nat)
  (va : exp (ary '{dh} num))
  (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
  (H : exp (ary '{Ts} (ary '{dh} num))) (h : exp (ary '{dh} num))
  (out : acc (ary '{dh} num)),
  A(out, BahdanauContext va W1 W2 H h) = BahdanauContext_comm va W1 W2 H h out.
Proof.
  intros. unfold BahdanauContext, BahdanauContext_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro k.
  rewrite A_sum_acc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Helper: projecting the hidden component out of a buffer of LSTM states     *)
(* -------------------------------------------------------------------------- *)

Definition ProjHidden {Ts dh : nat}
  (eP : exp (ary '{Ts} (ary '{2} (ary '{dh} num))))
  : exp (ary '{Ts} (ary '{dh} num)) :=
  mkvSeq (fun t : fin Ts => idx (idx eP t) st_h).

Definition ProjHidden_comm {Ts dh : nat}
  (eP : exp (ary '{Ts} (ary '{2} (ary '{dh} num))))
  (out : acc (ary '{Ts} (ary '{dh} num))) : comm :=
  seqfor (fun t : fin Ts => (out|{t}) |:= idx (idx eP t) st_h).

Lemma A_ProjHidden : forall (Ts dh : nat)
  (eP : exp (ary '{Ts} (ary '{2} (ary '{dh} num))))
  (out : acc (ary '{Ts} (ary '{dh} num))),
  A(out, ProjHidden eP) = ProjHidden_comm eP out.
Proof.
  intros. unfold ProjHidden, ProjHidden_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro t. reflexivity.
Qed.

(* Element access of a buffer accumulator built from a path:
   (acc' p)|{i} = acc' (AryIdx i p). *)
Lemma idxAcc_acc'_at : forall (T : nat) (d : data) (p : path) (i : fin T),
  idxAcc (@acc' (ary '{T} d) p) i = @acc' d (AryIdx i p).
Proof.
  intros. unfold idxAcc. rewrite acc'_ary. apply v_idx_mk_vec.
Qed.

(* -------------------------------------------------------------------------- *)
(* Seq2seq network                                                             *)
(* -------------------------------------------------------------------------- *)

Section Seq2SeqNet.

  Context (Ts dx dh Td nc : nat).

  (* Encoder LSTM (+ initial pair state), decoder GRU (input = token
     embedding concatenated with the dh-dim context, hence dx + dh),
     attention parameters, output head, source/target sequences. *)
  Context (psE : LSTMParams dx dh)
          (c0E h0E : exp (ary '{dh} num))
          (psD : GRUParams (dx + dh) dh)
          (h0D : exp (ary '{dh} num))
          (va : exp (ary '{dh} num))
          (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
          (Wo : exp (ary '{nc} (ary '{dh} num))) (bo : exp (ary '{nc} num))
          (xs : exp (ary '{Ts} (ary '{dx} num)))
          (ys : exp (ary '{Td} (ary '{dx} num))).

  (* ---------------- Functional network (opaque stage wrappers) ---------- *)

  (* Encoder pair-states over all prefixes. *)
  Definition EncPairs : exp (ary '{Ts} (ary '{2} (ary '{dh} num))) :=
    mkvSeq (fun t : fin Ts => LSTMSeq psE (lstm_state0 c0E h0E) (take_upto t xs)).
  (* All encoder hidden states. *)
  Definition s2s_H : exp (ary '{Ts} (ary '{dh} num)) := ProjHidden EncPairs.

  (* Decoder cell: GRU over (token embedding concatenated with the
     Bahdanau context of the current hidden state); the encoder hidden
     states [H] are a parameter so the imperative decoder can consume the
     value read back from the encoder buffer. *)
  Definition DecCell (H : exp (ary '{Ts} (ary '{dh} num)))
    (y : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
    : exp (ary '{dh} num) :=
    GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h.

  (* Fixed-step (teacher-forced) decoder fold. *)
  Definition dec_seq (H : exp (ary '{Ts} (ary '{dh} num))) : exp (ary '{dh} num) :=
    reduce (DecCell H) h0D ys.

  Definition s2s_dec : exp (ary '{dh} num) := dec_seq s2s_H.

  Definition s2s_logit : exp (ary '{nc} num) := Linear1d Wo bo s2s_dec.
  Definition s2s_soft : exp (ary '{nc} num) := Softmax1d s2s_logit.

  Lemma EncPairs_body : EncPairs =
    mkvSeq (fun t : fin Ts => LSTMSeq psE (lstm_state0 c0E h0E) (take_upto t xs)).
  Proof. reflexivity. Qed.
  Lemma s2s_H_body : s2s_H = ProjHidden EncPairs. Proof. reflexivity. Qed.
  Lemma s2s_dec_body : s2s_dec = dec_seq s2s_H. Proof. reflexivity. Qed.
  Lemma DecCell_body : forall (H : exp (ary '{Ts} (ary '{dh} num)))
    (y : exp (ary '{dx} num)) (h : exp (ary '{dh} num)),
    DecCell H y h = GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h.
  Proof. reflexivity. Qed.
  Lemma s2s_logit_body : s2s_logit = Linear1d Wo bo s2s_dec. Proof. reflexivity. Qed.
  Lemma s2s_soft_body : s2s_soft = Softmax1d s2s_logit. Proof. reflexivity. Qed.

  Opaque EncPairs s2s_H DecCell s2s_dec s2s_logit s2s_soft.

  Definition Seq2SeqAttn : exp (ary '{nc} num) := s2s_soft.

  (* ---------------- Imperative operator forms ---------------------------- *)

  (* Encoder: one LSTM run per prefix (naive O(T^2) recomputation — the
     honest scan sharing the running state is a further fusion lemma). *)
  Definition EncPairs_comm (out : acc (ary '{Ts} (ary '{2} (ary '{dh} num)))) : comm :=
    seqfor (fun t : fin Ts =>
      LSTMSeq_comm psE (lstm_state0 c0E h0E) (take_upto t xs) (out|{t})).

  Lemma A_EncPairs : forall (p : path),
    A(acc' p, EncPairs) = EncPairs_comm (acc' p).
  Proof.
    intros. rewrite EncPairs_body. unfold EncPairs_comm. rewrite AmkvSeq.
    apply seqfor_extensionality. intro t.
    rewrite (idxAcc_acc'_at (ary '{2} (ary '{dh} num)) p t).
    apply A_LSTMSeq.
  Qed.

  (* Decoder fold: a direct [A_reduce_gen] instance — the attention context
     is a pure subexpression of the cell, so no new rule is needed. *)
  Definition dec_seq_comm (H : exp (ary '{Ts} (ary '{dh} num)))
    (out : acc (ary '{dh} num)) : comm :=
    reducel (DecCell H) h0D ys (fun r => A(out, r)) out.

  Lemma A_dec_seq : forall (H : exp (ary '{Ts} (ary '{dh} num))) (p : path),
    A(acc' p, dec_seq H) = dec_seq_comm H (acc' p).
  Proof.
    intros. unfold dec_seq, dec_seq_comm. apply A_reduce_gen.
  Qed.  (* Cell-level rule: the decoder cell is the GRU cell on the concatenated
     input (direct instance of [A_GRUCell]). *)
  Lemma A_DecCell : forall (H : exp (ary '{Ts} (ary '{dh} num)))
    (y : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
    (out : acc (ary '{dh} num)),
    A(out, DecCell H y h) =
    GRUCell_comm psD (Concat1d y (BahdanauContext va W1 W2 H h)) h out.
  Proof. intros. rewrite DecCell_body. apply A_GRUCell. Qed.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition seq2seq_comm (output : acc (ary '{nc} num)) : comm :=
new (fun tE => EncPairs_comm tE ';
bind_read tE (fun eP =>
new (fun tH => ProjHidden_comm eP tH ';
bind_read tH (fun eH =>
new (fun tD => dec_seq_comm eH tD ';
bind_read tD (fun eD =>
new (fun tL => Linear1d_comm Wo bo eD tL ';
bind_read tL (fun eL => Softmax1d_comm eL output)
) (acc' (Var "sl"))
)) (acc' (Var "sd"))
)) (acc' (Var "sh"))
)) (acc' (Var "se")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition seq2seq_direct (output : acc (ary '{nc} num)) : comm :=
    A(acc' (Var "se"), EncPairs) ';
    A(acc' (Var "sh"), s2s_H) ';
    A(acc' (Var "sd"), s2s_dec) ';
    A(acc' (Var "sl"), s2s_logit) ';
    A(output, s2s_soft).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition seq2seq_fresh (output : acc (ary '{nc} num)) (rho : env) : Prop :=
    StructUndefined (acc' (Var "se") : acc (ary '{Ts} (ary '{2} (ary '{dh} num)))) rho /\
    StructUndefined (acc' (Var "sh") : acc (ary '{Ts} (ary '{dh} num))) rho /\
    StructUndefined (acc' (Var "sd") : acc (ary '{dh} num)) rho /\
    StructUndefined (acc' (Var "sl") : acc (ary '{nc} num)) rho /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "se") : acc (ary '{Ts} (ary '{2} (ary '{dh} num))))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "sh") : acc (ary '{Ts} (ary '{dh} num)))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "sd") : acc (ary '{dh} num))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "sl") : acc (ary '{nc} num))).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma seq2seq_comm_eq_direct :
    forall (output : acc (ary '{nc} num)),
    seq2seq_comm output = seq2seq_direct output.
  Proof.
    intros.
    unfold seq2seq_comm, seq2seq_direct, new.
    cbv beta.
    rewrite <- A_EncPairs.
    rewrite bind_read_replace.
    rewrite <- A_ProjHidden.
    rewrite <- s2s_H_body.
    rewrite bind_read_replace.
    rewrite <- A_dec_seq.
    rewrite <- s2s_dec_body.
    rewrite bind_read_replace.
    rewrite <- A_Linear1d.
    rewrite <- s2s_logit_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax1d.
    rewrite <- s2s_soft_body.
    reflexivity.
  Qed.

  Lemma A_Seq2SeqAttn_direct :
    forall (output : acc (ary '{nc} num)) (rho : env) (p : path),
    in_acc p output ->
    seq2seq_fresh output rho ->
    seq2seq_direct output rho p = A(output, Seq2SeqAttn) rho p.
  Proof.
    intros.
    unfold seq2seq_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold Seq2SeqAttn. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of Seq2seq+Attention: under freshness of
     the temporary buffers, the imperative network observed at an output
     path computes the functional [Seq2SeqAttn]. *)
  Theorem A_Seq2SeqAttn :
    forall (output : acc (ary '{nc} num)) (rho : env) (p : path),
    in_acc p output ->
    seq2seq_fresh output rho ->
    seq2seq_comm output rho p = A(output, Seq2SeqAttn) rho p.
  Proof.
    intros. rewrite seq2seq_comm_eq_direct.
    apply A_Seq2SeqAttn_direct; assumption.
  Qed.

End Seq2SeqNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: Ts = 8, dx = 2, dh = 2, Td = 4, nc = 3 (fin-8 scale)    *)
(* -------------------------------------------------------------------------- *)

Definition s2s_i0_3 : fin 3 := @nat2fin 3 0 (ltac:(lia)).
Definition s2s_i2_8 : fin 8 := @nat2fin 8 2 (ltac:(lia)).
Definition s2s_i0_8 : fin 8 := @nat2fin 8 0 (ltac:(lia)).
Definition s2s_i1_2 : fin 2 := @nat2fin 2 1 (ltac:(lia)).

Section Small_8_2_2_4_3.

  Context (psEs : LSTMParams 2 2)
          (c0Es h0Es : exp (ary '{2} num))
          (psDs : GRUParams 4 2)
          (h0Ds : exp (ary '{2} num))
          (vas : exp (ary '{2} num))
          (W1s W2s : exp (ary '{2} (ary '{2} num)))
          (Wos : exp (ary '{3} (ary '{2} num))) (bos : exp (ary '{3} num))
          (xss : exp (ary '{8} (ary '{2} num)))
          (yss : exp (ary '{4} (ary '{2} num)))
          (outs : acc (ary '{3} num)).

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition Seq2SeqAttn_8_2_2_4_3 : exp (ary '{3} num) :=
    @Seq2SeqAttn 8 2 2 4 3 psEs c0Es h0Es psDs h0Ds vas W1s W2s Wos bos xss yss.

  Definition seq2seq_comm_8_2_2_4_3 : comm :=
    @seq2seq_comm 8 2 2 4 3 psEs c0Es h0Es psDs h0Ds vas W1s W2s Wos bos xss yss outs.

End Small_8_2_2_4_3.

(* [vm_compute]/conversion spot checks of the structural parts. *)

(* Prefix read: (take_upto 2 xs)[0] = xs[0] at T = 8. *)
Example check_take_upto :
  forall (xs8 : exp (ary '{8} num)),
  idx (take_upto s2s_i2_8 xs8) s2s_i0_3 = idx xs8 s2s_i0_8.
Proof. reflexivity. Qed.

(* Bahdanau score entry (Ts = 2, dh = 2). *)
Example check_score_entry :
  forall (va : exp (ary '{2} num)) (W1 W2 : exp (ary '{2} (ary '{2} num)))
    (H : exp (ary '{2} (ary '{2} num))) (h : exp (ary '{2} num)),
  idx (BahdanauScore va W1 W2 H h) s2s_i1_2 =
  sum (mkvSeq (fun k : fin 2 =>
    mul (idx va k) (tanh1 (add (matvecdot W1 (idx H s2s_i1_2) k)
                               (matvecdot W2 h k))))).
Proof. reflexivity. Qed.

(* Decoder fold unrolls over Td = 4 teacher-forced steps, context
   recomputed from the running hidden state each step. *)
Example check_dec_unroll4 :
  forall (Ts dx dh : nat)
    (psD : GRUParams (dx + dh) dh)
    (va : exp (ary '{dh} num)) (W1 W2 : exp (ary '{dh} (ary '{dh} num)))
    (H : exp (ary '{Ts} (ary '{dh} num)))
    (h0 : exp (ary '{dh} num))
    (y0 y1 y2 y3 : exp (ary '{dx} num)),
  reduce (fun y h => GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h)
         h0 (((((tt, y0), y1), y2), y3) : exp (ary '{4} (ary '{dx} num))) =
  (fun y h => GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h) y3
  ((fun y h => GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h) y2
  ((fun y h => GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h) y1
  ((fun y h => GRUCell psD (Concat1d y (BahdanauContext va W1 W2 H h)) h) y0 h0))).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_BahdanauScore.
Print Assumptions A_BahdanauContext.
Print Assumptions A_ProjHidden.
Print Assumptions A_EncPairs.
Print Assumptions A_dec_seq.
Print Assumptions A_DecCell.
Print Assumptions A_Seq2SeqAttn.
