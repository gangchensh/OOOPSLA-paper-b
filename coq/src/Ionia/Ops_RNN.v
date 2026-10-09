(* DPIA-style rules for recurrent networks — milestone N1a of the NLP/LLM
   extension plan (doc/NLP与LLM扩展开发规划_20260911.md): RNN / LSTM / GRU
   cells and the sequence-level state-fold rule, in the route-A R-based
   expression model.

   Key idea: the hidden-state recurrence h_t = cell(x_t, h_{t-1}) IS the
   accumulator fold [reduce cell h0 xs], and its imperative realisation is
   the [reducel] skeleton of Ionia.DPIA_Rules (temp accumulator + [seqfor]
   over time steps).  [A_reduce_num] in DPIA_Rules is specialised to scalar
   ([num]) accumulators; the RNN hidden state is a VECTOR, so this file
   first generalises the reduction chain to accumulators of arbitrary data
   type:

     [assign_shadow]     a later assignment to the same accumulator
                         overwrites an earlier one (from
                         [assign_pure_independent] / [assign_not_in_acc]);
     [assign_update_gen] store e1 then store f(read-back) = store (f e1),
                         the general-[d] form of [assign_update_num];
     [reduce_aux_gen]    init-assign + seqfor loop = single assign of the
                         fold, general-[t] form of [reduce_aux_num];
     [A_reduce_gen]      A(acc' p, reduce op init xs) = reducel skeleton —
                         general-[t] form of [A_reduce_num].

   The RNN/LSTM/GRU sequence theorems are direct instances of
   [A_reduce_gen]; the cell theorems follow the Ops_Elementwise template
   (AmkvSeq + pointwise reflexivity).

   LSTM dual state (c, h): encoded as the length-2 array
   [ary '{2} (ary '{dh} num)] — the zero-cost isomorphic-pair encoding of
   the 2026-09-11 discussion (topic 2).  Because [A_reduce_gen] is fully
   general in the accumulator type, this encoding needs NO dual-accumulator
   [reducel2] variant: [reducel] already accepts t := ary '{2} _.
   Index convention: [st_c] (= 0) selects the cell state, [st_h] (= 1) the
   hidden state. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
From Stdlib Require Import Classical_Prop.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Generalised reduction machinery (arbitrary accumulator data type)          *)
(* -------------------------------------------------------------------------- *)

(* A later assignment to the same accumulator shadows an earlier one.
   Pointwise: inside the footprint the value is environment-independent
   ([assign_pure_independent]); outside, both assignments are no-ops
   ([assign_not_in_acc]). *)
Lemma assign_shadow : forall (d:data) (a : acc d) (e1 e2 : exp d),
  (a |:= e1) '; (a |:= e2) = a |:= e2.
Proof.
  intros. apply functional_extensionality. intro rho.
  apply functional_extensionality. intro q.
  unfold seq.
  destruct (classic (in_acc q a)) as [Hin | Hout].
  - apply assign_pure_independent. exact Hin.
  - rewrite (assign_not_in_acc d a e2 _ q Hout).
    rewrite (assign_not_in_acc d a e1 rho q Hout).
    rewrite (assign_not_in_acc d a e2 rho q Hout).
    reflexivity.
Qed.

(* Generalisation of [assign_update_num] (DPIA_Rules) to arbitrary data:
   store [e1], then read the accumulator back and store [f] of the read
   value — the net effect is storing [f e1]. *)
Lemma assign_update_gen : forall (d:data) (p : path) (e1 : exp d)
    (f : exp d -> exp d),
  ((acc' p) |:= e1) '; (fun rho => ((acc' p) |:= f (read_exp rho (acc' p))) rho)
  = (acc' p) |:= f e1.
Proof.
  intros. apply functional_extensionality. intro rho.
  unfold seq. cbv beta. rewrite read_exp_assign.
  pose proof (assign_shadow d (acc' p) e1 (f e1)) as Hs.
  apply (f_equal (fun c : comm => c rho)) in Hs. exact Hs.
Qed.

(* Generalisation of [reduce_aux_num] (DPIA_Rules): an initialised
   accumulator at path [p] followed by the [seqfor] update loop leaves
   exactly [reduce op init xs] at [p].  The proof mirrors the scalar
   version step by step; only [assign_update_num] is replaced by
   [assign_update_gen]. *)
Lemma reduce_aux_gen : forall (n:nat) (s t:data)
  (op : exp s -> exp t -> exp t) (init : exp t)
  (xs : exp (ary '{n} s)) (p : path),
  ((acc' p) |:= init) '; seqfor (fun i : fin n => fun rho =>
    ((acc' p) |:= op (xs|[i]) (read_exp rho (acc' p))) rho)
  = (acc' p) |:= reduce op init xs.
Proof.
  induction n as [| n' IHn]; intros.
  - (* n = 0 *)
    apply functional_extensionality. intro rho.
    unfold seq, reduce. reflexivity.
  - (* n = S n' *)
    apply functional_extensionality. intro rho.
    destruct xs as [xs' x].
    rewrite seqfor_Sn.
    replace (seqfor (fun (i : fin n') (rho0 : env) =>
               ((acc' p) |:= op ((xs', x) : exp (ary '{S n'} s))|[FS[i]]
                          (read_exp rho0 (acc' p))) rho0))
      with (seqfor (fun (i : fin n') (rho0 : env) =>
               ((acc' p) |:= op (xs'|[i]) (read_exp rho0 (acc' p))) rho0)).
    + rewrite (seq_assoc ((acc' p) |:= init)
                (seqfor (fun (i : fin n') (rho0 : env) =>
                   ((acc' p) |:= op (xs'|[i]) (read_exp rho0 (acc' p))) rho0))
                (fun rho0 : env =>
                   ((acc' p) |:= op ((xs', x) : exp (ary '{S n'} s))|['[n']]
                              (read_exp rho0 (acc' p))) rho0)).
      rewrite (IHn s t op init xs' p).
      rewrite assign_update_gen.
      rewrite ary_idx_last. rewrite reduce_Sn. reflexivity.
    + apply seqfor_extensionality. intro i.
      apply functional_extensionality. intro rho0.
      unfold idx, v_idx. simpl.
      assert (Hneq : (i =? n')%nat = false).
      { pose proof (fin_proof i) as Hlt.
        destruct (i =? n')%nat eqn:E; auto.
        exfalso. apply Nat.eqb_eq in E. lia. }
      rewrite Hneq. reflexivity.
Qed.

(* The core state-fold rule: translating [reduce op init xs] to output
   path [p] is the [reducel] skeleton (temp accumulator at [p], [seqfor]
   over the sequence, final copy-out).  Generalises [A_reduce_num] from
   scalar to arbitrary accumulators — this is what makes hidden-state
   vectors (and the LSTM pair encoding) foldable. *)
Lemma A_reduce_gen : forall (n:nat) (s t:data)
  (op : exp s -> exp t -> exp t) (init : exp t)
  (xs : exp (ary '{n} s)) (p : path),
  A(acc' p, reduce op init xs) =
  reducel op init xs (fun r => A(acc' p, r)) (acc' p).
Proof.
  intros. unfold A, reducel, new.
  rewrite (seq_assoc ((acc' p) |:= init)
                     (seqfor (fun i : fin n => fun rho =>
                        ((acc' p) |:= op (xs|[i]) (read_exp rho (acc' p))) rho))
                     (fun rho => ((acc' p) |:= (read_exp rho (acc' p))) rho)).
  rewrite reduce_aux_gen.
  replace (fun rho : env => ((acc' p) |:= read_exp rho (acc' p)) rho)
    with (fun rho : env => ((acc' p) |:= (fun old : exp t => old)
                              (read_exp rho (acc' p))) rho).
  - rewrite (assign_update_gen t p (reduce op init xs) (fun old : exp t => old)).
    reflexivity.
  - apply functional_extensionality. intro rho. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Scalar activations (reflexivity-shaped rules, cf. A_gelu_tanh)             *)
(* -------------------------------------------------------------------------- *)

(* sigmoid x = 1 / (1 + exp(-x))   (cf. Sigmoid2d in Ionia.Ops_Elementwise) *)
Definition sig1 (x : exp num) : exp num :=
  div one (add one (pExp (negate x))).

(* tanh x = (exp x - exp(-x)) / (exp x + exp(-x))   (cf. gelu_tanh in
   Ionia.Ops_Transformer, Tanh2d in Ionia.Ops_Elementwise) *)
Definition tanh1 (x : exp num) : exp num :=
  div (sub (pExp x) (pExp (negate x)))
      (add (pExp x) (pExp (negate x))).

Lemma A_sig1 : forall (a : acc num) (e : exp num),
  A(a, sig1 e) = C(e, fun r => a |:= sig1 r).
Proof. reflexivity. Qed.

Lemma A_tanh1 : forall (a : acc num) (e : exp num),
  A(a, tanh1 e) = C(e, fun r => a |:= tanh1 r).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Shared cell plumbing                                                        *)
(* -------------------------------------------------------------------------- *)

(* Dot product of row [i] of [M] with [v]: sum_j M[i,j] * v[j]. *)
Definition matvecdot {m n : nat}
  (M : exp (ary '{m} (ary '{n} num))) (v : exp (ary '{n} num)) (i : fin m)
  : exp num :=
  sum (mkvSeq (fun j : fin n => mul (idx (idx M i) j) (idx v j))).

(* Affine pre-activation W x + U h + b at hidden unit [k]. *)
Definition gate_pre {dx dh : nat}
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (k : fin dh) : exp num :=
  add (add (matvecdot W x k) (matvecdot U h k)) (idx b k).

(* -------------------------------------------------------------------------- *)
(* RNN cell: h' = tanh(W x + U h + b)                                          *)
(* -------------------------------------------------------------------------- *)

Definition rnn_body {dx dh : nat}
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (k : fin dh) : exp num :=
  tanh1 (gate_pre W U b x h k).

Definition RNNCell {dx dh : nat}
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  : exp (ary '{dh} num) :=
  mkvSeq (rnn_body W U b x h).

Definition RNNCell_comm {dx dh : nat}
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (out : acc (ary '{dh} num)) : comm :=
  seqfor (fun k : fin dh => (out|{k}) |:= rnn_body W U b x h k).

Lemma A_RNNCell : forall (dx dh : nat)
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (out : acc (ary '{dh} num)),
  A(out, RNNCell W U b x h) = RNNCell_comm W U b x h out.
Proof.
  intros. unfold RNNCell, RNNCell_comm.
  rewrite AmkvSeq. apply seqfor_extensionality. intro k. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* RNN sequence: h_T = cell(x_{T-1}, cell(..., cell(x_0, h0)))                 *)
(* -------------------------------------------------------------------------- *)

Definition RNNSeq {T dx dh : nat}
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (h0 : exp (ary '{dh} num))
  (xs : exp (ary '{T} (ary '{dx} num)))
  : exp (ary '{dh} num) :=
  reduce (RNNCell W U b) h0 xs.

Definition RNNSeq_comm {T dx dh : nat}
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (h0 : exp (ary '{dh} num))
  (xs : exp (ary '{T} (ary '{dx} num)))
  (out : acc (ary '{dh} num)) : comm :=
  reducel (RNNCell W U b) h0 xs (fun r => A(out, r)) out.

Lemma A_RNNSeq : forall (T dx dh : nat)
  (W : exp (ary '{dh} (ary '{dx} num)))
  (U : exp (ary '{dh} (ary '{dh} num)))
  (b : exp (ary '{dh} num))
  (h0 : exp (ary '{dh} num))
  (xs : exp (ary '{T} (ary '{dx} num)))
  (p : path),
  A(acc' p, RNNSeq W U b h0 xs) = RNNSeq_comm W U b h0 xs (acc' p).
Proof.
  intros. unfold RNNSeq, RNNSeq_comm. apply A_reduce_gen.
Qed.

(* -------------------------------------------------------------------------- *)
(* LSTM: dual state encoded as ary '{2} (ary '{dh} num)                        *)
(* -------------------------------------------------------------------------- *)

Record LSTMParams (dx dh : nat) : Set := mkLSTMParams {
  lWi : exp (ary '{dh} (ary '{dx} num));
  lUi : exp (ary '{dh} (ary '{dh} num));
  lbi : exp (ary '{dh} num);
  lWf : exp (ary '{dh} (ary '{dx} num));
  lUf : exp (ary '{dh} (ary '{dh} num));
  lbf : exp (ary '{dh} num);
  lWo : exp (ary '{dh} (ary '{dx} num));
  lUo : exp (ary '{dh} (ary '{dh} num));
  lbo : exp (ary '{dh} num);
  lWg : exp (ary '{dh} (ary '{dx} num));
  lUg : exp (ary '{dh} (ary '{dh} num));
  lbg : exp (ary '{dh} num)
}.

(* State indices in the pair encoding: 0 = cell state c, 1 = hidden h. *)
Definition st_c : fin 2 := fin0n 1.
Definition st_h : fin 2 := fin_last 1.

(* Select branch 0/1 of the pair encoding. *)
Definition sel2 {d : data} (u v : exp d) (j : fin 2) : exp d :=
  if (fin2nat j =? 0)%nat then u else v.

Lemma sel2_c : forall (d:data) (u v : exp d), sel2 u v st_c = u.
Proof. reflexivity. Qed.

Lemma sel2_h : forall (d:data) (u v : exp d), sel2 u v st_h = v.
Proof. reflexivity. Qed.

(* Pair of dh-vectors as a length-2 array (the initial state (c0, h0)). *)
Definition lstm_state0 {dh : nat} (c0 h0 : exp (ary '{dh} num))
  : exp (ary '{2} (ary '{dh} num)) :=
  mkvSeq (sel2 c0 h0).

(* c' = f . c + i . g   (i/f = sigmoid gates, g = tanh candidate) *)
Definition lstm_c_next {dx dh : nat} (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num)))
  : exp (ary '{dh} num) :=
  let c := idx st st_c in
  let h := idx st st_h in
  let ig := mkvSeq (fun k : fin dh => sig1 (gate_pre (lWi ps) (lUi ps) (lbi ps) x h k)) in
  let fg := mkvSeq (fun k : fin dh => sig1 (gate_pre (lWf ps) (lUf ps) (lbf ps) x h k)) in
  let gg := mkvSeq (fun k : fin dh => tanh1 (gate_pre (lWg ps) (lUg ps) (lbg ps) x h k)) in
  mkvSeq (fun k : fin dh => add (mul (idx fg k) (idx c k)) (mul (idx ig k) (idx gg k))).

(* h' = o . tanh(c') *)
Definition lstm_h_next {dx dh : nat} (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num)))
  : exp (ary '{dh} num) :=
  let h := idx st st_h in
  let og := mkvSeq (fun k : fin dh => sig1 (gate_pre (lWo ps) (lUo ps) (lbo ps) x h k)) in
  mkvSeq (fun k : fin dh => mul (idx og k) (tanh1 (idx (lstm_c_next ps x st) k))).

Definition LSTMCell {dx dh : nat} (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num)))
  : exp (ary '{2} (ary '{dh} num)) :=
  mkvSeq (sel2 (lstm_c_next ps x st) (lstm_h_next ps x st)).

Definition LSTMCell_comm {dx dh : nat} (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num)))
  (out : acc (ary '{2} (ary '{dh} num))) : comm :=
  seqfor (fun j : fin 2 =>
    (out|{j}) |:= sel2 (lstm_c_next ps x st) (lstm_h_next ps x st) j).

Lemma A_LSTMCell : forall (dx dh : nat) (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num)))
  (out : acc (ary '{2} (ary '{dh} num))),
  A(out, LSTMCell ps x st) = LSTMCell_comm ps x st out.
Proof.
  intros. unfold LSTMCell, LSTMCell_comm.
  rewrite AmkvSeq. apply seqfor_extensionality. intro j. reflexivity.
Qed.

(* The two branches of the pair encoding really are c' and h'. *)
Lemma LSTMCell_sel_c : forall (dx dh : nat) (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num))),
  idx (LSTMCell ps x st) st_c = lstm_c_next ps x st.
Proof.
  intros. unfold LSTMCell. rewrite idx_mkvSeq by lia. apply sel2_c.
Qed.

Lemma LSTMCell_sel_h : forall (dx dh : nat) (ps : LSTMParams dx dh)
  (x : exp (ary '{dx} num)) (st : exp (ary '{2} (ary '{dh} num))),
  idx (LSTMCell ps x st) st_h = lstm_h_next ps x st.
Proof.
  intros. unfold LSTMCell. rewrite idx_mkvSeq by lia. apply sel2_h.
Qed.

(* -------------------------------------------------------------------------- *)
(* LSTM sequence                                                               *)
(* -------------------------------------------------------------------------- *)

Definition LSTMSeq {T dx dh : nat} (ps : LSTMParams dx dh)
  (st0 : exp (ary '{2} (ary '{dh} num)))
  (xs : exp (ary '{T} (ary '{dx} num)))
  : exp (ary '{2} (ary '{dh} num)) :=
  reduce (LSTMCell ps) st0 xs.

Definition LSTMSeq_comm {T dx dh : nat} (ps : LSTMParams dx dh)
  (st0 : exp (ary '{2} (ary '{dh} num)))
  (xs : exp (ary '{T} (ary '{dx} num)))
  (out : acc (ary '{2} (ary '{dh} num))) : comm :=
  reducel (LSTMCell ps) st0 xs (fun r => A(out, r)) out.

(* The LSTM sequence fold is a DIRECT instance of [A_reduce_gen] with
   t := ary '{2} (ary '{dh} num): no dual-accumulator reducel variant is
   needed, because the generalised rule already folds array-typed state. *)
Lemma A_LSTMSeq : forall (T dx dh : nat) (ps : LSTMParams dx dh)
  (st0 : exp (ary '{2} (ary '{dh} num)))
  (xs : exp (ary '{T} (ary '{dx} num)))
  (p : path),
  A(acc' p, LSTMSeq ps st0 xs) = LSTMSeq_comm ps st0 xs (acc' p).
Proof.
  intros. unfold LSTMSeq, LSTMSeq_comm. apply A_reduce_gen.
Qed.

(* -------------------------------------------------------------------------- *)
(* GRU cell: z = sig(Wz x + Uz h + bz); r = sig(Wr x + Ur h + br);            *)
(*           n = tanh(Wn x + r . (Un h) + bn);  h' = (1 - z) . n + z . h      *)
(* -------------------------------------------------------------------------- *)

Record GRUParams (dx dh : nat) : Set := mkGRUParams {
  gWz : exp (ary '{dh} (ary '{dx} num));
  gUz : exp (ary '{dh} (ary '{dh} num));
  gbz : exp (ary '{dh} num);
  gWr : exp (ary '{dh} (ary '{dx} num));
  gUr : exp (ary '{dh} (ary '{dh} num));
  gbr : exp (ary '{dh} num);
  gWn : exp (ary '{dh} (ary '{dx} num));
  gUn : exp (ary '{dh} (ary '{dh} num));
  gbn : exp (ary '{dh} num)
}.

Definition gru_body {dx dh : nat} (ps : GRUParams dx dh)
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (k : fin dh) : exp num :=
  let z := sig1 (gate_pre (gWz ps) (gUz ps) (gbz ps) x h k) in
  let r := sig1 (gate_pre (gWr ps) (gUr ps) (gbr ps) x h k) in
  let n := tanh1 (add (add (matvecdot (gWn ps) x k)
                           (mul r (matvecdot (gUn ps) h k)))
                      (idx (gbn ps) k)) in
  add (mul (sub one z) n) (mul z (idx h k)).

Definition GRUCell {dx dh : nat} (ps : GRUParams dx dh)
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  : exp (ary '{dh} num) :=
  mkvSeq (gru_body ps x h).

Definition GRUCell_comm {dx dh : nat} (ps : GRUParams dx dh)
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (out : acc (ary '{dh} num)) : comm :=
  seqfor (fun k : fin dh => (out|{k}) |:= gru_body ps x h k).

Lemma A_GRUCell : forall (dx dh : nat) (ps : GRUParams dx dh)
  (x : exp (ary '{dx} num)) (h : exp (ary '{dh} num))
  (out : acc (ary '{dh} num)),
  A(out, GRUCell ps x h) = GRUCell_comm ps x h out.
Proof.
  intros. unfold GRUCell, GRUCell_comm.
  rewrite AmkvSeq. apply seqfor_extensionality. intro k. reflexivity.
Qed.

Definition GRUSeq {T dx dh : nat} (ps : GRUParams dx dh)
  (h0 : exp (ary '{dh} num))
  (xs : exp (ary '{T} (ary '{dx} num)))
  : exp (ary '{dh} num) :=
  reduce (GRUCell ps) h0 xs.

Definition GRUSeq_comm {T dx dh : nat} (ps : GRUParams dx dh)
  (h0 : exp (ary '{dh} num))
  (xs : exp (ary '{T} (ary '{dx} num)))
  (out : acc (ary '{dh} num)) : comm :=
  reducel (GRUCell ps) h0 xs (fun r => A(out, r)) out.

Lemma A_GRUSeq : forall (T dx dh : nat) (ps : GRUParams dx dh)
  (h0 : exp (ary '{dh} num))
  (xs : exp (ary '{T} (ary '{dx} num)))
  (p : path),
  A(acc' p, GRUSeq ps h0 xs) = GRUSeq_comm ps h0 xs (acc' p).
Proof.
  intros. unfold GRUSeq, GRUSeq_comm. apply A_reduce_gen.
Qed.

(* -------------------------------------------------------------------------- *)
(* Small-instance computational spot checks (fin-8 scale)                     *)
(* -------------------------------------------------------------------------- *)

(* Functional spot check: the length-8 fold unrolls to the 8-step nest,
   oldest input innermost (chronological time order). *)
Example rnn_seq_unroll8 : forall (dx dh : nat)
  (cell : exp (ary '{dx} num) -> exp (ary '{dh} num) -> exp (ary '{dh} num))
  (h0 : exp (ary '{dh} num))
  (x0 x1 x2 x3 x4 x5 x6 x7 : exp (ary '{dx} num)),
  reduce cell h0
    (((((((((tt, x0), x1), x2), x3), x4), x5), x6), x7)
      : exp (ary '{8} (ary '{dx} num)))
  = cell x7 (cell x6 (cell x5 (cell x4 (cell x3 (cell x2 (cell x1 (cell x0 h0))))))).
Proof. reflexivity. Qed.

(* Imperative spot check: running the 8-step [reducel] loop and copying the
   accumulator to path [p] stores exactly the functional fold there.  This
   goes through the proved rule [A_reduce_gen] plus definitional unrolling. *)
Example rnn_seq_comm_env8 : forall (dx dh : nat)
  (cell : exp (ary '{dx} num) -> exp (ary '{dh} num) -> exp (ary '{dh} num))
  (h0 : exp (ary '{dh} num))
  (x0 x1 x2 x3 x4 x5 x6 x7 : exp (ary '{dx} num))
  (p : path) (rho : env),
  reducel cell h0
    (((((((((tt, x0), x1), x2), x3), x4), x5), x6), x7)
      : exp (ary '{8} (ary '{dx} num)))
    (fun r => A(acc' p, r)) (acc' p) rho
  = assign (acc' p)
      (cell x7 (cell x6 (cell x5 (cell x4 (cell x3 (cell x2 (cell x1 (cell x0 h0)))))))) rho.
Proof.
  intros. rewrite <- A_reduce_gen. reflexivity.
Qed.

(* LSTM encoding spot check: the pair encoding of (c0, h0) projects back to
   its components. *)
Example lstm_state0_sel : forall (dh : nat) (c0 h0 : exp (ary '{dh} num)),
  idx (lstm_state0 c0 h0) st_c = c0 /\ idx (lstm_state0 c0 h0) st_h = h0.
Proof.
  intros. unfold lstm_state0. split.
  - rewrite idx_mkvSeq by lia. apply sel2_c.
  - rewrite idx_mkvSeq by lia. apply sel2_h.
Qed.

(* LSTM sequence spot check: the length-2 fold unrolls to the two-step
   nest of dual-state cells. *)
Example lstm_seq_unroll2 : forall (dx dh : nat) (ps : LSTMParams dx dh)
  (st0 : exp (ary '{2} (ary '{dh} num)))
  (x0 x1 : exp (ary '{dx} num)),
  LSTMSeq (T:=2) ps st0
    (((tt, x0), x1) : exp (ary '{2} (ary '{dx} num)))
  = LSTMCell ps x1 (LSTMCell ps x0 st0).
Proof. reflexivity. Qed.

(* GRU sequence spot check: same two-step unrolling. *)
Example gru_seq_unroll2 : forall (dx dh : nat) (ps : GRUParams dx dh)
  (h0 : exp (ary '{dh} num))
  (x0 x1 : exp (ary '{dx} num)),
  GRUSeq (T:=2) ps h0
    (((tt, x0), x1) : exp (ary '{2} (ary '{dx} num)))
  = GRUCell ps x1 (GRUCell ps x0 h0).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions assign_shadow.
Print Assumptions assign_update_gen.
Print Assumptions reduce_aux_gen.
Print Assumptions A_reduce_gen.
Print Assumptions A_sig1.
Print Assumptions A_tanh1.
Print Assumptions A_RNNCell.
Print Assumptions A_RNNSeq.
Print Assumptions A_LSTMCell.
Print Assumptions A_LSTMSeq.
Print Assumptions A_GRUCell.
Print Assumptions A_GRUSeq.
Print Assumptions rnn_seq_unroll8.
Print Assumptions rnn_seq_comm_env8.
Print Assumptions lstm_state0_sel.
Print Assumptions lstm_seq_unroll2.
Print Assumptions gru_seq_unroll2.
