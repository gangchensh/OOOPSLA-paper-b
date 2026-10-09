(* DPIA-style Leibniz equivalence proofs for a BERT-style encoder network
   (milestone N2a of the NLP/LLM extension, cf.
   doc/NLP与LLM扩展开发规划_20260911.md section 2-N2) in the route-A R-based
   expression model, as a variant of Ionia.MiniTransformer_DPIA (GPT-style
   decoder).

   The three BERT-specific deltas relative to MiniTransformer:

   - Bidirectional (unmasked) attention: [BAttention_cell] is
     softmax(Q K^T / sqrt(d)) V without the [CausalMask2d] stage;
     [BMHABlock] is the corresponding multi-head block (same structure as
     Ionia.Attention_DPIA.MHABlock, distinct buffer names bmq..bmmg).

   - Post-norm residual structure (original BERT): the encoder block is
        r1 = LN1(x + MHA(x))
        r2 = LN2(r1 + FFN(r1))
     i.e. LayerNorm AFTER each residual add, whereas MiniTransformer's
     pre-norm block computes x + MHA(LN1(x)) / r1 + FFN(LN2(r1)).  The block
     therefore stages seven buffers (attention, add, norm, ffn x3, add) and
     the final LayerNorm writes the block output directly.

   - Token + segment + position embeddings summed at the input, [CLS]
     pooling (row 0 of the final hidden states, index passed explicitly so
     the operator needs no positivity hypothesis) and a pooler/output head
     (Linear -> tanh -> Linear over nc classes).

   Delivered (all closed with [Qed], no Admitted/Axiom):
   [A_BAttention_cell], [A_BAttnHeads], [bmhablock_comm_eq_direct],
   [A_BMHABlock], [A_Tanh2d], [A_CLSPool], [bertblock_comm_eq_direct],
   [A_BERTEncoderBlock], [bertblock_direct_read], and the end-to-end
   [A_BERTMini]: under freshness of the temporary buffers, the imperative
   network observed at an output path equals the functional [BERTMini]
   (pointwise observational equivalence).  All sizes symbolic; a concrete
   b=1, s=8, h=2, d=16, df=32, v=8, sg=2, nc=4 instance and [vm_compute]
   spot checks of the computable parts. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* [bind_read] and the bind_read elimination lemmas. *)
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
(* [bind_read_replace_seq_r] (left-associated prefix variant). *)
Require Import Ionia.ResNet18_DPIA.
(* [Add3d] / [A_Add3d] (residual and embedding sum), [Mulc2d]. *)
Require Import Ionia.Ops_Elementwise.
(* [Softmax2d]. *)
Require Import Ionia.Ops_Reduce.
(* T1 operators: [LayerNorm3d], [Gather2d], [MatMul2d], [Transpose2d],
   [SplitHeads], [MergeHeads]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [attn_scale], [BMatMul2d]. *)
Require Import Ionia.Attention_DPIA.
(* T3: [GELU3d], [FFN] (feed-forward network, reused unchanged). *)
Require Import Ionia.MiniTransformer_DPIA.
(* [tanh1] (scalar tanh for the BERT pooler). *)
Require Import Ionia.Ops_RNN.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Bidirectional single-head attention cell (no causal mask)                   *)
(* -------------------------------------------------------------------------- *)

(* softmax(Q K^T / sqrt(d)) V on s x d matrices -- the causal-mask-free
   variant of Ionia.Attention_DPIA.Attention_cell. *)
Definition BAttention_cell {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  : exp (ary '{s} (ary '{d} num)) :=
  let scores := MatMul2d q (Transpose2d k) in
  let scaled := Mulc2d (attn_scale d) scores in
  let attn := Softmax2d scaled in
  MatMul2d attn v.

(* As in Attention_DPIA, the cell command is the final MatMul2d loop nest
   over the composed score expression; it writes only [output]. *)
Definition battention_cell_comm {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (output : acc (ary '{s} (ary '{d} num))) : comm :=
  MatMul2d_comm (Softmax2d (Mulc2d (attn_scale d)
                                   (MatMul2d q (Transpose2d k))))
                v output.

Lemma A_BAttention_cell : forall (s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (output : acc (ary '{s} (ary '{d} num))),
  A(output, BAttention_cell q k v) = battention_cell_comm q k v output.
Proof.
  intros. unfold BAttention_cell, battention_cell_comm. cbv zeta.
  apply A_MatMul2d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-head bidirectional attention over a (b, h, s, d) triple                 *)
(* -------------------------------------------------------------------------- *)

Definition BAttnHeads {b h s d : nat}
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    BAttention_cell (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                    (idx (idx vs bb) hh))).

Definition BAttnHeads_comm {b h s d : nat}
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    battention_cell_comm (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                         (idx (idx vs bb) hh) oh) ob) output.

Lemma A_BAttnHeads : forall (b h s d : nat)
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))),
  A(output, BAttnHeads qs ks vs) = BAttnHeads_comm qs ks vs output.
Proof.
  intros. unfold BAttnHeads, BAttnHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_BAttention_cell.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Bidirectional multi-head attention block (buffers bmq..bmmg)                *)
(* -------------------------------------------------------------------------- *)

Definition BMHABlock {b s h d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  let q := BMatMul2d input wq in
  let k := BMatMul2d input wk in
  let v := BMatMul2d input wv in
  let qs := SplitHeads q in
  let ks := SplitHeads k in
  let vs := SplitHeads v in
  let att := BAttnHeads qs ks vs in
  let merged := MergeHeads att in
  BMatMul2d merged wo.

Definition bmhablock_comm {b s h d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  new (fun tq => seq (BMatMul2d_comm input wq tq)
  (bind_read tq (fun eq =>
  new (fun tqs => seq (SplitHeads_comm eq tqs)
  (bind_read tqs (fun eqs =>
  new (fun tk => seq (BMatMul2d_comm input wk tk)
  (bind_read tk (fun ek =>
  new (fun tks => seq (SplitHeads_comm ek tks)
  (bind_read tks (fun eks =>
  new (fun tv => seq (BMatMul2d_comm input wv tv)
  (bind_read tv (fun ev =>
  new (fun tvs => seq (SplitHeads_comm ev tvs)
  (bind_read tvs (fun evs =>
  new (fun tatt => seq (BAttnHeads_comm eqs eks evs tatt)
  (bind_read tatt (fun eatt =>
  new (fun tmg => seq (MergeHeads_comm eatt tmg)
  (bind_read tmg (fun emg =>
    BMatMul2d_comm emg wo output)))
  (acc' (Var "bmmg")))))
  (acc' (Var "bmatt")))))
  (acc' (Var "bmvs")))))
  (acc' (Var "bmv")))))
  (acc' (Var "bmks")))))
  (acc' (Var "bmk")))))
  (acc' (Var "bmqs")))))
  (acc' (Var "bmq")).

Definition bmhablock_direct {b s h d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  let q := BMatMul2d input wq in
  let k := BMatMul2d input wk in
  let v := BMatMul2d input wv in
  let qs := SplitHeads q in
  let ks := SplitHeads k in
  let vs := SplitHeads v in
  let att := BAttnHeads qs ks vs in
  let merged := MergeHeads att in
  seq (A(acc' (Var "bmq"), q))
  (seq (A(acc' (Var "bmqs"), qs))
  (seq (A(acc' (Var "bmk"), k))
  (seq (A(acc' (Var "bmks"), ks))
  (seq (A(acc' (Var "bmv"), v))
  (seq (A(acc' (Var "bmvs"), vs))
  (seq (A(acc' (Var "bmatt"), att))
  (seq (A(acc' (Var "bmmg"), merged))
       (A(output, BMatMul2d merged wo))))))))).

Lemma bmhablock_comm_eq_direct : forall (b s h d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  bmhablock_comm input wq wk wv wo output =
  bmhablock_direct input wq wk wv wo output.
Proof.
  intros.
  unfold bmhablock_comm, bmhablock_direct, new.
  cbv zeta beta.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_BAttnHeads.
  rewrite bind_read_replace.
  rewrite <- A_MergeHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  reflexivity.
Qed.

Lemma A_BMHABlock : forall (b s h d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  bmhablock_comm input wq wk wv wo output rho p =
  A(output, BMHABlock input wq wk wv wo) rho p.
Proof.
  intros. rewrite bmhablock_comm_eq_direct.
  unfold bmhablock_direct, BMHABlock, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the MHA output buffer after the (folded) direct form yields the
   functional [BMHABlock] value (the [mhablock_direct_bind] pattern). *)
Lemma bmhablock_direct_bind : forall (b s h d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm),
  seq (bmhablock_direct input wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
  seq (bmhablock_direct input wq wk wv wo (acc' q))
      (k (BMHABlock input wq wk wv wo)).
Proof.
  intros. fun_ext.
  unfold bmhablock_direct, BMHABlock, seq, bind_read, A.
  cbv beta zeta.
  rewrite read_exp_assign. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Tanh2d (BERT pooler activation) and [CLS] pooling                           *)
(* -------------------------------------------------------------------------- *)

Definition Tanh2d {b m : nat}
  (input : exp (ary '{b} (ary '{m} num)))
  : exp (ary '{b} (ary '{m} num)) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun j : fin m =>
    tanh1 (idx (idx input bb) j))).

Definition Tanh2d_comm {b m : nat}
  (input : exp (ary '{b} (ary '{m} num)))
  (output : acc (ary '{b} (ary '{m} num))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun j oj =>
    oj |:= tanh1 (idx (idx input bb) j)) ob) output.

Lemma A_Tanh2d : forall (b m : nat)
  (input : exp (ary '{b} (ary '{m} num)))
  (output : acc (ary '{b} (ary '{m} num))),
  A(output, Tanh2d input) = Tanh2d_comm input output.
Proof.
  intros. unfold Tanh2d, Tanh2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* [CLS] pooling: select row [i0] (the [CLS] position, row 0 in BERT) of
   every batch element.  The row index is an explicit argument, so the
   operator needs no s > 0 hypothesis. *)
Definition CLSPool {b s dm : nat} (i0 : fin s)
  (input : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  : exp (ary '{b} (ary '{dm} num)) :=
  mkvSeq (fun bb : fin b => idx (idx input bb) i0).

Definition CLSPool_comm {b s dm : nat} (i0 : fin s)
  (input : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (output : acc (ary '{b} (ary '{dm} num))) : comm :=
  mkvSeql (fun bb ob => A(ob, idx (idx input bb) i0)) output.

Lemma A_CLSPool : forall (b s dm : nat) (i0 : fin s)
  (input : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (output : acc (ary '{b} (ary '{dm} num))),
  A(output, CLSPool i0 input) = CLSPool_comm i0 input output.
Proof.
  intros. unfold CLSPool, CLSPool_comm.
  rewrite AmkvSeq.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Post-norm BERT encoder block                                                *)
(*                                                                             *)
(*   r1 = LN1(x + MHA(x))   (bidirectional MHA on the RAW input, then          *)
(*   r2 = LN2(r1 + FFN(r1))  residual add, then LayerNorm)                     *)
(* -------------------------------------------------------------------------- *)

Definition BERTEncoderBlock {b s h d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  let r1 := LayerNorm3d (Add3d input (BMHABlock input wq wk wv wo))
                        ln1_g ln1_b eps in
  LayerNorm3d (Add3d r1 (FFN r1 w1 w2)) ln2_g ln2_b eps.

(* Imperative block: temporaries bemha, beadd1, ber1, bef1, beg, bef2,
   beadd2; the final LayerNorm writes [output] in place. *)
Definition bertblock_comm {b s h d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  new (fun t1 => seq (bmhablock_comm input wq wk wv wo t1)
  (bind_read t1 (fun e1 =>
  new (fun t2 => seq (Add3d_comm input e1 t2)
  (bind_read t2 (fun e2 =>
  new (fun t3 => seq (LayerNorm3d_comm e2 ln1_g ln1_b eps t3)
  (bind_read t3 (fun e3 =>
  new (fun t4 => seq (BMatMul2d_comm e3 w1 t4)
  (bind_read t4 (fun e4 =>
  new (fun t5 => seq (GELU3d_comm e4 t5)
  (bind_read t5 (fun e5 =>
  new (fun t6 => seq (BMatMul2d_comm e5 w2 t6)
  (bind_read t6 (fun e6 =>
  new (fun t7 => seq (Add3d_comm e3 e6 t7)
  (bind_read t7 (fun e7 =>
    LayerNorm3d_comm e7 ln2_g ln2_b eps output)))
  (acc' (Var "beadd2")))))
  (acc' (Var "bef2")))))
  (acc' (Var "beg")))))
  (acc' (Var "bef1")))))
  (acc' (Var "ber1")))))
  (acc' (Var "beadd1")))))
  (acc' (Var "bemha")).

(* Direct (DPIA-normal) form, left-associated so the final assignment is
   exposed at the top level; the MHA stage stays folded. *)
Definition bertblock_direct {b s h d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  let mha := BMHABlock input wq wk wv wo in
  let a1 := Add3d input mha in
  let r1 := LayerNorm3d a1 ln1_g ln1_b eps in
  let f1 := BMatMul2d r1 w1 in
  let gg := GELU3d f1 in
  let f2 := BMatMul2d gg w2 in
  let a2 := Add3d r1 f2 in
  seq (seq (seq (seq (seq (seq (seq
       (bmhablock_direct input wq wk wv wo (acc' (Var "bemha")))
       (A(acc' (Var "beadd1"), a1)))
       (A(acc' (Var "ber1"), r1)))
       (A(acc' (Var "bef1"), f1)))
       (A(acc' (Var "beg"), gg)))
       (A(acc' (Var "bef2"), f2)))
       (A(acc' (Var "beadd2"), a2)))
       (A(output, BERTEncoderBlock input ln1_g ln1_b ln2_g ln2_b
                                   wq wk wv wo w1 w2 eps)).

Lemma bertblock_comm_eq_direct : forall (b s h d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  bertblock_comm input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output =
  bertblock_direct input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output.
Proof.
  intros.
  unfold bertblock_comm, bertblock_direct, new.
  cbv zeta beta.
  rewrite bmhablock_comm_eq_direct.
  rewrite bmhablock_direct_bind.
  rewrite <- A_Add3d.
  rewrite bind_read_replace.
  rewrite <- A_LayerNorm3d.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_GELU3d.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_Add3d.
  rewrite bind_read_replace.
  rewrite <- A_LayerNorm3d.
  reflexivity.
Qed.

(* Block-level DPIA correctness (the [A_TransformerBlock] shape). *)
Lemma A_BERTEncoderBlock : forall (b s h d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  bertblock_comm input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output rho p =
  A(output, BERTEncoderBlock input ln1_g ln1_b ln2_g ln2_b
                            wq wk wv wo w1 w2 eps) rho p.
Proof.
  intros. rewrite bertblock_comm_eq_direct.
  unfold bertblock_direct, BERTEncoderBlock, FFN, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value (the [transformerblock_direct_read] pattern). *)
Lemma bertblock_direct_read : forall (b s h d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm) (c0 : comm),
  seq (bertblock_direct input ln1_g ln1_b ln2_g ln2_b
                        wq wk wv wo w1 w2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (bertblock_direct input ln1_g ln1_b ln2_g ln2_b
                        wq wk wv wo w1 w2 eps (acc' q))
      (seq (k (BERTEncoderBlock input ln1_g ln1_b ln2_g ln2_b
                                wq wk wv wo w1 w2 eps)) c0).
Proof.
  intros. unfold bertblock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* BERTMini: token+segment+position embedding -> 2 x encoder block ->          *)
(* [CLS] pool -> pooler (Linear -> tanh) -> output head                        *)
(* -------------------------------------------------------------------------- *)

Section BERTMiniNet.

  (* All sizes symbolic: batch b, sequence s, heads h, head dimension d
     (model dimension h*d), FFN width df, vocabulary v, segment vocabulary
     sg (2 in BERT), number of classes nc.  [Hs] witnesses that the [CLS]
     row exists. *)
  Context (b s h d df v sg nc : nat).
  Context (Hs : (s > 0)%nat).
  Context (eps : exp num).

  (* Token / segment index maps (host-level, cf. [Gather2d]) and the three
     embedding tables. *)
  Context (toks : fin s -> fin v) (segs : fin s -> fin sg).
  Context (tok_table : exp (ary '{v} (ary '{h * d} num)))
          (seg_table : exp (ary '{sg} (ary '{h * d} num)))
          (pos_table : exp (ary '{s} (ary '{h * d} num))).

  (* Layer-1 parameters. *)
  Context (l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b : exp (ary '{h * d} num))
          (l1_wq l1_wk l1_wv l1_wo : exp (ary '{h * d} (ary '{h * d} num)))
          (l1_w1 : exp (ary '{h * d} (ary '{df} num)))
          (l1_w2 : exp (ary '{df} (ary '{h * d} num))).

  (* Layer-2 parameters. *)
  Context (l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b : exp (ary '{h * d} num))
          (l2_wq l2_wk l2_wv l2_wo : exp (ary '{h * d} (ary '{h * d} num)))
          (l2_w1 : exp (ary '{h * d} (ary '{df} num)))
          (l2_w2 : exp (ary '{df} (ary '{h * d} num))).

  (* Pooler (BERT's tanh pooler on the [CLS] vector) and output head. *)
  Context (wpool : exp (ary '{h * d} (ary '{h * d} num)))
          (whead : exp (ary '{h * d} (ary '{nc} num))).

  (* The [CLS] row index. *)
  Definition cls0 : fin s := @nat2fin s 0 (ltac:(lia)).

  (* Batched embeddings: the same token/segment sequence and position table
     in every batch element (the batch=1 use case; the tables are arbitrary
     parameters). *)
  Definition TokEmbed : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => Gather2d toks tok_table).
  Definition SegEmbed : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => Gather2d segs seg_table).
  Definition PosEmbed : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => pos_table).

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  Definition bt_x0 := Add3d (Add3d TokEmbed SegEmbed) PosEmbed.
  Definition bt_x1 := BERTEncoderBlock bt_x0 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                                       l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps.
  Definition bt_x2 := BERTEncoderBlock bt_x1 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                                       l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps.
  Definition bt_x3 := CLSPool cls0 bt_x2.
  Definition bt_x4 := MatMul2d bt_x3 wpool.
  Definition bt_x5 := Tanh2d bt_x4.
  Definition bt_x6 := MatMul2d bt_x5 whead.

  Lemma bt_x0_body : bt_x0 = Add3d (Add3d TokEmbed SegEmbed) PosEmbed.
  Proof. reflexivity. Qed.
  Lemma bt_x1_body : bt_x1 = BERTEncoderBlock bt_x0 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                                       l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps.
  Proof. reflexivity. Qed.
  Lemma bt_x2_body : bt_x2 = BERTEncoderBlock bt_x1 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                                       l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps.
  Proof. reflexivity. Qed.
  Lemma bt_x3_body : bt_x3 = CLSPool cls0 bt_x2.
  Proof. reflexivity. Qed.
  Lemma bt_x4_body : bt_x4 = MatMul2d bt_x3 wpool.
  Proof. reflexivity. Qed.
  Lemma bt_x5_body : bt_x5 = Tanh2d bt_x4.
  Proof. reflexivity. Qed.
  Lemma bt_x6_body : bt_x6 = MatMul2d bt_x5 whead.
  Proof. reflexivity. Qed.

  Opaque bt_x0 bt_x1 bt_x2 bt_x3 bt_x4 bt_x5 bt_x6.

  Definition BERTMini : exp (ary '{b} (ary '{nc} num)) := bt_x6.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition bertmini_comm
    (output : acc (ary '{b} (ary '{nc} num))) : comm :=
new (fun t0 => seq (Add3d_comm TokEmbed SegEmbed t0)
(new (fun t1 => seq (bind_read t0 (fun e0 => Add3d_comm e0 PosEmbed t1))
(new (fun t2 => seq (bind_read t1 (fun e1 =>
      bertblock_comm e1 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                     l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 =>
      bertblock_comm e2 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                     l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => CLSPool_comm cls0 e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => MatMul2d_comm e4 wpool t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Tanh2d_comm e5 t6))
     (bind_read t6 (fun e6 => MatMul2d_comm e6 whead output))
) (acc' (Var "l6")))
) (acc' (Var "l5")))
) (acc' (Var "l4")))
) (acc' (Var "l3")))
) (acc' (Var "l2")))
) (acc' (Var "l1")))
) (acc' (Var "bt0")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition bertmini_direct
    (output : acc (ary '{b} (ary '{nc} num))) : comm :=
    seq (A(acc' (Var "bt0"), Add3d TokEmbed SegEmbed))
    (seq (A(acc' (Var "l1"), bt_x0))
    (seq (bertblock_direct bt_x0 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                           l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps
                           (acc' (Var "l2")))
    (seq (bertblock_direct bt_x1 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                           l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps
                           (acc' (Var "l3")))
    (seq (A(acc' (Var "l4"), bt_x3))
    (seq (A(acc' (Var "l5"), bt_x4))
    (seq (A(acc' (Var "l6"), bt_x5))
         (A(output, bt_x6)))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition bt0_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "bt0").
  Definition l1_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l1").
  Definition l2_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l2").
  Definition l3_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l3").
  Definition l4_acc : acc (ary '{b} (ary '{h * d} num))
    := acc' (Var "l4").
  Definition l5_acc : acc (ary '{b} (ary '{h * d} num))
    := acc' (Var "l5").
  Definition l6_acc : acc (ary '{b} (ary '{h * d} num))
    := acc' (Var "l6").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries bemha..beadd2 and the MHA temporaries bmq..bmmg are shared
     between the two layers and are required to be fresh at every type
     (the [minitransformer_fresh] pattern). *)
  Definition bertmini_fresh
    (output : acc (ary '{b} (ary '{nc} num))) (rho : env) : Prop :=
    StructUndefined bt0_acc rho /\
    StructUndefined l1_acc rho /\
    StructUndefined l2_acc rho /\
    StructUndefined l3_acc rho /\
    StructUndefined l4_acc rho /\
    StructUndefined l5_acc rho /\
    StructUndefined l6_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "bemha") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "beadd1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "ber1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bef1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "beg") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bef2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "beadd2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmq") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmqs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmk") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmks") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmv") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmvs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmatt") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmmg") : acc d0) rho) /\
    (forall p, in_acc p output -> ~ in_acc p bt0_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l4_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l5_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l6_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bemha") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "beadd1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "ber1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bef1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "beg") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bef2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "beadd2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmq") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmqs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmk") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmks") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmv") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmvs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmatt") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmmg") : acc d0)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma bertmini_comm_eq_direct :
    forall (output : acc (ary '{b} (ary '{nc} num))),
    bertmini_comm output = bertmini_direct output.
  Proof.
    intros.
    unfold bertmini_comm, bertmini_direct, new.
    cbv beta.
    rewrite <- A_Add3d.
    rewrite bind_read_replace_seq.
    rewrite <- A_Add3d.
    rewrite <- bt_x0_body.
    rewrite bind_read_replace_seq.
    rewrite bertblock_comm_eq_direct.
    rewrite bertblock_direct_read.
    rewrite <- bt_x1_body.
    rewrite bertblock_comm_eq_direct.
    rewrite bertblock_direct_read.
    rewrite <- bt_x2_body.
    rewrite <- A_CLSPool.
    rewrite <- bt_x3_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_MatMul2d.
    rewrite <- bt_x4_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Tanh2d.
    rewrite <- bt_x5_body.
    rewrite bind_read_replace.
    rewrite <- A_MatMul2d.
    rewrite <- bt_x6_body.
    reflexivity.
  Qed.

  Lemma A_BERTMini_direct :
    forall (output : acc (ary '{b} (ary '{nc} num)))
      (rho : env) (p : path),
    in_acc p output ->
    bertmini_fresh output rho ->
    bertmini_direct output rho p = A(output, BERTMini) rho p.
  Proof.
    intros.
    unfold bertmini_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold BERTMini. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of the mini BERT encoder: under freshness
     of the temporary buffers, the imperative network observed at an output
     path computes the functional [BERTMini]. *)
  Theorem A_BERTMini :
    forall (output : acc (ary '{b} (ary '{nc} num)))
      (rho : env) (p : path),
    in_acc p output ->
    bertmini_fresh output rho ->
    bertmini_comm output rho p = A(output, BERTMini) rho p.
  Proof.
    intros. rewrite bertmini_comm_eq_direct.
    apply A_BERTMini_direct; assumption.
  Qed.

End BERTMiniNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: b = 1, s = 8, h = 2, d = 16 (model dim 32), df = 32,   *)
(* vocab v = 8, segment vocab sg = 2, classes nc = 4                           *)
(* -------------------------------------------------------------------------- *)

Section Small_1_8_2_16.

  Context (eps8 : exp num)
          (toks8 : fin 8 -> fin 8) (segs8 : fin 8 -> fin 2)
          (tok_tab8 : exp (ary '{8} (ary '{32} num)))
          (seg_tab8 : exp (ary '{2} (ary '{32} num)))
          (pos_tab8 : exp (ary '{8} (ary '{32} num)))
          (g1_1 b1_1 g2_1 b2_1 : exp (ary '{32} num))
          (wq1 wk1 wv1 wo1 : exp (ary '{32} (ary '{32} num)))
          (w1_1 : exp (ary '{32} (ary '{32} num)))
          (w2_1 : exp (ary '{32} (ary '{32} num)))
          (g1_2 b1_2 g2_2 b2_2 : exp (ary '{32} num))
          (wq2 wk2 wv2 wo2 : exp (ary '{32} (ary '{32} num)))
          (w1_2 : exp (ary '{32} (ary '{32} num)))
          (w2_2 : exp (ary '{32} (ary '{32} num)))
          (wp8 : exp (ary '{32} (ary '{32} num)))
          (wh8 : exp (ary '{32} (ary '{4} num)))
          (out8 : acc (ary '{1} (ary '{4} num))).

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition BERTMini_1_8_2_16 : exp (ary '{1} (ary '{4} num)) :=
    @BERTMini 1 8 2 16 32 8 2 4 (ltac:(lia))
      eps8 toks8 segs8 tok_tab8 seg_tab8 pos_tab8
      g1_1 b1_1 g2_1 b2_1 wq1 wk1 wv1 wo1 w1_1 w2_1
      g1_2 b1_2 g2_2 b2_2 wq2 wk2 wv2 wo2 w1_2 w2_2
      wp8 wh8.

  Definition bertmini_comm_1_8_2_16 : comm :=
    @bertmini_comm 1 8 2 16 32 8 2 4 (ltac:(lia))
      eps8 toks8 segs8 tok_tab8 seg_tab8 pos_tab8
      g1_1 b1_1 g2_1 b2_1 wq1 wk1 wv1 wo1 w1_1 w2_1
      g1_2 b1_2 g2_2 b2_2 wq2 wk2 wv2 wo2 w1_2 w2_2
      wp8 wh8 out8.

End Small_1_8_2_16.

(* [vm_compute]/conversion spot checks of the computable (structural) parts
   of the pipeline. *)

Definition bi0_1 : fin 1 := @nat2fin 1 0 (ltac:(lia)).
Definition bi0_2 : fin 2 := @nat2fin 2 0 (ltac:(lia)).
Definition bi1_2 : fin 2 := @nat2fin 2 1 (ltac:(lia)).
Definition bi0_4 : fin 4 := @nat2fin 4 0 (ltac:(lia)).
Definition bi3_8 : fin 8 := @nat2fin 8 3 (ltac:(lia)).
Definition bi5_8 : fin 8 := @nat2fin 8 5 (ltac:(lia)).

(* row*10+col encoding of an 8x8 score matrix. *)
Definition BM8 : exp (ary '{8} (ary '{8} num)) :=
  mkvSeq (fun i : fin 8 => mkvSeq (fun j : fin 8 =>
    (INR ((fin2nat i * 10 + fin2nat j)%nat) : exp num))).

(* Bidirectional attention keeps above-diagonal scores: position (3,5),
   which the causal mask would map to [NEGINF], keeps the scaled score. *)
Example check_bidir_no_mask :
  idx (idx (Mulc2d (attn_scale 8) BM8) bi3_8) bi5_8 =
  mul (INR 35) (attn_scale 8).
Proof. reflexivity. Qed.

(* Segment embedding lookup: a 2x2 segment table, entry (i, j) = 10*i + j;
   the segment map sends position 0 to segment 1. *)
Definition BS22 : exp (ary '{2} (ary '{2} num)) :=
  mkvSeq (fun i : fin 2 => mkvSeq (fun j : fin 2 =>
    (INR (fin2nat i * 10 + fin2nat j)%nat : exp num))).

Definition segs01 : fin 2 -> fin 2 :=
  fun i => if (fin2nat i =? 0)%nat then bi1_2 else bi0_2.

Example check_seg_embed :
  idx (idx (Gather2d segs01 BS22) bi0_2) bi1_2 = INR 11.
Proof. vm_compute. reflexivity. Qed.

(* [CLS] pooling selects row 0: entry (ss, j) = 10*ss + j, pooled entry
   j = 1 is 1. *)
Definition X142 : exp (ary '{1} (ary '{4} (ary '{2} num))) :=
  mkvSeq (fun bb : fin 1 => mkvSeq (fun ss : fin 4 => mkvSeq (fun j : fin 2 =>
    (INR (fin2nat ss * 10 + fin2nat j)%nat : exp num)))).

Example check_cls_pool :
  idx (idx (CLSPool bi0_4 X142) bi0_1) bi1_2 = INR 1.
Proof. vm_compute. reflexivity. Qed.

(* Post-norm block structure: LN after each residual add (contrast with
   MiniTransformer's pre-norm x + MHA(LN(x))). *)
Example check_postnorm_structure :
  forall (x : exp (ary '{1} (ary '{2} (ary '{2} num))))
    (g1 b1 g2 b2 : exp (ary '{2} num))
    (wq wk wv wo : exp (ary '{2} (ary '{2} num)))
    (w1 w2 : exp (ary '{2} (ary '{2} num)))
    (eps : exp num),
  BERTEncoderBlock (b:=1) (s:=2) (h:=1) (d:=2) (df:=2)
                   x g1 b1 g2 b2 wq wk wv wo w1 w2 eps =
  LayerNorm3d (Add3d (LayerNorm3d (Add3d x (BMHABlock (b:=1) (s:=2) (h:=1) (d:=2)
                                                    x wq wk wv wo)) g1 b1 eps)
                     (FFN (LayerNorm3d (Add3d x (BMHABlock (b:=1) (s:=2) (h:=1) (d:=2)
                                                           x wq wk wv wo)) g1 b1 eps)
                          w1 w2))
              g2 b2 eps.
Proof. reflexivity. Qed.

(* Tanh2d entry structure. *)
Example check_tanh2d_entry :
  forall (x : exp (ary '{2} (ary '{2} num))),
  idx (idx (Tanh2d x) bi0_2) bi1_2 = tanh1 (idx (idx x bi0_2) bi1_2).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_BAttention_cell.
Print Assumptions A_BAttnHeads.
Print Assumptions bmhablock_comm_eq_direct.
Print Assumptions A_BMHABlock.
Print Assumptions A_Tanh2d.
Print Assumptions A_CLSPool.
Print Assumptions bertblock_comm_eq_direct.
Print Assumptions A_BERTEncoderBlock.
Print Assumptions bertmini_comm_eq_direct.
Print Assumptions A_BERTMini.
