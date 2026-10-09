(* DPIA-style Leibniz equivalence proofs for a T5-style encoder-decoder
   network (milestone N2c of the NLP/LLM extension, cf.
   doc/NLP与LLM扩展开发规划_20260911.md §2-N2) in the route-A R-based
   expression model.

   Delivered here (all closed with [Qed], no Admitted/Axiom):

   - [RelPosBiasHeads]: T5 relative position bias — a per-head bias table
     lookup [bias hh i j = table hh (bucket i j)], where [bucket] is a pure
     fin/fin host-level index map (the [Gather] pattern of
     Ionia.Ops_Transformer; T5 uses no absolute positional encoding, the
     bias added to the attention scores is the only position signal).

   - The three attention cells of the T5 architecture, all direct
     generalisations of [Attention_cell] (Ionia.Attention_DPIA):
       [EncAttention_cell]: self-attention, no mask, scores + bias;
       [DecAttention_cell]: self-attention, causal mask, scores + bias;
       [CrossAttention_cell]: encoder-decoder attention — Q from the
         decoder state (length sq), K/V from the encoder output (length
         sk), no mask, no bias (as in T5).  This is the only genuinely new
         block shape of N2: two separate input sets.
     Each cell command is the final [MatMul2d] loop nest over the composed
     score expression, so the cell rules are plain command equalities (the
     T1/T2 operator style).

   - [T5MHABlock]: a generic multi-head attention block (Section [T5MHA])
     parameterised by the per-head computation and its A-rule, with TWO
     sources: the query input (b, sq, h*d) and the key/value source
     (b, sk, h*d).  Self-attention instantiates kvsrc := input;
     cross-attention takes the encoder output as kvsrc.  The block proof
     machinery (comm/direct collapse, direct-bind, block A-rule) is proved
     once against the hypothesis [A_heads] and instantiated three times
     ([EncMHABlock] / [DecMHABlock] / [CrossMHABlock]).

   - [T5EncoderBlock]: pre-norm encoder block
       r1 = x + EncMHA(LN1(x));  out = r1 + FFN(LN2(r1)).
   - [T5DecoderBlock]: pre-norm decoder block
       r1 = x + DecMHA(LN1(x));
       r2 = r1 + CrossMHA(LN2(r1), enc);
       out = r2 + FFN(LN3(r2)).

   - [T5Mini]: end-to-end network, all sizes symbolic (batch b, source
     length se, target length sd, heads h, head dim d, FFN width df,
     vocab v, bias buckets nb):
       encoder: token embedding (Gather2d, NO positional table — the
                relative bias carries the position signal)
                -> T5EncoderBlock x 2 -> final LayerNorm;
       decoder: token embedding -> T5DecoderBlock x 2 (cross-attention
                reads the final encoder output) -> final LayerNorm
                -> output head Linear (logits over vocab).
     Layer values are folded into [Opaque] constants (the ResNet50 /
     MiniTransformer wrapper pattern).  [A_T5Mini] is the end-to-end
     theorem: under freshness of the temporary buffers, the imperative
     network observed at an output path equals the functional network.

   - A concrete instantiation at b = 1, se = 8, sd = 4, h = 2, d = 16
     (model dimension 32), df = 32, v = 8, nb = 8, with [vm_compute]/
     conversion spot checks of the computable parts (bias table lookup,
     decoder mask structure, cross-attention shapes). *)

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
(* [Add2d] / [Add3d] / [Mulc2d]. *)
Require Import Ionia.Ops_Elementwise.
(* [Softmax2d]. *)
Require Import Ionia.Ops_Reduce.
(* T1 operators: [MatMul2d], [Transpose2d], [CausalMask2d], [Gather2d],
   [LayerNorm3d]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [attn_scale], [BMatMul2d]. *)
Require Import Ionia.Attention_DPIA.
(* T3: [FFN], [GELU3d]. *)
Require Import Ionia.MiniTransformer_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Relative position bias (per-head table lookup)                              *)
(* -------------------------------------------------------------------------- *)

(* bias hh i j = table hh (bucket i j): the [Gather] pattern with a two-index
   host-level bucket map. *)
Definition RelPosBiasHeads {h s nb : nat}
  (bucket : fin s -> fin s -> fin nb)
  (table : exp (ary '{h} (ary '{nb} num)))
  : exp (ary '{h} (ary '{s} (ary '{s} num))) :=
  mkvSeq (fun hh : fin h => mkvSeq (fun i : fin s => mkvSeq (fun j : fin s =>
    idx (idx table hh) (bucket i j)))).

Definition RelPosBiasHeads_comm {h s nb : nat}
  (bucket : fin s -> fin s -> fin nb)
  (table : exp (ary '{h} (ary '{nb} num)))
  (output : acc (ary '{h} (ary '{s} (ary '{s} num)))) : comm :=
  mkvSeql (fun hh oh => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    oj |:= idx (idx table hh) (bucket i j)) oi) oh) output.

Lemma A_RelPosBiasHeads : forall (h s nb : nat)
  (bucket : fin s -> fin s -> fin nb)
  (table : exp (ary '{h} (ary '{nb} num)))
  (output : acc (ary '{h} (ary '{s} (ary '{s} num)))),
  A(output, RelPosBiasHeads bucket table) = RelPosBiasHeads_comm bucket table output.
Proof.
  intros. unfold RelPosBiasHeads, RelPosBiasHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The three T5 attention cells                                                *)
(* -------------------------------------------------------------------------- *)

(* Encoder self-attention cell: softmax(Q K^T / sqrt(d) + bias) V, no mask. *)
Definition EncAttention_cell {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (bias : exp (ary '{s} (ary '{s} num)))
  : exp (ary '{s} (ary '{d} num)) :=
  let scores := MatMul2d q (Transpose2d k) in
  let scaled := Mulc2d (attn_scale d) scores in
  let biased := Add2d scaled bias in
  let attn := Softmax2d biased in
  MatMul2d attn v.

Definition enc_attention_cell_comm {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (bias : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{d} num))) : comm :=
  MatMul2d_comm (Softmax2d (Add2d (Mulc2d (attn_scale d)
                                         (MatMul2d q (Transpose2d k)))
                                  bias))
                v output.

Lemma A_EncAttention_cell : forall (s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (bias : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{d} num))),
  A(output, EncAttention_cell q k v bias) = enc_attention_cell_comm q k v bias output.
Proof.
  intros. unfold EncAttention_cell, enc_attention_cell_comm. cbv zeta.
  apply A_MatMul2d.
Qed.

(* Decoder self-attention cell: causal mask applied to the biased scores. *)
Definition DecAttention_cell {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (bias : exp (ary '{s} (ary '{s} num)))
  : exp (ary '{s} (ary '{d} num)) :=
  let scores := MatMul2d q (Transpose2d k) in
  let scaled := Mulc2d (attn_scale d) scores in
  let masked := CausalMask2d (Add2d scaled bias) in
  let attn := Softmax2d masked in
  MatMul2d attn v.

Definition dec_attention_cell_comm {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (bias : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{d} num))) : comm :=
  MatMul2d_comm (Softmax2d (CausalMask2d (Add2d (Mulc2d (attn_scale d)
                                                       (MatMul2d q (Transpose2d k)))
                                                bias)))
                v output.

Lemma A_DecAttention_cell : forall (s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (bias : exp (ary '{s} (ary '{s} num)))
  (output : acc (ary '{s} (ary '{d} num))),
  A(output, DecAttention_cell q k v bias) = dec_attention_cell_comm q k v bias output.
Proof.
  intros. unfold DecAttention_cell, dec_attention_cell_comm. cbv zeta.
  apply A_MatMul2d.
Qed.

(* Cross-attention cell: Q (sq x d) from the decoder state, K/V (sk x d)
   from the encoder output; no mask, no bias (as in T5). *)
Definition CrossAttention_cell {sq sk d : nat}
  (q : exp (ary '{sq} (ary '{d} num)))
  (k v : exp (ary '{sk} (ary '{d} num)))
  : exp (ary '{sq} (ary '{d} num)) :=
  let scores := MatMul2d q (Transpose2d k) in
  let scaled := Mulc2d (attn_scale d) scores in
  let attn := Softmax2d scaled in
  MatMul2d attn v.

Definition cross_attention_cell_comm {sq sk d : nat}
  (q : exp (ary '{sq} (ary '{d} num)))
  (k v : exp (ary '{sk} (ary '{d} num)))
  (output : acc (ary '{sq} (ary '{d} num))) : comm :=
  MatMul2d_comm (Softmax2d (Mulc2d (attn_scale d)
                                  (MatMul2d q (Transpose2d k))))
                v output.

Lemma A_CrossAttention_cell : forall (sq sk d : nat)
  (q : exp (ary '{sq} (ary '{d} num)))
  (k v : exp (ary '{sk} (ary '{d} num)))
  (output : acc (ary '{sq} (ary '{d} num))),
  A(output, CrossAttention_cell q k v) = cross_attention_cell_comm q k v output.
Proof.
  intros. unfold CrossAttention_cell, cross_attention_cell_comm. cbv zeta.
  apply A_MatMul2d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-head attention over (b, h, s, d) triples                                *)
(* -------------------------------------------------------------------------- *)

Definition EncAttnHeads {b h s d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    EncAttention_cell (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                      (idx (idx vs bb) hh) (idx bias hh))).

Definition EncAttnHeads_comm {b h s d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    enc_attention_cell_comm (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                            (idx (idx vs bb) hh) (idx bias hh) oh) ob) output.

Lemma A_EncAttnHeads : forall (b h s d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))),
  A(output, EncAttnHeads bias qs ks vs) = EncAttnHeads_comm bias qs ks vs output.
Proof.
  intros. unfold EncAttnHeads, EncAttnHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_EncAttention_cell.
  reflexivity.
Qed.

Definition DecAttnHeads {b h s d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    DecAttention_cell (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                      (idx (idx vs bb) hh) (idx bias hh))).

Definition DecAttnHeads_comm {b h s d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    dec_attention_cell_comm (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                            (idx (idx vs bb) hh) (idx bias hh) oh) ob) output.

Lemma A_DecAttnHeads : forall (b h s d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))),
  A(output, DecAttnHeads bias qs ks vs) = DecAttnHeads_comm bias qs ks vs output.
Proof.
  intros. unfold DecAttnHeads, DecAttnHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_DecAttention_cell.
  reflexivity.
Qed.

(* Cross-attention heads: queries of length sq, keys/values of length sk. *)
Definition CrossAttnHeads {b h sq sk d : nat}
  (qs : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num)))))
  (ks vs : exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num)))))
  : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    CrossAttention_cell (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                        (idx (idx vs bb) hh))).

Definition CrossAttnHeads_comm {b h sq sk d : nat}
  (qs : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num)))))
  (ks vs : exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    cross_attention_cell_comm (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                              (idx (idx vs bb) hh) oh) ob) output.

Lemma A_CrossAttnHeads : forall (b h sq sk d : nat)
  (qs : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num)))))
  (ks vs : exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))),
  A(output, CrossAttnHeads qs ks vs) = CrossAttnHeads_comm qs ks vs output.
Proof.
  intros. unfold CrossAttnHeads, CrossAttnHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_CrossAttention_cell.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic two-source multi-head attention block                               *)
(*                                                                             *)
(* Parameterised by the per-head computation [heads] and its A-rule; the      *)
(* block proof is done once and instantiated for encoder self-attention,      *)
(* decoder self-attention and cross-attention.                                 *)
(* -------------------------------------------------------------------------- *)

Section T5MHA.

  Context (b sq sk h d : nat).

  Context (heads : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))
                -> exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num))))
                -> exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num))))
                -> exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))).
  Context (heads_comm : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))
                -> exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num))))
                -> exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num))))
                -> acc (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))
                -> comm).
  Context (A_heads : forall
    (qs : exp (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num)))))
    (ks vs : exp (ary '{b} (ary '{h} (ary '{sk} (ary '{d} num)))))
    (output : acc (ary '{b} (ary '{h} (ary '{sq} (ary '{d} num))))),
    A(output, heads qs ks vs) = heads_comm qs ks vs output).

  (* Functional block: q from [input], k/v from [kvsrc]; head split,
     per-head attention, head merge, output projection. *)
  Definition T5MHABlock
    (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
    (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
    : exp (ary '{b} (ary '{sq} (ary '{h * d} num))) :=
    let q := BMatMul2d input wq in
    let k := BMatMul2d kvsrc wk in
    let v := BMatMul2d kvsrc wv in
    let qs := SplitHeads q in
    let ks := SplitHeads k in
    let vs := SplitHeads v in
    let att := heads qs ks vs in
    let merged := MergeHeads att in
    BMatMul2d merged wo.

  (* Imperative block: temporaries 5tq..5tmg (the [mhablock_comm] staging
     pattern of Ionia.Attention_DPIA). *)
  Definition t5mhablock_comm
    (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
    (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
    (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num)))) : comm :=
    new (fun tq => seq (BMatMul2d_comm input wq tq)
    (bind_read tq (fun eq =>
    new (fun tqs => seq (SplitHeads_comm eq tqs)
    (bind_read tqs (fun eqs =>
    new (fun tk => seq (BMatMul2d_comm kvsrc wk tk)
    (bind_read tk (fun ek =>
    new (fun tks => seq (SplitHeads_comm ek tks)
    (bind_read tks (fun eks =>
    new (fun tv => seq (BMatMul2d_comm kvsrc wv tv)
    (bind_read tv (fun ev =>
    new (fun tvs => seq (SplitHeads_comm ev tvs)
    (bind_read tvs (fun evs =>
    new (fun tatt => seq (heads_comm eqs eks evs tatt)
    (bind_read tatt (fun eatt =>
    new (fun tmg => seq (MergeHeads_comm eatt tmg)
    (bind_read tmg (fun emg =>
      BMatMul2d_comm emg wo output)))
    (acc' (Var "5tmg")))))
    (acc' (Var "5tatt")))))
    (acc' (Var "5tvs")))))
    (acc' (Var "5tv")))))
    (acc' (Var "5tks")))))
    (acc' (Var "5tk")))))
    (acc' (Var "5tqs")))))
    (acc' (Var "5tq")).

  (* Direct (DPIA-normal) form of the block. *)
  Definition t5mhablock_direct
    (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
    (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
    (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num)))) : comm :=
    let q := BMatMul2d input wq in
    let k := BMatMul2d kvsrc wk in
    let v := BMatMul2d kvsrc wv in
    let qs := SplitHeads q in
    let ks := SplitHeads k in
    let vs := SplitHeads v in
    let att := heads qs ks vs in
    let merged := MergeHeads att in
    seq (A(acc' (Var "5tq"), q))
    (seq (A(acc' (Var "5tqs"), qs))
    (seq (A(acc' (Var "5tk"), k))
    (seq (A(acc' (Var "5tks"), ks))
    (seq (A(acc' (Var "5tv"), v))
    (seq (A(acc' (Var "5tvs"), vs))
    (seq (A(acc' (Var "5tatt"), att))
    (seq (A(acc' (Var "5tmg"), merged))
         (A(output, BMatMul2d merged wo))))))))).

  Lemma t5mhablock_comm_eq_direct : forall
    (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
    (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
    (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num)))),
    t5mhablock_comm input kvsrc wq wk wv wo output =
    t5mhablock_direct input kvsrc wq wk wv wo output.
  Proof.
    intros.
    unfold t5mhablock_comm, t5mhablock_direct, new.
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
    rewrite <- A_heads.
    rewrite bind_read_replace.
    rewrite <- A_MergeHeads.
    rewrite bind_read_replace.
    rewrite <- A_BMatMul2d.
    reflexivity.
  Qed.

  (* Reading the block output buffer after the (folded) direct form yields
     the functional [T5MHABlock] value. *)
  Lemma t5mhablock_direct_bind : forall
    (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
    (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
    (q : path)
    (k : exp (ary '{b} (ary '{sq} (ary '{h * d} num))) -> comm),
    seq (t5mhablock_direct input kvsrc wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
    seq (t5mhablock_direct input kvsrc wq wk wv wo (acc' q))
        (k (T5MHABlock input kvsrc wq wk wv wo)).
  Proof.
    intros. fun_ext.
    unfold t5mhablock_direct, T5MHABlock, seq, bind_read, A.
    cbv beta zeta.
    rewrite read_exp_assign. reflexivity.
  Qed.

  (* Block-level DPIA correctness (the [A_MHABlock] shape). *)
  Lemma A_T5MHABlock : forall
    (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
    (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
    (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num))))
    (rho : env) (p : path),
    in_acc p output ->
    t5mhablock_comm input kvsrc wq wk wv wo output rho p =
    A(output, T5MHABlock input kvsrc wq wk wv wo) rho p.
  Proof.
    intros. rewrite t5mhablock_comm_eq_direct.
    unfold t5mhablock_direct, T5MHABlock, A. cbv zeta beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - reflexivity.
  Qed.

End T5MHA.

(* -------------------------------------------------------------------------- *)
(* The three block instantiations                                              *)
(* -------------------------------------------------------------------------- *)

(* Encoder self-attention block: kvsrc := input. *)
Definition EncMHABlock {b s h d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  @T5MHABlock b s s h d (EncAttnHeads bias) input input wq wk wv wo.

Definition encmhablock_comm {b s h d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  @t5mhablock_comm b s s h d (EncAttnHeads_comm bias)
                  input input wq wk wv wo output.

Definition encmhablock_direct {b s h d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  @t5mhablock_direct b s s h d (EncAttnHeads bias) input input wq wk wv wo output.

Lemma encmha_comm_eq_direct : forall (b s h d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  encmhablock_comm bias input wq wk wv wo output =
  encmhablock_direct bias input wq wk wv wo output.
Proof.
  intros. unfold encmhablock_comm, encmhablock_direct.
  apply t5mhablock_comm_eq_direct.
  intros. apply A_EncAttnHeads.
Qed.

Lemma encmha_direct_bind : forall (b s h d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm),
  seq (encmhablock_direct bias input wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
  seq (encmhablock_direct bias input wq wk wv wo (acc' q))
      (k (EncMHABlock bias input wq wk wv wo)).
Proof.
  intros. unfold encmhablock_direct, EncMHABlock.
  apply t5mhablock_direct_bind.
Qed.

Lemma A_EncMHABlock : forall (b s h d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  encmhablock_comm bias input wq wk wv wo output rho p =
  A(output, EncMHABlock bias input wq wk wv wo) rho p.
Proof.
  intros. unfold encmhablock_comm, EncMHABlock.
  apply A_T5MHABlock; try assumption.
  intros. apply A_EncAttnHeads.
Qed.

(* Decoder self-attention block: kvsrc := input. *)
Definition DecMHABlock {b s h d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  @T5MHABlock b s s h d (DecAttnHeads bias) input input wq wk wv wo.

Definition decmhablock_comm {b s h d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  @t5mhablock_comm b s s h d (DecAttnHeads_comm bias)
                  input input wq wk wv wo output.

Definition decmhablock_direct {b s h d : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  @t5mhablock_direct b s s h d (DecAttnHeads bias) input input wq wk wv wo output.

Lemma decmha_comm_eq_direct : forall (b s h d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  decmhablock_comm bias input wq wk wv wo output =
  decmhablock_direct bias input wq wk wv wo output.
Proof.
  intros. unfold decmhablock_comm, decmhablock_direct.
  apply t5mhablock_comm_eq_direct.
  intros. apply A_DecAttnHeads.
Qed.

Lemma decmha_direct_bind : forall (b s h d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm),
  seq (decmhablock_direct bias input wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
  seq (decmhablock_direct bias input wq wk wv wo (acc' q))
      (k (DecMHABlock bias input wq wk wv wo)).
Proof.
  intros. unfold decmhablock_direct, DecMHABlock.
  apply t5mhablock_direct_bind.
Qed.

Lemma A_DecMHABlock : forall (b s h d : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  decmhablock_comm bias input wq wk wv wo output rho p =
  A(output, DecMHABlock bias input wq wk wv wo) rho p.
Proof.
  intros. unfold decmhablock_comm, DecMHABlock.
  apply A_T5MHABlock; try assumption.
  intros. apply A_DecAttnHeads.
Qed.

(* Cross-attention block: queries from [input] (decoder state, length sq),
   keys/values from [kvsrc] (encoder output, length sk). *)
Definition CrossMHABlock {b sq sk h d : nat}
  (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  : exp (ary '{b} (ary '{sq} (ary '{h * d} num))) :=
  @T5MHABlock b sq sk h d CrossAttnHeads input kvsrc wq wk wv wo.

Definition crossmhablock_comm {b sq sk h d : nat}
  (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num)))) : comm :=
  @t5mhablock_comm b sq sk h d CrossAttnHeads_comm
                  input kvsrc wq wk wv wo output.

Definition crossmhablock_direct {b sq sk h d : nat}
  (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num)))) : comm :=
  @t5mhablock_direct b sq sk h d CrossAttnHeads input kvsrc wq wk wv wo output.

Lemma crossmha_comm_eq_direct : forall (b sq sk h d : nat)
  (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num)))),
  crossmhablock_comm input kvsrc wq wk wv wo output =
  crossmhablock_direct input kvsrc wq wk wv wo output.
Proof.
  intros. unfold crossmhablock_comm, crossmhablock_direct.
  apply t5mhablock_comm_eq_direct.
  intros. apply A_CrossAttnHeads.
Qed.

Lemma crossmha_direct_bind : forall (b sq sk h d : nat)
  (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{sq} (ary '{h * d} num))) -> comm),
  seq (crossmhablock_direct input kvsrc wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
  seq (crossmhablock_direct input kvsrc wq wk wv wo (acc' q))
      (k (CrossMHABlock input kvsrc wq wk wv wo)).
Proof.
  intros. unfold crossmhablock_direct, CrossMHABlock.
  apply t5mhablock_direct_bind.
Qed.

Lemma A_CrossMHABlock : forall (b sq sk h d : nat)
  (input : exp (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (kvsrc : exp (ary '{b} (ary '{sk} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{sq} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  crossmhablock_comm input kvsrc wq wk wv wo output rho p =
  A(output, CrossMHABlock input kvsrc wq wk wv wo) rho p.
Proof.
  intros. unfold crossmhablock_comm, CrossMHABlock.
  apply A_T5MHABlock; try assumption.
  intros. apply A_CrossAttnHeads.
Qed.

(* -------------------------------------------------------------------------- *)
(* T5 encoder block (pre-norm: self-attention + FFN)                           *)
(* -------------------------------------------------------------------------- *)

Definition T5EncoderBlock {b s h d df : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  let r1 := Add3d input (EncMHABlock bias (LayerNorm3d input ln1_g ln1_b eps)
                                     wq wk wv wo) in
  Add3d r1 (FFN (LayerNorm3d r1 ln2_g ln2_b eps) w1 w2).

(* Imperative block: temporaries 5bln1, 5bmha, 5br1, 5bln2, 5bf1, 5bg, 5bf2
   (the [transformerblock_comm] staging pattern). *)
Definition t5encblock_comm {b s h d df : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  new (fun t1 => seq (LayerNorm3d_comm input ln1_g ln1_b eps t1)
  (bind_read t1 (fun e1 =>
  new (fun t2 => seq (encmhablock_comm bias e1 wq wk wv wo t2)
  (bind_read t2 (fun e2 =>
  new (fun t3 => seq (Add3d_comm input e2 t3)
  (bind_read t3 (fun e3 =>
  new (fun t4 => seq (LayerNorm3d_comm e3 ln2_g ln2_b eps t4)
  (bind_read t4 (fun e4 =>
  new (fun t5 => seq (BMatMul2d_comm e4 w1 t5)
  (bind_read t5 (fun e5 =>
  new (fun t6 => seq (GELU3d_comm e5 t6)
  (bind_read t6 (fun e6 =>
  new (fun t7 => seq (BMatMul2d_comm e6 w2 t7)
  (bind_read t7 (fun e7 =>
    Add3d_comm e3 e7 output)))
  (acc' (Var "5bf2")))))
  (acc' (Var "5bg")))))
  (acc' (Var "5bf1")))))
  (acc' (Var "5bln2")))))
  (acc' (Var "5br1")))))
  (acc' (Var "5bmha")))))
  (acc' (Var "5bln1")).

Definition t5encblock_direct {b s h d df : nat}
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  let ln1 := LayerNorm3d input ln1_g ln1_b eps in
  let mha := EncMHABlock bias ln1 wq wk wv wo in
  let r1 := Add3d input mha in
  let ln2 := LayerNorm3d r1 ln2_g ln2_b eps in
  let f1 := BMatMul2d ln2 w1 in
  let gg := GELU3d f1 in
  let f2 := BMatMul2d gg w2 in
  seq (seq (seq (seq (seq (seq (seq
       (A(acc' (Var "5bln1"), ln1))
       (encmhablock_direct bias ln1 wq wk wv wo (acc' (Var "5bmha"))))
       (A(acc' (Var "5br1"), r1)))
       (A(acc' (Var "5bln2"), ln2)))
       (A(acc' (Var "5bf1"), f1)))
       (A(acc' (Var "5bg"), gg)))
       (A(acc' (Var "5bf2"), f2)))
       (A(output, T5EncoderBlock bias input ln1_g ln1_b ln2_g ln2_b
                                 wq wk wv wo w1 w2 eps)).

Lemma t5encblock_comm_eq_direct : forall (b s h d df : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  t5encblock_comm bias input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output =
  t5encblock_direct bias input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output.
Proof.
  intros.
  unfold t5encblock_comm, t5encblock_direct, new.
  cbv zeta beta.
  rewrite <- A_LayerNorm3d.
  rewrite bind_read_replace.
  rewrite encmha_comm_eq_direct.
  rewrite encmha_direct_bind.
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
  reflexivity.
Qed.

Lemma A_T5EncoderBlock : forall (b s h d df : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  t5encblock_comm bias input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output rho p =
  A(output, T5EncoderBlock bias input ln1_g ln1_b ln2_g ln2_b
                          wq wk wv wo w1 w2 eps) rho p.
Proof.
  intros. rewrite t5encblock_comm_eq_direct.
  unfold t5encblock_direct, T5EncoderBlock, FFN, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

Lemma t5encblock_direct_read : forall (b s h d df : nat)
  (bias : exp (ary '{h} (ary '{s} (ary '{s} num))))
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm) (c0 : comm),
  seq (t5encblock_direct bias input ln1_g ln1_b ln2_g ln2_b
                         wq wk wv wo w1 w2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (t5encblock_direct bias input ln1_g ln1_b ln2_g ln2_b
                         wq wk wv wo w1 w2 eps (acc' q))
      (seq (k (T5EncoderBlock bias input ln1_g ln1_b ln2_g ln2_b
                              wq wk wv wo w1 w2 eps)) c0).
Proof.
  intros. unfold t5encblock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* T5 decoder block (pre-norm: self-attention + cross-attention + FFN)         *)
(* -------------------------------------------------------------------------- *)

Definition T5DecoderBlock {b sd se h d df : nat}
  (bias : exp (ary '{h} (ary '{sd} (ary '{sd} num))))
  (input : exp (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (enc : exp (ary '{b} (ary '{se} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b : exp (ary '{h * d} num))
  (wqS wkS wvS woS : exp (ary '{h * d} (ary '{h * d} num)))
  (wqC wkC wvC woC : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  : exp (ary '{b} (ary '{sd} (ary '{h * d} num))) :=
  let r1 := Add3d input (DecMHABlock bias (LayerNorm3d input ln1_g ln1_b eps)
                                     wqS wkS wvS woS) in
  let r2 := Add3d r1 (CrossMHABlock (LayerNorm3d r1 ln2_g ln2_b eps) enc
                                    wqC wkC wvC woC) in
  Add3d r2 (FFN (LayerNorm3d r2 ln3_g ln3_b eps) w1 w2).

(* Imperative block: temporaries 5dln1, 5dself, 5dr1, 5dln2, 5dcro, 5dr2,
   5dln3, 5df1, 5dg, 5df2. *)
Definition t5decblock_comm {b sd se h d df : nat}
  (bias : exp (ary '{h} (ary '{sd} (ary '{sd} num))))
  (input : exp (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (enc : exp (ary '{b} (ary '{se} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b : exp (ary '{h * d} num))
  (wqS wkS wvS woS : exp (ary '{h * d} (ary '{h * d} num)))
  (wqC wkC wvC woC : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{sd} (ary '{h * d} num)))) : comm :=
  new (fun t1 => seq (LayerNorm3d_comm input ln1_g ln1_b eps t1)
  (bind_read t1 (fun e1 =>
  new (fun t2 => seq (decmhablock_comm bias e1 wqS wkS wvS woS t2)
  (bind_read t2 (fun e2 =>
  new (fun t3 => seq (Add3d_comm input e2 t3)
  (bind_read t3 (fun e3 =>
  new (fun t4 => seq (LayerNorm3d_comm e3 ln2_g ln2_b eps t4)
  (bind_read t4 (fun e4 =>
  new (fun t5 => seq (crossmhablock_comm e4 enc wqC wkC wvC woC t5)
  (bind_read t5 (fun e5 =>
  new (fun t6 => seq (Add3d_comm e3 e5 t6)
  (bind_read t6 (fun e6 =>
  new (fun t7 => seq (LayerNorm3d_comm e6 ln3_g ln3_b eps t7)
  (bind_read t7 (fun e7 =>
  new (fun t8 => seq (BMatMul2d_comm e7 w1 t8)
  (bind_read t8 (fun e8 =>
  new (fun t9 => seq (GELU3d_comm e8 t9)
  (bind_read t9 (fun e9 =>
  new (fun t10 => seq (BMatMul2d_comm e9 w2 t10)
  (bind_read t10 (fun e10 =>
    Add3d_comm e6 e10 output)))
  (acc' (Var "5df2")))))
  (acc' (Var "5dg")))))
  (acc' (Var "5df1")))))
  (acc' (Var "5dln3")))))
  (acc' (Var "5dr2")))))
  (acc' (Var "5dcro")))))
  (acc' (Var "5dln2")))))
  (acc' (Var "5dr1")))))
  (acc' (Var "5dself")))))
  (acc' (Var "5dln1")).

Definition t5decblock_direct {b sd se h d df : nat}
  (bias : exp (ary '{h} (ary '{sd} (ary '{sd} num))))
  (input : exp (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (enc : exp (ary '{b} (ary '{se} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b : exp (ary '{h * d} num))
  (wqS wkS wvS woS : exp (ary '{h * d} (ary '{h * d} num)))
  (wqC wkC wvC woC : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{sd} (ary '{h * d} num)))) : comm :=
  let ln1 := LayerNorm3d input ln1_g ln1_b eps in
  let mha := DecMHABlock bias ln1 wqS wkS wvS woS in
  let r1 := Add3d input mha in
  let ln2 := LayerNorm3d r1 ln2_g ln2_b eps in
  let cro := CrossMHABlock ln2 enc wqC wkC wvC woC in
  let r2 := Add3d r1 cro in
  let ln3 := LayerNorm3d r2 ln3_g ln3_b eps in
  let f1 := BMatMul2d ln3 w1 in
  let gg := GELU3d f1 in
  let f2 := BMatMul2d gg w2 in
  seq (seq (seq (seq (seq (seq (seq (seq (seq (seq
       (A(acc' (Var "5dln1"), ln1))
       (decmhablock_direct bias ln1 wqS wkS wvS woS (acc' (Var "5dself"))))
       (A(acc' (Var "5dr1"), r1)))
       (A(acc' (Var "5dln2"), ln2)))
       (crossmhablock_direct ln2 enc wqC wkC wvC woC (acc' (Var "5dcro"))))
       (A(acc' (Var "5dr2"), r2)))
       (A(acc' (Var "5dln3"), ln3)))
       (A(acc' (Var "5df1"), f1)))
       (A(acc' (Var "5dg"), gg)))
       (A(acc' (Var "5df2"), f2)))
       (A(output, T5DecoderBlock bias input enc
                                 ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                                 wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps)).

Lemma t5decblock_comm_eq_direct : forall (b sd se h d df : nat)
  (bias : exp (ary '{h} (ary '{sd} (ary '{sd} num))))
  (input : exp (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (enc : exp (ary '{b} (ary '{se} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b : exp (ary '{h * d} num))
  (wqS wkS wvS woS : exp (ary '{h * d} (ary '{h * d} num)))
  (wqC wkC wvC woC : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{sd} (ary '{h * d} num)))),
  t5decblock_comm bias input enc
                  ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                  wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps output =
  t5decblock_direct bias input enc
                    ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                    wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps output.
Proof.
  intros.
  unfold t5decblock_comm, t5decblock_direct, new.
  cbv zeta beta.
  rewrite <- A_LayerNorm3d.
  rewrite bind_read_replace.
  rewrite decmha_comm_eq_direct.
  rewrite decmha_direct_bind.
  rewrite <- A_Add3d.
  rewrite bind_read_replace.
  rewrite <- A_LayerNorm3d.
  rewrite bind_read_replace.
  rewrite crossmha_comm_eq_direct.
  rewrite crossmha_direct_bind.
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
  reflexivity.
Qed.

Lemma A_T5DecoderBlock : forall (b sd se h d df : nat)
  (bias : exp (ary '{h} (ary '{sd} (ary '{sd} num))))
  (input : exp (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (enc : exp (ary '{b} (ary '{se} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b : exp (ary '{h * d} num))
  (wqS wkS wvS woS : exp (ary '{h * d} (ary '{h * d} num)))
  (wqC wkC wvC woC : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  t5decblock_comm bias input enc
                  ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                  wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps output rho p =
  A(output, T5DecoderBlock bias input enc
                           ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                           wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps) rho p.
Proof.
  intros. rewrite t5decblock_comm_eq_direct.
  unfold t5decblock_direct, T5DecoderBlock, FFN, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

Lemma t5decblock_direct_read : forall (b sd se h d df : nat)
  (bias : exp (ary '{h} (ary '{sd} (ary '{sd} num))))
  (input : exp (ary '{b} (ary '{sd} (ary '{h * d} num))))
  (enc : exp (ary '{b} (ary '{se} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b : exp (ary '{h * d} num))
  (wqS wkS wvS woS : exp (ary '{h * d} (ary '{h * d} num)))
  (wqC wkC wvC woC : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{b} (ary '{sd} (ary '{h * d} num))) -> comm) (c0 : comm),
  seq (t5decblock_direct bias input enc
                         ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                         wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (t5decblock_direct bias input enc
                         ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                         wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps (acc' q))
      (seq (k (T5DecoderBlock bias input enc
                              ln1_g ln1_b ln2_g ln2_b ln3_g ln3_b
                              wqS wkS wvS woS wqC wkC wvC woC w1 w2 eps)) c0).
Proof.
  intros. unfold t5decblock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* T5Mini: encoder stack + decoder stack + output head                         *)
(* -------------------------------------------------------------------------- *)

Section T5MiniNet.

  (* All sizes symbolic: batch b, source length se, target length sd,
     heads h, head dimension d (model dimension h*d), FFN width df,
     vocabulary v, bias buckets nb. *)
  Context (b se sd h d df v nb : nat).
  Context (eps : exp num).

  (* Token indices (host-level index maps, cf. [Gather2d]) and the shared
     token embedding table; the relative position bucket maps and the
     per-layer per-head bias tables.  T5 uses NO positional table. *)
  Context (toks_e : fin se -> fin v) (toks_d : fin sd -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{h * d} num))).
  Context (enc_bucket : fin se -> fin se -> fin nb)
          (dec_bucket : fin sd -> fin sd -> fin nb).
  Context (ebt1 ebt2 dbt1 dbt2 : exp (ary '{h} (ary '{nb} num))).

  (* Encoder layer parameters (two layers). *)
  Context (e1_ln1_g e1_ln1_b e1_ln2_g e1_ln2_b : exp (ary '{h * d} num))
          (e1_wq e1_wk e1_wv e1_wo : exp (ary '{h * d} (ary '{h * d} num)))
          (e1_w1 : exp (ary '{h * d} (ary '{df} num)))
          (e1_w2 : exp (ary '{df} (ary '{h * d} num))).
  Context (e2_ln1_g e2_ln1_b e2_ln2_g e2_ln2_b : exp (ary '{h * d} num))
          (e2_wq e2_wk e2_wv e2_wo : exp (ary '{h * d} (ary '{h * d} num)))
          (e2_w1 : exp (ary '{h * d} (ary '{df} num)))
          (e2_w2 : exp (ary '{df} (ary '{h * d} num))).

  (* Decoder layer parameters (two layers). *)
  Context (d1_ln1_g d1_ln1_b d1_ln2_g d1_ln2_b d1_ln3_g d1_ln3_b : exp (ary '{h * d} num))
          (d1_wqS d1_wkS d1_wvS d1_woS : exp (ary '{h * d} (ary '{h * d} num)))
          (d1_wqC d1_wkC d1_wvC d1_woC : exp (ary '{h * d} (ary '{h * d} num)))
          (d1_w1 : exp (ary '{h * d} (ary '{df} num)))
          (d1_w2 : exp (ary '{df} (ary '{h * d} num))).
  Context (d2_ln1_g d2_ln1_b d2_ln2_g d2_ln2_b d2_ln3_g d2_ln3_b : exp (ary '{h * d} num))
          (d2_wqS d2_wkS d2_wvS d2_woS : exp (ary '{h * d} (ary '{h * d} num)))
          (d2_wqC d2_wkC d2_wvC d2_woC : exp (ary '{h * d} (ary '{h * d} num)))
          (d2_w1 : exp (ary '{h * d} (ary '{df} num)))
          (d2_w2 : exp (ary '{df} (ary '{h * d} num))).

  (* Final LayerNorms and the output head (logits over the vocabulary). *)
  Context (lne_g lne_b lnf_g lnf_b : exp (ary '{h * d} num))
          (whead : exp (ary '{h * d} (ary '{v} num))).

  (* Batched embeddings / bias matrices. *)
  Definition BEmbedE : exp (ary '{b} (ary '{se} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => Gather2d toks_e tok_table).
  Definition BEmbedD : exp (ary '{b} (ary '{sd} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => Gather2d toks_d tok_table).
  Definition EBias1 : exp (ary '{h} (ary '{se} (ary '{se} num))) :=
    RelPosBiasHeads enc_bucket ebt1.
  Definition EBias2 : exp (ary '{h} (ary '{se} (ary '{se} num))) :=
    RelPosBiasHeads enc_bucket ebt2.
  Definition DBias1 : exp (ary '{h} (ary '{sd} (ary '{sd} num))) :=
    RelPosBiasHeads dec_bucket dbt1.
  Definition DBias2 : exp (ary '{h} (ary '{sd} (ary '{sd} num))) :=
    RelPosBiasHeads dec_bucket dbt2.

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  Definition t5_enc0 := BEmbedE.
  Definition t5_enc1 := T5EncoderBlock EBias1 t5_enc0
    e1_ln1_g e1_ln1_b e1_ln2_g e1_ln2_b e1_wq e1_wk e1_wv e1_wo e1_w1 e1_w2 eps.
  Definition t5_enc2 := T5EncoderBlock EBias2 t5_enc1
    e2_ln1_g e2_ln1_b e2_ln2_g e2_ln2_b e2_wq e2_wk e2_wv e2_wo e2_w1 e2_w2 eps.
  Definition t5_encF := LayerNorm3d t5_enc2 lne_g lne_b eps.
  Definition t5_dec0 := BEmbedD.
  Definition t5_dec1 := T5DecoderBlock DBias1 t5_dec0 t5_encF
    d1_ln1_g d1_ln1_b d1_ln2_g d1_ln2_b d1_ln3_g d1_ln3_b
    d1_wqS d1_wkS d1_wvS d1_woS d1_wqC d1_wkC d1_wvC d1_woC d1_w1 d1_w2 eps.
  Definition t5_dec2 := T5DecoderBlock DBias2 t5_dec1 t5_encF
    d2_ln1_g d2_ln1_b d2_ln2_g d2_ln2_b d2_ln3_g d2_ln3_b
    d2_wqS d2_wkS d2_wvS d2_woS d2_wqC d2_wkC d2_wvC d2_woC d2_w1 d2_w2 eps.
  Definition t5_dec3 := LayerNorm3d t5_dec2 lnf_g lnf_b eps.
  Definition t5_dec4 := BMatMul2d t5_dec3 whead.

  Lemma t5_enc0_body : t5_enc0 = BEmbedE. Proof. reflexivity. Qed.
  Lemma t5_enc1_body : t5_enc1 = T5EncoderBlock EBias1 t5_enc0
    e1_ln1_g e1_ln1_b e1_ln2_g e1_ln2_b e1_wq e1_wk e1_wv e1_wo e1_w1 e1_w2 eps.
  Proof. reflexivity. Qed.
  Lemma t5_enc2_body : t5_enc2 = T5EncoderBlock EBias2 t5_enc1
    e2_ln1_g e2_ln1_b e2_ln2_g e2_ln2_b e2_wq e2_wk e2_wv e2_wo e2_w1 e2_w2 eps.
  Proof. reflexivity. Qed.
  Lemma t5_encF_body : t5_encF = LayerNorm3d t5_enc2 lne_g lne_b eps.
  Proof. reflexivity. Qed.
  Lemma t5_dec0_body : t5_dec0 = BEmbedD. Proof. reflexivity. Qed.
  Lemma t5_dec1_body : t5_dec1 = T5DecoderBlock DBias1 t5_dec0 t5_encF
    d1_ln1_g d1_ln1_b d1_ln2_g d1_ln2_b d1_ln3_g d1_ln3_b
    d1_wqS d1_wkS d1_wvS d1_woS d1_wqC d1_wkC d1_wvC d1_woC d1_w1 d1_w2 eps.
  Proof. reflexivity. Qed.
  Lemma t5_dec2_body : t5_dec2 = T5DecoderBlock DBias2 t5_dec1 t5_encF
    d2_ln1_g d2_ln1_b d2_ln2_g d2_ln2_b d2_ln3_g d2_ln3_b
    d2_wqS d2_wkS d2_wvS d2_woS d2_wqC d2_wkC d2_wvC d2_woC d2_w1 d2_w2 eps.
  Proof. reflexivity. Qed.
  Lemma t5_dec3_body : t5_dec3 = LayerNorm3d t5_dec2 lnf_g lnf_b eps.
  Proof. reflexivity. Qed.
  Lemma t5_dec4_body : t5_dec4 = BMatMul2d t5_dec3 whead.
  Proof. reflexivity. Qed.

  Opaque t5_enc0 t5_enc1 t5_enc2 t5_encF t5_dec0 t5_dec1 t5_dec2 t5_dec3 t5_dec4.

  Definition T5Mini : exp (ary '{b} (ary '{sd} (ary '{v} num))) := t5_dec4.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  (* The read of the encoder-output buffer t5ef wraps the whole decoder
     stack, so both decoder layers see the encoder output value. *)
  Definition t5mini_comm
    (output : acc (ary '{b} (ary '{sd} (ary '{v} num)))) : comm :=
new (fun t1 => seq (t5encblock_comm EBias1 t5_enc0
    e1_ln1_g e1_ln1_b e1_ln2_g e1_ln2_b e1_wq e1_wk e1_wv e1_wo e1_w1 e1_w2 eps t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => t5encblock_comm EBias2 e1
    e2_ln1_g e2_ln1_b e2_ln2_g e2_ln2_b e2_wq e2_wk e2_wv e2_wo e2_w1 e2_w2 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => LayerNorm3d_comm e2 lne_g lne_b eps t3))
(bind_read t3 (fun ef =>
  new (fun t4 => seq (t5decblock_comm DBias1 t5_dec0 ef
      d1_ln1_g d1_ln1_b d1_ln2_g d1_ln2_b d1_ln3_g d1_ln3_b
      d1_wqS d1_wkS d1_wvS d1_woS d1_wqC d1_wkC d1_wvC d1_woC d1_w1 d1_w2 eps t4)
  (new (fun t5 => seq (bind_read t4 (fun d1 => t5decblock_comm DBias2 d1 ef
      d2_ln1_g d2_ln1_b d2_ln2_g d2_ln2_b d2_ln3_g d2_ln3_b
      d2_wqS d2_wkS d2_wvS d2_woS d2_wqC d2_wkC d2_wvC d2_woC d2_w1 d2_w2 eps t5))
  (new (fun t6 => seq (bind_read t5 (fun d2 => LayerNorm3d_comm d2 lnf_g lnf_b eps t6))
       (bind_read t6 (fun d3 => BMatMul2d_comm d3 whead output))
  ) (acc' (Var "t5df")))
  ) (acc' (Var "t5d2")))
  ) (acc' (Var "t5d1")))))
(acc' (Var "t5ef")))
) (acc' (Var "t5e2")))
) (acc' (Var "t5e1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition t5mini_direct
    (output : acc (ary '{b} (ary '{sd} (ary '{v} num)))) : comm :=
    seq (t5encblock_direct EBias1 t5_enc0
          e1_ln1_g e1_ln1_b e1_ln2_g e1_ln2_b e1_wq e1_wk e1_wv e1_wo e1_w1 e1_w2 eps
          (acc' (Var "t5e1")))
    (seq (t5encblock_direct EBias2 t5_enc1
          e2_ln1_g e2_ln1_b e2_ln2_g e2_ln2_b e2_wq e2_wk e2_wv e2_wo e2_w1 e2_w2 eps
          (acc' (Var "t5e2")))
    (seq (A(acc' (Var "t5ef"), t5_encF))
    (seq (t5decblock_direct DBias1 t5_dec0 t5_encF
          d1_ln1_g d1_ln1_b d1_ln2_g d1_ln2_b d1_ln3_g d1_ln3_b
          d1_wqS d1_wkS d1_wvS d1_woS d1_wqC d1_wkC d1_wvC d1_woC d1_w1 d1_w2 eps
          (acc' (Var "t5d1")))
    (seq (t5decblock_direct DBias2 t5_dec1 t5_encF
          d2_ln1_g d2_ln1_b d2_ln2_g d2_ln2_b d2_ln3_g d2_ln3_b
          d2_wqS d2_wkS d2_wvS d2_woS d2_wqC d2_wkC d2_wvC d2_woC d2_w1 d2_w2 eps
          (acc' (Var "t5d2")))
    (seq (A(acc' (Var "t5df"), t5_dec3))
         (A(output, t5_dec4))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition t5e1_acc : acc (ary '{b} (ary '{se} (ary '{h * d} num)))
    := acc' (Var "t5e1").
  Definition t5e2_acc : acc (ary '{b} (ary '{se} (ary '{h * d} num)))
    := acc' (Var "t5e2").
  Definition t5ef_acc : acc (ary '{b} (ary '{se} (ary '{h * d} num)))
    := acc' (Var "t5ef").
  Definition t5d1_acc : acc (ary '{b} (ary '{sd} (ary '{h * d} num)))
    := acc' (Var "t5d1").
  Definition t5d2_acc : acc (ary '{b} (ary '{sd} (ary '{h * d} num)))
    := acc' (Var "t5d2").
  Definition t5df_acc : acc (ary '{b} (ary '{sd} (ary '{h * d} num)))
    := acc' (Var "t5df").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries 5bln1..5bf2 / 5dln1..5df2 and the MHA temporaries 5tq..5tmg
     are shared between all block instances and are required to be fresh at
     every type (the [minitransformer_fresh] pattern). *)
  Definition t5mini_fresh
    (output : acc (ary '{b} (ary '{sd} (ary '{v} num)))) (rho : env) : Prop :=
    StructUndefined t5e1_acc rho /\
    StructUndefined t5e2_acc rho /\
    StructUndefined t5ef_acc rho /\
    StructUndefined t5d1_acc rho /\
    StructUndefined t5d2_acc rho /\
    StructUndefined t5df_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "5bln1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5bmha") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5br1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5bln2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5bf1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5bg") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5bf2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dln1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dself") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dr1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dln2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dcro") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dr2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dln3") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5df1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5dg") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5df2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tq") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tqs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tk") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tks") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tv") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tvs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tatt") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "5tmg") : acc d0) rho) /\
    (forall p, in_acc p output -> ~ in_acc p t5e1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p t5e2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p t5ef_acc) /\
    (forall p, in_acc p output -> ~ in_acc p t5d1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p t5d2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p t5df_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5bln1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5bmha") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5br1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5bln2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5bf1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5bg") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5bf2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dln1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dself") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dr1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dln2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dcro") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dr2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dln3") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5df1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5dg") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5df2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tq") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tqs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tk") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tks") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tv") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tvs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tatt") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "5tmg") : acc d0)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma t5mini_comm_eq_direct :
    forall (output : acc (ary '{b} (ary '{sd} (ary '{v} num)))),
    t5mini_comm output = t5mini_direct output.
  Proof.
    intros.
    unfold t5mini_comm, t5mini_direct, new.
    cbv beta.
    rewrite t5encblock_comm_eq_direct.
    rewrite t5encblock_direct_read.
    rewrite <- t5_enc1_body.
    rewrite t5encblock_comm_eq_direct.
    rewrite t5encblock_direct_read.
    rewrite <- t5_enc2_body.
    rewrite <- A_LayerNorm3d.
    rewrite <- t5_encF_body.
    rewrite bind_read_replace.
    rewrite t5decblock_comm_eq_direct.
    rewrite t5decblock_direct_read.
    rewrite <- t5_dec1_body.
    rewrite t5decblock_comm_eq_direct.
    rewrite t5decblock_direct_read.
    rewrite <- t5_dec2_body.
    rewrite <- A_LayerNorm3d.
    rewrite <- t5_dec3_body.
    rewrite bind_read_replace.
    rewrite <- A_BMatMul2d.
    rewrite <- t5_dec4_body.
    reflexivity.
  Qed.

  Lemma A_T5Mini_direct :
    forall (output : acc (ary '{b} (ary '{sd} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    t5mini_fresh output rho ->
    t5mini_direct output rho p = A(output, T5Mini) rho p.
  Proof.
    intros.
    unfold t5mini_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold T5Mini. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of the mini T5: under freshness of the
     temporary buffers, the imperative network observed at an output path
     computes the functional [T5Mini]. *)
  Theorem A_T5Mini :
    forall (output : acc (ary '{b} (ary '{sd} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    t5mini_fresh output rho ->
    t5mini_comm output rho p = A(output, T5Mini) rho p.
  Proof.
    intros. rewrite t5mini_comm_eq_direct.
    apply A_T5Mini_direct; assumption.
  Qed.

End T5MiniNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: b = 1, se = 8, sd = 4, h = 2, d = 16 (model dim 32),   *)
(* df = 32, vocab v = 8, bias buckets nb = 8                                   *)
(* -------------------------------------------------------------------------- *)

Section Small_1_8_4_2_16.

  Context (eps8 : exp num)
          (toks_e8 : fin 8 -> fin 8) (toks_d8 : fin 4 -> fin 8)
          (tok_tab8 : exp (ary '{8} (ary '{32} num)))
          (enc_bucket8 : fin 8 -> fin 8 -> fin 8)
          (dec_bucket8 : fin 4 -> fin 4 -> fin 8)
          (ebt_8 dbt_8 : exp (ary '{2} (ary '{8} num)))
          (eg1 eb1 eg2 eb2 : exp (ary '{32} num))
          (ewq ewk ewv ewo : exp (ary '{32} (ary '{32} num)))
          (ew1 : exp (ary '{32} (ary '{32} num)))
          (ew2 : exp (ary '{32} (ary '{32} num)))
          (dg1 db1 dg2 db2 dg3 db3 : exp (ary '{32} num))
          (dwqS dwkS dwvS dwoS : exp (ary '{32} (ary '{32} num)))
          (dwqC dwkC dwvC dwoC : exp (ary '{32} (ary '{32} num)))
          (dw1 : exp (ary '{32} (ary '{32} num)))
          (dw2 : exp (ary '{32} (ary '{32} num)))
          (ge be gf bf : exp (ary '{32} num))
          (wh : exp (ary '{32} (ary '{8} num)))
          (out8 : acc (ary '{1} (ary '{4} (ary '{8} num)))).

  (* Shape check: the symbolic network and its command instantiate at the
     small size (the same parameter set is shared between the two layers of
     each stack; this only checks well-typedness of the instantiation). *)
  Definition T5Mini_1_8_4_2_16 : exp (ary '{1} (ary '{4} (ary '{8} num))) :=
    @T5Mini 1 8 4 2 16 32 8 8
      eps8 toks_e8 toks_d8 tok_tab8 enc_bucket8 dec_bucket8
      ebt_8 ebt_8 dbt_8 dbt_8
      eg1 eb1 eg2 eb2 ewq ewk ewv ewo ew1 ew2
      eg1 eb1 eg2 eb2 ewq ewk ewv ewo ew1 ew2
      dg1 db1 dg2 db2 dg3 db3 dwqS dwkS dwvS dwoS dwqC dwkC dwvC dwoC dw1 dw2
      dg1 db1 dg2 db2 dg3 db3 dwqS dwkS dwvS dwoS dwqC dwkC dwvC dwoC dw1 dw2
      ge be gf bf wh.

  Definition t5mini_comm_1_8_4_2_16 : comm :=
    @t5mini_comm 1 8 4 2 16 32 8 8
      eps8 toks_e8 toks_d8 tok_tab8 enc_bucket8 dec_bucket8
      ebt_8 ebt_8 dbt_8 dbt_8
      eg1 eb1 eg2 eb2 ewq ewk ewv ewo ew1 ew2
      eg1 eb1 eg2 eb2 ewq ewk ewv ewo ew1 ew2
      dg1 db1 dg2 db2 dg3 db3 dwqS dwkS dwvS dwoS dwqC dwkC dwvC dwoC dw1 dw2
      dg1 db1 dg2 db2 dg3 db3 dwqS dwkS dwvS dwoS dwqC dwkC dwvC dwoC dw1 dw2
      ge be gf bf wh out8.

End Small_1_8_4_2_16.

(* [vm_compute]/conversion spot checks of the computable (structural) parts
   of the pipeline. *)

Definition i0_2t : fin 2 := @nat2fin 2 0 (ltac:(lia)).
Definition i0_1t : fin 1 := @nat2fin 1 0 (ltac:(lia)).
Definition i1_2t : fin 2 := @nat2fin 2 1 (ltac:(lia)).
Definition i2_4 : fin 4 := @nat2fin 4 2 (ltac:(lia)).
Definition i3_4t : fin 4 := @nat2fin 4 3 (ltac:(lia)).
Definition i5_8t : fin 8 := @nat2fin 8 5 (ltac:(lia)).

(* Bucket map: bucket(i, j) = min (nb-1) (i + j) at nb = 8. *)
Definition bucket8 : fin 4 -> fin 4 -> fin 8 :=
  fun i j => @nat2fin 8 (Nat.min 7 (fin2nat i + fin2nat j)) (ltac:(lia)).

(* 2 x 8 bias table, entry (h, k) = 10*h + k. *)
Definition BT28 : exp (ary '{2} (ary '{8} num)) :=
  mkvSeq (fun hh : fin 2 => mkvSeq (fun k : fin 8 =>
    (INR (fin2nat hh * 10 + fin2nat k)%nat : exp num))).

(* Bias lookup: head 1, positions (2, 3) -> bucket min 7 5 = 5 -> 15. *)
Example check_rel_bias :
  idx (idx (idx (RelPosBiasHeads bucket8 BT28) i1_2t) i2_4) i3_4t = INR 15.
Proof. vm_compute. reflexivity. Qed.

(* Saturation: positions (3, 3) -> bucket min 7 6 = 6 -> head 0 -> 6. *)
Example check_rel_bias_sat :
  idx (idx (idx (RelPosBiasHeads bucket8 BT28) i0_2t) i3_4t) i3_4t = INR 6.
Proof. vm_compute. reflexivity. Qed.

(* Decoder self-attention cell: the pre-softmax matrix is the causal-masked
   biased score.  Above the diagonal (0, 3) the mask writes [NEGINF]; on the
   diagonal/below (3, 0) the biased score is kept. *)
Definition i0_4t : fin 4 := @nat2fin 4 0 (ltac:(lia)).

Definition M44 : exp (ary '{4} (ary '{4} num)) :=
  mkvSeq (fun i : fin 4 => mkvSeq (fun j : fin 4 =>
    (INR (fin2nat i * 10 + fin2nat j)%nat : exp num))).

Example check_dec_bias_mask_drop :
  idx (idx (CausalMask2d (Add2d M44 M44)) i0_4t) i3_4t = NEGINF.
Proof. reflexivity. Qed.

Example check_dec_bias_mask_keep :
  idx (idx (CausalMask2d (Add2d M44 M44)) i3_4t) i0_4t = add (INR 30) (INR 30).
Proof. reflexivity. Qed.

(* Cross-attention cell: shape check at sq = 4, sk = 8, d = 16 — the cell and
   its command instantiate across the two different sequence lengths. *)
Section CrossShapeCheck.
  Context (qc : exp (ary '{4} (ary '{16} num)))
          (kc vc : exp (ary '{8} (ary '{16} num)))
          (oc : acc (ary '{4} (ary '{16} num))).
  Definition cross_cell_shape : exp (ary '{4} (ary '{16} num)) :=
    CrossAttention_cell qc kc vc.
  Definition cross_cell_comm_shape : comm :=
    cross_attention_cell_comm qc kc vc oc.
End CrossShapeCheck.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_RelPosBiasHeads.
Print Assumptions A_EncAttention_cell.
Print Assumptions A_DecAttention_cell.
Print Assumptions A_CrossAttention_cell.
Print Assumptions A_EncAttnHeads.
Print Assumptions A_DecAttnHeads.
Print Assumptions A_CrossAttnHeads.
Print Assumptions t5mhablock_comm_eq_direct.
Print Assumptions A_T5MHABlock.
Print Assumptions A_EncMHABlock.
Print Assumptions A_DecMHABlock.
Print Assumptions A_CrossMHABlock.
Print Assumptions t5encblock_comm_eq_direct.
Print Assumptions A_T5EncoderBlock.
Print Assumptions t5decblock_comm_eq_direct.
Print Assumptions A_T5DecoderBlock.
Print Assumptions t5mini_comm_eq_direct.
Print Assumptions A_T5Mini.
