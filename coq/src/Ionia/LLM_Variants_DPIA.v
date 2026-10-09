(* End-to-end DPIA assemblies for three mainstream LLM variants (milestone
   M-d of the mainstream-LLM coverage plan, cf.
   doc/主流大模型覆盖规划_20260914.md §2 item 4) in the route-A R-based
   expression model:

   - Qwen2-mini:  the LLaMA skeleton with BIASED QKV projections (Qwen2 adds
     biases to q/k/v; the biased per-position linear is [Linear3d] of
     Ionia.Ops_PoolPad);
   - Mistral-mini: the LLaMA skeleton with sliding-window attention
     ([SlidingWindowMask2d] of Ionia.Ops_LLaMA_Variants, milestone M-a) and
     GQA KV-head sharing ([GQAExpand] of Ionia.Ops_LLaMA, milestone N3a);
   - Mixtral-mini: the Mistral skeleton with the dense SwiGLU FFN replaced
     by the MoE feed-forward ([MoEFeedForward] of Ionia.Ops_MoE, M-b, in the
     per-token batched form [MoEFFN3d] of Ionia.MLA_DPIA, M-c).

   Since the three variants share the same assembly shape (pre-norm decoder
   block = RMSNorm -> attention -> residual -> RMSNorm -> FFN -> residual;
   network = embedding -> 2 blocks -> final RMSNorm -> output head), the
   file is built around a PARAMETERISED SKELETON proved once:

   - [Section GenBlockSec]: the generic pre-norm decoder block, abstract over
     the attention stage (functional [attF], direct form [attD], staged
     command [attC], with the two lemmas [attC_eq]/[attD_last]) and the FFN
     stage (functional [ffnF], command [ffnC], with [ffnC_correct]).
     [genblock_comm]/[genblock_direct]/[genblock_comm_eq_direct]/
     [A_GenBlock]/[genblock_direct_read] follow the [LLaMABlock] template of
     Ionia.LLaMAMini_DPIA, with the FFN as a single recompute-style stage
     (the [MoEFFN3d] staging precedent of Ionia.MLA_DPIA).

   - [Section GenNetSec]: the generic 2-layer decoder-only network, abstract
     over two block instances (functional/direct/comm + the collapse and
     read lemmas of [GenBlockSec]).  [gennet_comm]/[gennet_direct]/
     [gennet_fresh]/[gennet_comm_eq_direct]/[A_GenNet] follow the
     [LLaMAMini] template: under freshness of the temporary buffers the
     imperative network observed at an output path equals the functional
     network.

   Each variant is then an INSTANTIATION of the skeleton: the attention
   blocks [Qwen2Attn] (biased QKV) and [SWGQAAttn] (sliding window + GQA)
   are proved once each (functional + staged comm + direct form + collapse
   + read-back, the [RopeMHABlock] template), and the three end-to-end
   theorems [A_Qwen2Mini]/[A_MistralMini]/[A_MixtralMini] are one-line
   instances of [A_GenNet].

   All results closed with [Qed], no Admitted/Axiom.  Small-instance shape
   instantiations and structural spot checks close the file, followed by
   the axiom audit. *)

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
(* [Add3d] / [A_Add3d] (residual), [Mulc2d] (attention scaling). *)
Require Import Ionia.Ops_Elementwise.
(* [Softmax2d] (Require Import is not transitive, cf. MLA_DPIA). *)
Require Import Ionia.Ops_Reduce.
(* T1 operators: [Gather2d], [SplitHeads], [MergeHeads], [Transpose2d],
   [MatMul2d]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [BMatMul2d], [AttnHeads], [attn_scale]. *)
Require Import Ionia.Attention_DPIA.
(* N3a: [RMSNorm3d], [SwiGLU3d], [GQAExpand]. *)
Require Import Ionia.Ops_LLaMA.
(* N3b: [RoPEHeads], [SwiGLUFFN] (the LLaMA assembly template). *)
Require Import Ionia.LLaMAMini_DPIA.
(* M-a: [SlidingWindowMask2d]. *)
Require Import Ionia.Ops_LLaMA_Variants.
(* M-b: [MoEFeedForward]. *)
Require Import Ionia.Ops_MoE.
(* M-c: [MoEFFN3d] (per-token batched MoE feed-forward). *)
Require Import Ionia.MLA_DPIA.
(* [Linear3d] (biased per-position linear, the Qwen2 QKV projections). *)
Require Import Ionia.Ops_PoolPad.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Sliding-window attention cell and per-head form (Mistral)                   *)
(* -------------------------------------------------------------------------- *)

(* softmax(SlidingWindowMask(Q K^T / sqrt(d))) V on s x d matrices — the
   [Attention_cell] of Ionia.Attention_DPIA with the causal mask replaced by
   the windowed mask of Ionia.Ops_LLaMA_Variants. *)
Definition SWAttention_cell (win : nat) {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  : exp (ary '{s} (ary '{d} num)) :=
  MatMul2d (Softmax2d (SlidingWindowMask2d win
             (Mulc2d (attn_scale d) (MatMul2d q (Transpose2d k))))) v.

(* The cell command is the final MatMul2d loop nest over the composed score
   expression (the recompute style of [attention_cell_comm]). *)
Definition sw_attention_cell_comm (win : nat) {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (output : acc (ary '{s} (ary '{d} num))) : comm :=
  MatMul2d_comm (Softmax2d (SlidingWindowMask2d win
             (Mulc2d (attn_scale d) (MatMul2d q (Transpose2d k))))) v output.

Lemma A_SWAttention_cell : forall (win s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (output : acc (ary '{s} (ary '{d} num))),
  A(output, SWAttention_cell win q k v) = sw_attention_cell_comm win q k v output.
Proof.
  intros. unfold SWAttention_cell, sw_attention_cell_comm. cbv zeta.
  apply A_MatMul2d.
Qed.

(* Per-head sliding-window attention over a (b, h, s, d) triple. *)
Definition SWAttnHeads (win : nat) {b h s d : nat}
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    SWAttention_cell win (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                         (idx (idx vs bb) hh))).

Definition SWAttnHeads_comm (win : nat) {b h s d : nat}
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    sw_attention_cell_comm win (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                               (idx (idx vs bb) hh) oh) ob) output.

Lemma A_SWAttnHeads : forall (win b h s d : nat)
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))),
  A(output, SWAttnHeads win qs ks vs) = SWAttnHeads_comm win qs ks vs output.
Proof.
  intros. unfold SWAttnHeads, SWAttnHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_SWAttention_cell.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Qwen2 attention block: RoPE-MHA with biased QKV projections                 *)
(* -------------------------------------------------------------------------- *)

(* Functional block: q/k/v projections WITH BIAS (the [Linear3d] of
   Ionia.Ops_PoolPad, weight in (out, in) orientation), head split, RoPE on
   q/k, per-head causal attention, head merge, unbiased output projection
   (the [RopeMHABlock] of Ionia.LLaMAMini_DPIA with biased q/k/v). *)
Definition Qwen2Attn {b s h half : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) :=
  let q := Linear3d input wq bq in
  let k := Linear3d input wk bk in
  let v := Linear3d input wv bv in
  let qr := RoPEHeads base (SplitHeads q) in
  let kr := RoPEHeads base (SplitHeads k) in
  let vs := SplitHeads v in
  let att := AttnHeads qr kr vs in
  BMatMul2d (MergeHeads att) wo.

(* Imperative block: temporaries qw_q..qw_mg (the [ropemhablock_comm]
   template, with [Linear3d_comm] for the biased q/k/v projections). *)
Definition qwen2attn_comm {b s h half : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
  new (fun tq => seq (Linear3d_comm input wq bq tq)
  (bind_read tq (fun eq =>
  new (fun tqs => seq (SplitHeads_comm eq tqs)
  (bind_read tqs (fun eqs =>
  new (fun tqr => seq (RoPEHeads_comm base eqs tqr)
  (bind_read tqr (fun eqr =>
  new (fun tk => seq (Linear3d_comm input wk bk tk)
  (bind_read tk (fun ek =>
  new (fun tks => seq (SplitHeads_comm ek tks)
  (bind_read tks (fun eks =>
  new (fun tkr => seq (RoPEHeads_comm base eks tkr)
  (bind_read tkr (fun ekr =>
  new (fun tv => seq (Linear3d_comm input wv bv tv)
  (bind_read tv (fun ev =>
  new (fun tvs => seq (SplitHeads_comm ev tvs)
  (bind_read tvs (fun evs =>
  new (fun tatt => seq (AttnHeads_comm eqr ekr evs tatt)
  (bind_read tatt (fun eatt =>
  new (fun tmg => seq (MergeHeads_comm eatt tmg)
  (bind_read tmg (fun emg =>
    BMatMul2d_comm emg wo output)))
  (acc' (Var "qw_mg")))))
  (acc' (Var "qw_att")))))
  (acc' (Var "qw_vs")))))
  (acc' (Var "qw_v")))))
  (acc' (Var "qw_kr")))))
  (acc' (Var "qw_ks")))))
  (acc' (Var "qw_k")))))
  (acc' (Var "qw_qr")))))
  (acc' (Var "qw_qs")))))
  (acc' (Var "qw_q")).

(* Direct (DPIA-normal) form: whole-array assignments of the stage values. *)
Definition qwen2attn_direct {b s h half : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
  let q := Linear3d input wq bq in
  let k := Linear3d input wk bk in
  let v := Linear3d input wv bv in
  let qs := SplitHeads q in
  let qr := RoPEHeads base qs in
  let ks := SplitHeads k in
  let kr := RoPEHeads base ks in
  let vs := SplitHeads v in
  let att := AttnHeads qr kr vs in
  let merged := MergeHeads att in
  seq (A(acc' (Var "qw_q"), q))
  (seq (A(acc' (Var "qw_qs"), qs))
  (seq (A(acc' (Var "qw_qr"), qr))
  (seq (A(acc' (Var "qw_k"), k))
  (seq (A(acc' (Var "qw_ks"), ks))
  (seq (A(acc' (Var "qw_kr"), kr))
  (seq (A(acc' (Var "qw_v"), v))
  (seq (A(acc' (Var "qw_vs"), vs))
  (seq (A(acc' (Var "qw_att"), att))
  (seq (A(acc' (Var "qw_mg"), merged))
       (A(output, BMatMul2d merged wo))))))))))).

Lemma qwen2attn_comm_eq_direct : forall (b s h half : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))),
  qwen2attn_comm input base wq wk wv bq bk bv wo output =
  qwen2attn_direct input base wq wk wv bq bk bv wo output.
Proof.
  intros.
  unfold qwen2attn_comm, qwen2attn_direct, new.
  cbv zeta beta.
  rewrite <- A_Linear3d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_Linear3d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_Linear3d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_AttnHeads.
  rewrite bind_read_replace.
  rewrite <- A_MergeHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  reflexivity.
Qed.

(* Read-back lemma for the folded direct form (the [ropemhablock_direct_bind]
   pattern). *)
Lemma qwen2attn_direct_bind : forall (b s h half : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) -> comm),
  seq (qwen2attn_direct input base wq wk wv bq bk bv wo (acc' q))
      (bind_read (acc' q) k) =
  seq (qwen2attn_direct input base wq wk wv bq bk bv wo (acc' q))
      (k (Qwen2Attn input base wq wk wv bq bk bv wo)).
Proof.
  intros. fun_ext.
  unfold qwen2attn_direct, Qwen2Attn, seq, bind_read, A.
  cbv beta zeta.
  rewrite read_exp_assign. reflexivity.
Qed.

(* Block-level DPIA correctness (the [A_RopeMHABlock] shape). *)
Lemma A_Qwen2Attn : forall (b s h half : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rho : env) (p : path),
  in_acc p output ->
  qwen2attn_comm input base wq wk wv bq bk bv wo output rho p =
  A(output, Qwen2Attn input base wq wk wv bq bk bv wo) rho p.
Proof.
  intros. rewrite qwen2attn_comm_eq_direct.
  unfold qwen2attn_direct, Qwen2Attn, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Mistral attention block: sliding-window RoPE-MHA with GQA                   *)
(* -------------------------------------------------------------------------- *)

(* Functional block: h = hk*g query heads share hk KV heads.  q projects to
   the full h*(half*2); k/v project to hk*(half*2); after the head split the
   KV tensors are broadcast to h heads by [GQAExpand]; RoPE acts on q and on
   the expanded k (per head/position); the per-head attention is the
   sliding-window cell [SWAttention_cell]; merge + unbiased output
   projection. *)
Definition SWGQAAttn {b s hk g half : nat} (win : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))) :=
  let q := BMatMul2d input wq in
  let qs := SplitHeads q in
  let qr := RoPEHeads base qs in
  let k := BMatMul2d input wk in
  let ks := SplitHeads k in
  let kx := GQAExpand (g:=g) ks in
  let kr := RoPEHeads base kx in
  let v := BMatMul2d input wv in
  let vs := SplitHeads v in
  let vx := GQAExpand (g:=g) vs in
  let att := SWAttnHeads win qr kr vx in
  BMatMul2d (MergeHeads att) wo.

(* Imperative block: temporaries sw_q..sw_mg (12 buffers: the
   [ropemhablock_comm] template with the two [GQAExpand] stages added after
   the k/v splits). *)
Definition swgqaattn_comm {b s hk g half : nat} (win : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num)))) : comm :=
  new (fun tq => seq (BMatMul2d_comm input wq tq)
  (bind_read tq (fun eq =>
  new (fun tqs => seq (SplitHeads_comm eq tqs)
  (bind_read tqs (fun eqs =>
  new (fun tqr => seq (RoPEHeads_comm base eqs tqr)
  (bind_read tqr (fun eqr =>
  new (fun tk => seq (BMatMul2d_comm input wk tk)
  (bind_read tk (fun ek =>
  new (fun tks => seq (SplitHeads_comm ek tks)
  (bind_read tks (fun eks =>
  new (fun tkx => seq (GQAExpand_comm eks tkx)
  (bind_read tkx (fun ekx =>
  new (fun tkr => seq (RoPEHeads_comm base ekx tkr)
  (bind_read tkr (fun ekr =>
  new (fun tv => seq (BMatMul2d_comm input wv tv)
  (bind_read tv (fun ev =>
  new (fun tvs => seq (SplitHeads_comm ev tvs)
  (bind_read tvs (fun evs =>
  new (fun tvx => seq (GQAExpand_comm evs tvx)
  (bind_read tvx (fun evx =>
  new (fun tatt => seq (SWAttnHeads_comm win eqr ekr evx tatt)
  (bind_read tatt (fun eatt =>
  new (fun tmg => seq (MergeHeads_comm eatt tmg)
  (bind_read tmg (fun emg =>
    BMatMul2d_comm emg wo output)))
  (acc' (Var "sw_mg")))))
  (acc' (Var "sw_att")))))
  (acc' (Var "sw_vx")))))
  (acc' (Var "sw_vs")))))
  (acc' (Var "sw_v")))))
  (acc' (Var "sw_kr")))))
  (acc' (Var "sw_kx")))))
  (acc' (Var "sw_ks")))))
  (acc' (Var "sw_k")))))
  (acc' (Var "sw_qr")))))
  (acc' (Var "sw_qs")))))
  (acc' (Var "sw_q")).

(* Direct (DPIA-normal) form. *)
Definition swgqaattn_direct {b s hk g half : nat} (win : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num)))) : comm :=
  let q := BMatMul2d input wq in
  let qs := SplitHeads q in
  let qr := RoPEHeads base qs in
  let k := BMatMul2d input wk in
  let ks := SplitHeads k in
  let kx := GQAExpand (g:=g) ks in
  let kr := RoPEHeads base kx in
  let v := BMatMul2d input wv in
  let vs := SplitHeads v in
  let vx := GQAExpand (g:=g) vs in
  let att := SWAttnHeads win qr kr vx in
  let merged := MergeHeads att in
  seq (A(acc' (Var "sw_q"), q))
  (seq (A(acc' (Var "sw_qs"), qs))
  (seq (A(acc' (Var "sw_qr"), qr))
  (seq (A(acc' (Var "sw_k"), k))
  (seq (A(acc' (Var "sw_ks"), ks))
  (seq (A(acc' (Var "sw_kx"), kx))
  (seq (A(acc' (Var "sw_kr"), kr))
  (seq (A(acc' (Var "sw_v"), v))
  (seq (A(acc' (Var "sw_vs"), vs))
  (seq (A(acc' (Var "sw_vx"), vx))
  (seq (A(acc' (Var "sw_att"), att))
  (seq (A(acc' (Var "sw_mg"), merged))
       (A(output, BMatMul2d merged wo))))))))))))).

Lemma swgqaattn_comm_eq_direct : forall (b s hk g half : nat) (win : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num)))),
  swgqaattn_comm win input base wq wk wv wo output =
  swgqaattn_direct win input base wq wk wv wo output.
Proof.
  intros.
  unfold swgqaattn_comm, swgqaattn_direct, new.
  cbv zeta beta.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_GQAExpand.
  rewrite bind_read_replace.
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_GQAExpand.
  rewrite bind_read_replace.
  rewrite <- A_SWAttnHeads.
  rewrite bind_read_replace.
  rewrite <- A_MergeHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  reflexivity.
Qed.

Lemma swgqaattn_direct_bind : forall (b s hk g half : nat) (win : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))) -> comm),
  seq (swgqaattn_direct win input base wq wk wv wo (acc' q))
      (bind_read (acc' q) k) =
  seq (swgqaattn_direct win input base wq wk wv wo (acc' q))
      (k (SWGQAAttn win input base wq wk wv wo)).
Proof.
  intros. fun_ext.
  unfold swgqaattn_direct, SWGQAAttn, seq, bind_read, A.
  cbv beta zeta.
  rewrite read_exp_assign. reflexivity.
Qed.

Lemma A_SWGQAAttn : forall (b s hk g half : nat) (win : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (rho : env) (p : path),
  in_acc p output ->
  swgqaattn_comm win input base wq wk wv wo output rho p =
  A(output, SWGQAAttn win input base wq wk wv wo) rho p.
Proof.
  intros. rewrite swgqaattn_comm_eq_direct.
  unfold swgqaattn_direct, SWGQAAttn, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* FFN stage commands (single-stage recompute style, the [MoEFFN3d]           *)
(* precedent of Ionia.MLA_DPIA)                                                *)
(* -------------------------------------------------------------------------- *)

(* Dense SwiGLU FFN (LLaMA/Qwen2/Mistral): the flat command computes the two
   projections and the gate inside the final [BMatMul2d_comm] nest (the
   composed-input style of [attention_cell_comm]). *)
Lemma A_SwiGLUFFN_flat : forall (b s dm df : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (w1 : exp (ary '{dm} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{dm} num)))
  (w3 : exp (ary '{dm} (ary '{df} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{dm} num)))),
  A(output, SwiGLUFFN x w1 w2 w3)
  = BMatMul2d_comm (SwiGLU3d (BMatMul2d x w1) (BMatMul2d x w3)) w2 output.
Proof. intros. unfold SwiGLUFFN. apply A_BMatMul2d. Qed.

(* -------------------------------------------------------------------------- *)
(* Batched embedding (token table lookup broadcast over the batch)            *)
(* -------------------------------------------------------------------------- *)

Definition BEmbedG {b s dm v : nat} (toks : fin s -> fin v)
  (tok_table : exp (ary '{v} (ary '{dm} num)))
  : exp (ary '{b} (ary '{s} (ary '{dm} num))) :=
  mkvSeq (fun bb : fin b => Gather2d toks tok_table).

Definition BEmbedG_comm {b s dm v : nat} (toks : fin s -> fin v)
  (tok_table : exp (ary '{v} (ary '{dm} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{dm} num)))) : comm :=
  mkvSeql (fun bb ob => Gather2d_comm toks tok_table ob) output.

Lemma A_BEmbedG : forall (b s dm v : nat) (toks : fin s -> fin v)
  (tok_table : exp (ary '{v} (ary '{dm} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{dm} num)))),
  A(output, BEmbedG toks tok_table) = BEmbedG_comm toks tok_table output.
Proof.
  intros. unfold BEmbedG, BEmbedG_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite A_Gather2d.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Generic pre-norm decoder block (the parameterised LLM skeleton, block      *)
(* level)                                                                      *)
(* -------------------------------------------------------------------------- *)

Section GenBlockSec.

  Context (b s dm : nat).
  Let T : data := ary '{b} (ary '{s} (ary '{dm} num)).

  (* Attention stage: functional form, direct (DPIA-normal) form, staged
     command, and the two lemmas connecting them (the collapse
     [attC x o = attD x o] and the read-back [attD_last]). *)
  Context (attF : exp T -> exp T).
  Context (attD attC : exp T -> acc T -> comm).
  Context (attC_eq : forall (x : exp T) (o : acc T), attC x o = attD x o).
  Context (attD_last : forall (x : exp T) (q : path) (k : exp T -> comm),
    seq (attD x (acc' q)) (bind_read (acc' q) k)
    = seq (attD x (acc' q)) (k (attF x))).

  (* FFN stage: functional form and single-stage command with its operator
     rule (the recompute-style [ffnC_correct]). *)
  Context (ffnF : exp T -> exp T).
  Context (ffnC : exp T -> acc T -> comm).
  Context (ffnC_correct : forall (x : exp T) (o : acc T),
    A(o, ffnF x) = ffnC x o).

  Context (g1 g2 : exp (ary '{dm} num)) (eps : exp num).

  (* Functional block: r1 = x + att(RMSNorm1 x); out = r1 + ffn(RMSNorm2 r1). *)
  Definition GenBlock (input : exp T) : exp T :=
    let r1 := Add3d input (attF (RMSNorm3d input g1 eps)) in
    Add3d r1 (ffnF (RMSNorm3d r1 g2 eps)).

  (* Imperative block: temporaries gbn1, gbmha, gbr1, gbn2, gbff (the
     [llamablock_comm] template with a single-stage FFN). *)
  Definition genblock_comm (input : exp T) (output : acc T) : comm :=
    new (fun t1 => seq (RMSNorm3d_comm input g1 eps t1)
    (bind_read t1 (fun e1 =>
    new (fun t2 => seq (attC e1 t2)
    (bind_read t2 (fun e2 =>
    new (fun t3 => seq (Add3d_comm input e2 t3)
    (bind_read t3 (fun e3 =>
    new (fun t4 => seq (RMSNorm3d_comm e3 g2 eps t4)
    (bind_read t4 (fun e4 =>
    new (fun t5 => seq (ffnC e4 t5)
    (bind_read t5 (fun e5 =>
      Add3d_comm e3 e5 output)))
    (acc' (Var "gbff")))))
    (acc' (Var "gbn2")))))
    (acc' (Var "gbr1")))))
    (acc' (Var "gbmha")))))
    (acc' (Var "gbn1")).

  (* Direct form, left-associated so the final assignment is exposed at the
     top level (the [llamablock_direct] pattern). *)
  Definition genblock_direct (input : exp T) (output : acc T) : comm :=
    let n1 := RMSNorm3d input g1 eps in
    let r1 := Add3d input (attF n1) in
    let n2 := RMSNorm3d r1 g2 eps in
    let ff := ffnF n2 in
    seq (seq (seq (seq (seq
      (A(acc' (Var "gbn1"), n1))
      (attD n1 (acc' (Var "gbmha"))))
      (A(acc' (Var "gbr1"), r1)))
      (A(acc' (Var "gbn2"), n2)))
      (A(acc' (Var "gbff"), ff)))
      (A(output, GenBlock input)).

  Lemma genblock_comm_eq_direct : forall (input : exp T) (output : acc T),
    genblock_comm input output = genblock_direct input output.
  Proof.
    intros.
    unfold genblock_comm, genblock_direct, new.
    cbv zeta beta.
    rewrite <- A_RMSNorm3d.
    rewrite bind_read_replace.
    rewrite attC_eq.
    rewrite attD_last.
    rewrite <- A_Add3d.
    rewrite bind_read_replace.
    rewrite <- A_RMSNorm3d.
    rewrite bind_read_replace.
    rewrite <- ffnC_correct.
    rewrite bind_read_replace.
    rewrite <- A_Add3d.
    reflexivity.
  Qed.

  (* Block-level DPIA correctness (the [A_LLaMABlock] shape). *)
  Lemma A_GenBlock : forall (input : exp T) (output : acc T)
    (rho : env) (p : path),
    in_acc p output ->
    genblock_comm input output rho p = A(output, GenBlock input) rho p.
  Proof.
    intros. rewrite genblock_comm_eq_direct.
    unfold genblock_direct, GenBlock, A. cbv zeta beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - reflexivity.
  Qed.

  (* Read-back lemma for the folded direct form (the
     [llamablock_direct_read] pattern). *)
  Lemma genblock_direct_read : forall (input : exp T) (q : path)
    (k : exp T -> comm) (c0 : comm),
    seq (genblock_direct input (acc' q)) (seq (bind_read (acc' q) k) c0)
    = seq (genblock_direct input (acc' q)) (seq (k (GenBlock input)) c0).
  Proof.
    intros. unfold genblock_direct. cbv beta zeta.
    apply bind_read_replace_seq_r.
  Qed.

End GenBlockSec.

(* -------------------------------------------------------------------------- *)
(* Generic 2-layer decoder-only network (the parameterised LLM skeleton,      *)
(* network level)                                                              *)
(* -------------------------------------------------------------------------- *)

Section GenNetSec.

  (* All sizes symbolic: batch b, sequence s, model width dm, vocab v. *)
  Context (b s dm v : nat).
  Context (eps : exp num).

  (* Token indices and the token embedding table.  No absolute position
     table: RoPE carries the position signal inside the blocks. *)
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{dm} num))).

  Let T : data := ary '{b} (ary '{s} (ary '{dm} num)).

  (* The two block instances, with the collapse and read-back lemmas of
     [GenBlockSec]. *)
  Context (block1F block2F : exp T -> exp T).
  Context (block1D block2D : exp T -> acc T -> comm).
  Context (block1C block2C : exp T -> acc T -> comm).
  Context (block1C_eq : forall (x : exp T) (o : acc T),
    block1C x o = block1D x o).
  Context (block1D_read : forall (x : exp T) (q : path)
    (k : exp T -> comm) (c0 : comm),
    seq (block1D x (acc' q)) (seq (bind_read (acc' q) k) c0)
    = seq (block1D x (acc' q)) (seq (k (block1F x)) c0)).
  Context (block2C_eq : forall (x : exp T) (o : acc T),
    block2C x o = block2D x o).
  Context (block2D_read : forall (x : exp T) (q : path)
    (k : exp T -> comm) (c0 : comm),
    seq (block2D x (acc' q)) (seq (bind_read (acc' q) k) c0)
    = seq (block2D x (acc' q)) (seq (k (block2F x)) c0)).

  (* Final RMSNorm and the output head (logits over the vocabulary). *)
  Context (rmsf_g : exp (ary '{dm} num)).
  Context (whead : exp (ary '{dm} (ary '{v} num))).

  (* Freshness of the attention-stage temporaries, supplied per variant. *)
  Context (attfresh : env -> Prop).

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  Definition gn_x0 := BEmbedG (b:=b) toks tok_table.
  Definition gn_x1 := block1F gn_x0.
  Definition gn_x2 := block2F gn_x1.
  Definition gn_x3 := RMSNorm3d gn_x2 rmsf_g eps.
  Definition gn_x4 := BMatMul2d gn_x3 whead.

  Lemma gn_x0_body : gn_x0 = BEmbedG (b:=b) toks tok_table.
  Proof. reflexivity. Qed.
  Lemma gn_x1_body : gn_x1 = block1F gn_x0.
  Proof. reflexivity. Qed.
  Lemma gn_x2_body : gn_x2 = block2F gn_x1.
  Proof. reflexivity. Qed.
  Lemma gn_x3_body : gn_x3 = RMSNorm3d gn_x2 rmsf_g eps.
  Proof. reflexivity. Qed.
  Lemma gn_x4_body : gn_x4 = BMatMul2d gn_x3 whead.
  Proof. reflexivity. Qed.

  Opaque gn_x0 gn_x1 gn_x2 gn_x3 gn_x4.

  Definition GenNet : exp (ary '{b} (ary '{s} (ary '{v} num))) := gn_x4.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition gennet_comm
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
new (fun t1 => seq (BEmbedG_comm (b:=b) toks tok_table t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => block1C e1 t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => block2C e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => RMSNorm3d_comm e3 rmsf_g eps t4))
     (bind_read t4 (fun e4 => BMatMul2d_comm e4 whead output))
) (acc' (Var "l4")))
) (acc' (Var "l3")))
) (acc' (Var "l2")))
) (acc' (Var "l1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition gennet_direct
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
    seq (A(acc' (Var "l1"), gn_x0))
    (seq (block1D gn_x0 (acc' (Var "l2")))
    (seq (block2D gn_x1 (acc' (Var "l3")))
    (seq (A(acc' (Var "l4"), gn_x3))
         (A(output, gn_x4))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition gn_l1_acc : acc T := acc' (Var "l1").
  Definition gn_l2_acc : acc T := acc' (Var "l2").
  Definition gn_l3_acc : acc T := acc' (Var "l3").
  Definition gn_l4_acc : acc T := acc' (Var "l4").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output (the
     [llamamini_fresh] pattern; the attention-stage temporaries are covered
     by the per-variant [attfresh]). *)
  Definition gennet_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    StructUndefined gn_l1_acc rho /\
    StructUndefined gn_l2_acc rho /\
    StructUndefined gn_l3_acc rho /\
    StructUndefined gn_l4_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "gbn1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "gbmha") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "gbr1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "gbn2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "gbff") : acc d0) rho) /\
    (forall p, in_acc p output -> ~ in_acc p gn_l1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p gn_l2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p gn_l3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p gn_l4_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "gbn1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "gbmha") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "gbr1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "gbn2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "gbff") : acc d0)) /\
    attfresh rho.

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma gennet_comm_eq_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num)))),
    gennet_comm output = gennet_direct output.
  Proof.
    intros.
    unfold gennet_comm, gennet_direct, new.
    cbv beta.
    rewrite <- A_BEmbedG.
    rewrite <- gn_x0_body.
    rewrite bind_read_replace_seq.
    rewrite block1C_eq.
    rewrite block1D_read.
    rewrite <- gn_x1_body.
    rewrite block2C_eq.
    rewrite block2D_read.
    rewrite <- gn_x2_body.
    rewrite <- A_RMSNorm3d.
    rewrite <- gn_x3_body.
    rewrite bind_read_replace.
    rewrite <- A_BMatMul2d.
    rewrite <- gn_x4_body.
    reflexivity.
  Qed.

  Lemma A_GenNet_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    gennet_fresh output rho ->
    gennet_direct output rho p = A(output, GenNet) rho p.
  Proof.
    intros.
    unfold gennet_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold GenNet. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of the generic 2-layer network: under
     freshness of the temporary buffers, the imperative network observed at
     an output path computes the functional [GenNet]. *)
  Theorem A_GenNet :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    gennet_fresh output rho ->
    gennet_comm output rho p = A(output, GenNet) rho p.
  Proof.
    intros. rewrite gennet_comm_eq_direct.
    apply A_GenNet_direct; assumption.
  Qed.

End GenNetSec.

(* -------------------------------------------------------------------------- *)
(* Qwen2-mini: GenNet with Qwen2Attn blocks and dense SwiGLU FFNs              *)
(* -------------------------------------------------------------------------- *)

Section Qwen2MiniNet.

  (* All sizes symbolic: batch b, sequence s, heads h, half head dimension
     half (head dim half*2, model dim h*(half*2)), FFN width df, vocab v. *)
  Context (b s h half df v : nat).
  Context (eps base : exp num).
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{h * (half * 2)} num))).

  (* Layer-1 parameters (note the QKV biases l1_bq/l1_bk/l1_bv — the Qwen2
     difference from LLaMA). *)
  Context (l1_g1 l1_g2 : exp (ary '{h * (half * 2)} num))
          (l1_wq l1_wk l1_wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
          (l1_bq l1_bk l1_bv : exp (ary '{h * (half * 2)} num))
          (l1_wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
          (l1_w1 l1_w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
          (l1_w2 : exp (ary '{df} (ary '{h * (half * 2)} num))).

  (* Layer-2 parameters. *)
  Context (l2_g1 l2_g2 : exp (ary '{h * (half * 2)} num))
          (l2_wq l2_wk l2_wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
          (l2_bq l2_bk l2_bv : exp (ary '{h * (half * 2)} num))
          (l2_wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
          (l2_w1 l2_w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
          (l2_w2 : exp (ary '{df} (ary '{h * (half * 2)} num))).

  (* Final RMSNorm and the output head. *)
  Context (rmsf_g : exp (ary '{h * (half * 2)} num))
          (whead : exp (ary '{h * (half * 2)} (ary '{v} num))).

  Let Tq : data := ary '{b} (ary '{s} (ary '{h * (half * 2)} num)).

  (* ---- Layer 1: attention stage ---- *)
  Definition qw1_attF (x : exp Tq) : exp Tq :=
    Qwen2Attn x base l1_wq l1_wk l1_wv l1_bq l1_bk l1_bv l1_wo.
  Definition qw1_attD (x : exp Tq) (o : acc Tq) : comm :=
    qwen2attn_direct x base l1_wq l1_wk l1_wv l1_bq l1_bk l1_bv l1_wo o.
  Definition qw1_attC (x : exp Tq) (o : acc Tq) : comm :=
    qwen2attn_comm x base l1_wq l1_wk l1_wv l1_bq l1_bk l1_bv l1_wo o.
  Definition qw1_attC_eq : forall (x : exp Tq) (o : acc Tq),
      qw1_attC x o = qw1_attD x o :=
    fun x o => @qwen2attn_comm_eq_direct b s h half x base
                 l1_wq l1_wk l1_wv l1_bq l1_bk l1_bv l1_wo o.
  Definition qw1_attD_last : forall (x : exp Tq) (q : path)
      (k : exp Tq -> comm),
      seq (qw1_attD x (acc' q)) (bind_read (acc' q) k)
      = seq (qw1_attD x (acc' q)) (k (qw1_attF x)) :=
    fun x q k => @qwen2attn_direct_bind b s h half x base
                   l1_wq l1_wk l1_wv l1_bq l1_bk l1_bv l1_wo q k.

  (* ---- Layer 1: FFN stage ---- *)
  Definition qw1_ffnF (x : exp Tq) : exp Tq := SwiGLUFFN x l1_w1 l1_w2 l1_w3.
  Definition qw1_ffnC (x : exp Tq) (o : acc Tq) : comm :=
    BMatMul2d_comm (SwiGLU3d (BMatMul2d x l1_w1) (BMatMul2d x l1_w3)) l1_w2 o.
  Definition qw1_ffnC_correct : forall (x : exp Tq) (o : acc Tq),
      A(o, qw1_ffnF x) = qw1_ffnC x o :=
    fun x o => @A_SwiGLUFFN_flat b s (h * (half * 2)) df x
                 l1_w1 l1_w2 l1_w3 o.

  (* ---- Layer 2: attention stage ---- *)
  Definition qw2_attF (x : exp Tq) : exp Tq :=
    Qwen2Attn x base l2_wq l2_wk l2_wv l2_bq l2_bk l2_bv l2_wo.
  Definition qw2_attD (x : exp Tq) (o : acc Tq) : comm :=
    qwen2attn_direct x base l2_wq l2_wk l2_wv l2_bq l2_bk l2_bv l2_wo o.
  Definition qw2_attC (x : exp Tq) (o : acc Tq) : comm :=
    qwen2attn_comm x base l2_wq l2_wk l2_wv l2_bq l2_bk l2_bv l2_wo o.
  Definition qw2_attC_eq : forall (x : exp Tq) (o : acc Tq),
      qw2_attC x o = qw2_attD x o :=
    fun x o => @qwen2attn_comm_eq_direct b s h half x base
                 l2_wq l2_wk l2_wv l2_bq l2_bk l2_bv l2_wo o.
  Definition qw2_attD_last : forall (x : exp Tq) (q : path)
      (k : exp Tq -> comm),
      seq (qw2_attD x (acc' q)) (bind_read (acc' q) k)
      = seq (qw2_attD x (acc' q)) (k (qw2_attF x)) :=
    fun x q k => @qwen2attn_direct_bind b s h half x base
                   l2_wq l2_wk l2_wv l2_bq l2_bk l2_bv l2_wo q k.

  (* ---- Layer 2: FFN stage ---- *)
  Definition qw2_ffnF (x : exp Tq) : exp Tq := SwiGLUFFN x l2_w1 l2_w2 l2_w3.
  Definition qw2_ffnC (x : exp Tq) (o : acc Tq) : comm :=
    BMatMul2d_comm (SwiGLU3d (BMatMul2d x l2_w1) (BMatMul2d x l2_w3)) l2_w2 o.
  Definition qw2_ffnC_correct : forall (x : exp Tq) (o : acc Tq),
      A(o, qw2_ffnF x) = qw2_ffnC x o :=
    fun x o => @A_SwiGLUFFN_flat b s (h * (half * 2)) df x
                 l2_w1 l2_w2 l2_w3 o.

  (* ---- The two block instances of the generic skeleton ---- *)
  Definition qw_block1F := @GenBlock b s (h * (half * 2))
                             qw1_attF qw1_ffnF l1_g1 l1_g2 eps.
  Definition qw_block1D := @genblock_direct b s (h * (half * 2))
                             qw1_attF qw1_attD qw1_ffnF l1_g1 l1_g2 eps.
  Definition qw_block1C := @genblock_comm b s (h * (half * 2))
                             qw1_attC qw1_ffnC l1_g1 l1_g2 eps.
  Definition qw_block1C_eq := @genblock_comm_eq_direct b s (h * (half * 2))
    qw1_attF qw1_attD qw1_attC qw1_attC_eq qw1_attD_last
    qw1_ffnF qw1_ffnC qw1_ffnC_correct l1_g1 l1_g2 eps.
  Definition qw_block1D_read := @genblock_direct_read b s (h * (half * 2))
    qw1_attF qw1_attD qw1_ffnF l1_g1 l1_g2 eps.

  Definition qw_block2F := @GenBlock b s (h * (half * 2))
                             qw2_attF qw2_ffnF l2_g1 l2_g2 eps.
  Definition qw_block2D := @genblock_direct b s (h * (half * 2))
                             qw2_attF qw2_attD qw2_ffnF l2_g1 l2_g2 eps.
  Definition qw_block2C := @genblock_comm b s (h * (half * 2))
                             qw2_attC qw2_ffnC l2_g1 l2_g2 eps.
  Definition qw_block2C_eq := @genblock_comm_eq_direct b s (h * (half * 2))
    qw2_attF qw2_attD qw2_attC qw2_attC_eq qw2_attD_last
    qw2_ffnF qw2_ffnC qw2_ffnC_correct l2_g1 l2_g2 eps.
  Definition qw_block2D_read := @genblock_direct_read b s (h * (half * 2))
    qw2_attF qw2_attD qw2_ffnF l2_g1 l2_g2 eps.

  (* ---- The network (functional + imperative) ---- *)
  Definition Qwen2Mini := @GenNet b s (h * (half * 2)) v eps toks tok_table
                            qw_block1F qw_block2F rmsf_g whead.
  Definition qwen2mini_comm := @gennet_comm b s (h * (half * 2)) v eps
                                 toks tok_table
                                 qw_block1C qw_block2C rmsf_g whead.

  (* ---- Freshness: the Qwen2 attention temporaries ---- *)
  Definition qw_attfresh (rho : env) : Prop :=
    (forall d0 : data, StructUndefined (acc' (Var "qw_q") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_qs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_qr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_k") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_ks") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_kr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_v") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_vs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_att") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "qw_mg") : acc d0) rho).

  Definition qwen2mini_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    gennet_fresh b s (h * (half * 2)) v qw_attfresh output rho.

  (* ---- End-to-end theorem: a one-line instance of [A_GenNet] ---- *)
  Theorem A_Qwen2Mini :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    qwen2mini_fresh output rho ->
    qwen2mini_comm output rho p = A(output, Qwen2Mini) rho p.
  Proof.
    intros output rho p Hin Hfresh.
    exact (@A_GenNet b s (h * (half * 2)) v eps toks tok_table
             qw_block1F qw_block2F qw_block1D qw_block2D
             qw_block1C qw_block2C
             qw_block1C_eq qw_block1D_read qw_block2C_eq qw_block2D_read
             rmsf_g whead qw_attfresh output rho p Hin Hfresh).
  Qed.

End Qwen2MiniNet.

(* -------------------------------------------------------------------------- *)
(* Mistral-mini: GenNet with SWGQAAttn blocks and dense SwiGLU FFNs            *)
(* -------------------------------------------------------------------------- *)

Section MistralMiniNet.

  (* All sizes symbolic: batch b, sequence s, KV heads hk, query group size
     g (query heads h = hk*g), half head dimension half, FFN width df,
     vocab v, sliding window win. *)
  Context (b s hk g half df v win : nat).
  Context (eps base : exp num).
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{hk * g * (half * 2)} num))).

  (* Layer-1 parameters (k/v project to hk*(half*2) — GQA). *)
  Context (l1_g1 l1_g2 : exp (ary '{hk * g * (half * 2)} num))
          (l1_wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l1_wk l1_wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
          (l1_wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l1_w1 l1_w3 : exp (ary '{hk * g * (half * 2)} (ary '{df} num)))
          (l1_w2 : exp (ary '{df} (ary '{hk * g * (half * 2)} num))).

  (* Layer-2 parameters. *)
  Context (l2_g1 l2_g2 : exp (ary '{hk * g * (half * 2)} num))
          (l2_wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l2_wk l2_wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
          (l2_wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l2_w1 l2_w3 : exp (ary '{hk * g * (half * 2)} (ary '{df} num)))
          (l2_w2 : exp (ary '{df} (ary '{hk * g * (half * 2)} num))).

  Context (rmsf_g : exp (ary '{hk * g * (half * 2)} num))
          (whead : exp (ary '{hk * g * (half * 2)} (ary '{v} num))).

  Let Tm : data := ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num)).

  (* ---- Layer 1: attention stage ---- *)
  Definition mi1_attF (x : exp Tm) : exp Tm :=
    SWGQAAttn win x base l1_wq l1_wk l1_wv l1_wo.
  Definition mi1_attD (x : exp Tm) (o : acc Tm) : comm :=
    swgqaattn_direct win x base l1_wq l1_wk l1_wv l1_wo o.
  Definition mi1_attC (x : exp Tm) (o : acc Tm) : comm :=
    swgqaattn_comm win x base l1_wq l1_wk l1_wv l1_wo o.
  Definition mi1_attC_eq : forall (x : exp Tm) (o : acc Tm),
      mi1_attC x o = mi1_attD x o :=
    fun x o => @swgqaattn_comm_eq_direct b s hk g half win x base
                 l1_wq l1_wk l1_wv l1_wo o.
  Definition mi1_attD_last : forall (x : exp Tm) (q : path)
      (k : exp Tm -> comm),
      seq (mi1_attD x (acc' q)) (bind_read (acc' q) k)
      = seq (mi1_attD x (acc' q)) (k (mi1_attF x)) :=
    fun x q k => @swgqaattn_direct_bind b s hk g half win x base
                   l1_wq l1_wk l1_wv l1_wo q k.

  (* ---- Layer 1: FFN stage ---- *)
  Definition mi1_ffnF (x : exp Tm) : exp Tm := SwiGLUFFN x l1_w1 l1_w2 l1_w3.
  Definition mi1_ffnC (x : exp Tm) (o : acc Tm) : comm :=
    BMatMul2d_comm (SwiGLU3d (BMatMul2d x l1_w1) (BMatMul2d x l1_w3)) l1_w2 o.
  Definition mi1_ffnC_correct : forall (x : exp Tm) (o : acc Tm),
      A(o, mi1_ffnF x) = mi1_ffnC x o :=
    fun x o => @A_SwiGLUFFN_flat b s (hk * g * (half * 2)) df x
                 l1_w1 l1_w2 l1_w3 o.

  (* ---- Layer 2: attention stage ---- *)
  Definition mi2_attF (x : exp Tm) : exp Tm :=
    SWGQAAttn win x base l2_wq l2_wk l2_wv l2_wo.
  Definition mi2_attD (x : exp Tm) (o : acc Tm) : comm :=
    swgqaattn_direct win x base l2_wq l2_wk l2_wv l2_wo o.
  Definition mi2_attC (x : exp Tm) (o : acc Tm) : comm :=
    swgqaattn_comm win x base l2_wq l2_wk l2_wv l2_wo o.
  Definition mi2_attC_eq : forall (x : exp Tm) (o : acc Tm),
      mi2_attC x o = mi2_attD x o :=
    fun x o => @swgqaattn_comm_eq_direct b s hk g half win x base
                 l2_wq l2_wk l2_wv l2_wo o.
  Definition mi2_attD_last : forall (x : exp Tm) (q : path)
      (k : exp Tm -> comm),
      seq (mi2_attD x (acc' q)) (bind_read (acc' q) k)
      = seq (mi2_attD x (acc' q)) (k (mi2_attF x)) :=
    fun x q k => @swgqaattn_direct_bind b s hk g half win x base
                   l2_wq l2_wk l2_wv l2_wo q k.

  (* ---- Layer 2: FFN stage ---- *)
  Definition mi2_ffnF (x : exp Tm) : exp Tm := SwiGLUFFN x l2_w1 l2_w2 l2_w3.
  Definition mi2_ffnC (x : exp Tm) (o : acc Tm) : comm :=
    BMatMul2d_comm (SwiGLU3d (BMatMul2d x l2_w1) (BMatMul2d x l2_w3)) l2_w2 o.
  Definition mi2_ffnC_correct : forall (x : exp Tm) (o : acc Tm),
      A(o, mi2_ffnF x) = mi2_ffnC x o :=
    fun x o => @A_SwiGLUFFN_flat b s (hk * g * (half * 2)) df x
                 l2_w1 l2_w2 l2_w3 o.

  (* ---- The two block instances ---- *)
  Definition mi_block1F := @GenBlock b s (hk * g * (half * 2))
                             mi1_attF mi1_ffnF l1_g1 l1_g2 eps.
  Definition mi_block1D := @genblock_direct b s (hk * g * (half * 2))
                             mi1_attF mi1_attD mi1_ffnF l1_g1 l1_g2 eps.
  Definition mi_block1C := @genblock_comm b s (hk * g * (half * 2))
                             mi1_attC mi1_ffnC l1_g1 l1_g2 eps.
  Definition mi_block1C_eq := @genblock_comm_eq_direct b s (hk * g * (half * 2))
    mi1_attF mi1_attD mi1_attC mi1_attC_eq mi1_attD_last
    mi1_ffnF mi1_ffnC mi1_ffnC_correct l1_g1 l1_g2 eps.
  Definition mi_block1D_read := @genblock_direct_read b s (hk * g * (half * 2))
    mi1_attF mi1_attD mi1_ffnF l1_g1 l1_g2 eps.

  Definition mi_block2F := @GenBlock b s (hk * g * (half * 2))
                             mi2_attF mi2_ffnF l2_g1 l2_g2 eps.
  Definition mi_block2D := @genblock_direct b s (hk * g * (half * 2))
                             mi2_attF mi2_attD mi2_ffnF l2_g1 l2_g2 eps.
  Definition mi_block2C := @genblock_comm b s (hk * g * (half * 2))
                             mi2_attC mi2_ffnC l2_g1 l2_g2 eps.
  Definition mi_block2C_eq := @genblock_comm_eq_direct b s (hk * g * (half * 2))
    mi2_attF mi2_attD mi2_attC mi2_attC_eq mi2_attD_last
    mi2_ffnF mi2_ffnC mi2_ffnC_correct l2_g1 l2_g2 eps.
  Definition mi_block2D_read := @genblock_direct_read b s (hk * g * (half * 2))
    mi2_attF mi2_attD mi2_ffnF l2_g1 l2_g2 eps.

  (* ---- The network ---- *)
  Definition MistralMini := @GenNet b s (hk * g * (half * 2)) v eps
                              toks tok_table
                              mi_block1F mi_block2F rmsf_g whead.
  Definition mistralmini_comm := @gennet_comm b s (hk * g * (half * 2)) v eps
                                   toks tok_table
                                   mi_block1C mi_block2C rmsf_g whead.

  (* ---- Freshness: the sliding-window attention temporaries ---- *)
  Definition sw_attfresh (rho : env) : Prop :=
    (forall d0 : data, StructUndefined (acc' (Var "sw_q") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_qs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_qr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_k") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_ks") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_kx") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_kr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_v") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_vs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_vx") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_att") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "sw_mg") : acc d0) rho).

  Definition mistralmini_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    gennet_fresh b s (hk * g * (half * 2)) v sw_attfresh output rho.

  (* ---- End-to-end theorem ---- *)
  Theorem A_MistralMini :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    mistralmini_fresh output rho ->
    mistralmini_comm output rho p = A(output, MistralMini) rho p.
  Proof.
    intros output rho p Hin Hfresh.
    exact (@A_GenNet b s (hk * g * (half * 2)) v eps toks tok_table
             mi_block1F mi_block2F mi_block1D mi_block2D
             mi_block1C mi_block2C
             mi_block1C_eq mi_block1D_read mi_block2C_eq mi_block2D_read
             rmsf_g whead sw_attfresh output rho p Hin Hfresh).
  Qed.

End MistralMiniNet.

(* -------------------------------------------------------------------------- *)
(* Mixtral-mini: the Mistral skeleton with MoE feed-forward blocks             *)
(* -------------------------------------------------------------------------- *)

Section MixtralMiniNet.

  (* Sizes as Mistral, plus the expert count E (top-2 routing inside
     [MoEFeedForward]). *)
  Context (b s hk g half df v win E : nat).
  Context (eps base : exp num).
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{hk * g * (half * 2)} num))).

  (* Layer-1 parameters: attention as Mistral; the FFN is the MoE gate and
     the per-expert SwiGLU weight families. *)
  Context (l1_g1 l1_g2 : exp (ary '{hk * g * (half * 2)} num))
          (l1_wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l1_wk l1_wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
          (l1_wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l1_wg : exp (ary '{E} (ary '{hk * g * (half * 2)} num)))
          (l1_w1s l1_w3s : exp (ary '{E} (ary '{df} (ary '{hk * g * (half * 2)} num))))
          (l1_w2s : exp (ary '{E} (ary '{hk * g * (half * 2)} (ary '{df} num)))).

  (* Layer-2 parameters. *)
  Context (l2_g1 l2_g2 : exp (ary '{hk * g * (half * 2)} num))
          (l2_wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l2_wk l2_wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
          (l2_wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
          (l2_wg : exp (ary '{E} (ary '{hk * g * (half * 2)} num)))
          (l2_w1s l2_w3s : exp (ary '{E} (ary '{df} (ary '{hk * g * (half * 2)} num))))
          (l2_w2s : exp (ary '{E} (ary '{hk * g * (half * 2)} (ary '{df} num)))).

  Context (rmsf_g : exp (ary '{hk * g * (half * 2)} num))
          (whead : exp (ary '{hk * g * (half * 2)} (ary '{v} num))).

  Let Tx : data := ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num)).

  (* ---- Layer 1: attention stage (shared with Mistral) ---- *)
  Definition mx1_attF (x : exp Tx) : exp Tx :=
    SWGQAAttn win x base l1_wq l1_wk l1_wv l1_wo.
  Definition mx1_attD (x : exp Tx) (o : acc Tx) : comm :=
    swgqaattn_direct win x base l1_wq l1_wk l1_wv l1_wo o.
  Definition mx1_attC (x : exp Tx) (o : acc Tx) : comm :=
    swgqaattn_comm win x base l1_wq l1_wk l1_wv l1_wo o.
  Definition mx1_attC_eq : forall (x : exp Tx) (o : acc Tx),
      mx1_attC x o = mx1_attD x o :=
    fun x o => @swgqaattn_comm_eq_direct b s hk g half win x base
                 l1_wq l1_wk l1_wv l1_wo o.
  Definition mx1_attD_last : forall (x : exp Tx) (q : path)
      (k : exp Tx -> comm),
      seq (mx1_attD x (acc' q)) (bind_read (acc' q) k)
      = seq (mx1_attD x (acc' q)) (k (mx1_attF x)) :=
    fun x q k => @swgqaattn_direct_bind b s hk g half win x base
                   l1_wq l1_wk l1_wv l1_wo q k.

  (* ---- Layer 1: MoE FFN stage ---- *)
  Definition mx1_ffnF (x : exp Tx) : exp Tx :=
    MoEFFN3d x l1_wg l1_w1s l1_w3s l1_w2s.
  Definition mx1_ffnC (x : exp Tx) (o : acc Tx) : comm :=
    MoEFFN3d_comm x l1_wg l1_w1s l1_w3s l1_w2s o.
  Definition mx1_ffnC_correct : forall (x : exp Tx) (o : acc Tx),
      A(o, mx1_ffnF x) = mx1_ffnC x o :=
    fun x o => @A_MoEFFN3d b s E (hk * g * (half * 2)) df x
                 l1_wg l1_w1s l1_w3s l1_w2s o.

  (* ---- Layer 2: attention stage ---- *)
  Definition mx2_attF (x : exp Tx) : exp Tx :=
    SWGQAAttn win x base l2_wq l2_wk l2_wv l2_wo.
  Definition mx2_attD (x : exp Tx) (o : acc Tx) : comm :=
    swgqaattn_direct win x base l2_wq l2_wk l2_wv l2_wo o.
  Definition mx2_attC (x : exp Tx) (o : acc Tx) : comm :=
    swgqaattn_comm win x base l2_wq l2_wk l2_wv l2_wo o.
  Definition mx2_attC_eq : forall (x : exp Tx) (o : acc Tx),
      mx2_attC x o = mx2_attD x o :=
    fun x o => @swgqaattn_comm_eq_direct b s hk g half win x base
                 l2_wq l2_wk l2_wv l2_wo o.
  Definition mx2_attD_last : forall (x : exp Tx) (q : path)
      (k : exp Tx -> comm),
      seq (mx2_attD x (acc' q)) (bind_read (acc' q) k)
      = seq (mx2_attD x (acc' q)) (k (mx2_attF x)) :=
    fun x q k => @swgqaattn_direct_bind b s hk g half win x base
                   l2_wq l2_wk l2_wv l2_wo q k.

  (* ---- Layer 2: MoE FFN stage ---- *)
  Definition mx2_ffnF (x : exp Tx) : exp Tx :=
    MoEFFN3d x l2_wg l2_w1s l2_w3s l2_w2s.
  Definition mx2_ffnC (x : exp Tx) (o : acc Tx) : comm :=
    MoEFFN3d_comm x l2_wg l2_w1s l2_w3s l2_w2s o.
  Definition mx2_ffnC_correct : forall (x : exp Tx) (o : acc Tx),
      A(o, mx2_ffnF x) = mx2_ffnC x o :=
    fun x o => @A_MoEFFN3d b s E (hk * g * (half * 2)) df x
                 l2_wg l2_w1s l2_w3s l2_w2s o.

  (* ---- The two block instances ---- *)
  Definition mx_block1F := @GenBlock b s (hk * g * (half * 2))
                             mx1_attF mx1_ffnF l1_g1 l1_g2 eps.
  Definition mx_block1D := @genblock_direct b s (hk * g * (half * 2))
                             mx1_attF mx1_attD mx1_ffnF l1_g1 l1_g2 eps.
  Definition mx_block1C := @genblock_comm b s (hk * g * (half * 2))
                             mx1_attC mx1_ffnC l1_g1 l1_g2 eps.
  Definition mx_block1C_eq := @genblock_comm_eq_direct b s (hk * g * (half * 2))
    mx1_attF mx1_attD mx1_attC mx1_attC_eq mx1_attD_last
    mx1_ffnF mx1_ffnC mx1_ffnC_correct l1_g1 l1_g2 eps.
  Definition mx_block1D_read := @genblock_direct_read b s (hk * g * (half * 2))
    mx1_attF mx1_attD mx1_ffnF l1_g1 l1_g2 eps.

  Definition mx_block2F := @GenBlock b s (hk * g * (half * 2))
                             mx2_attF mx2_ffnF l2_g1 l2_g2 eps.
  Definition mx_block2D := @genblock_direct b s (hk * g * (half * 2))
                             mx2_attF mx2_attD mx2_ffnF l2_g1 l2_g2 eps.
  Definition mx_block2C := @genblock_comm b s (hk * g * (half * 2))
                             mx2_attC mx2_ffnC l2_g1 l2_g2 eps.
  Definition mx_block2C_eq := @genblock_comm_eq_direct b s (hk * g * (half * 2))
    mx2_attF mx2_attD mx2_attC mx2_attC_eq mx2_attD_last
    mx2_ffnF mx2_ffnC mx2_ffnC_correct l2_g1 l2_g2 eps.
  Definition mx_block2D_read := @genblock_direct_read b s (hk * g * (half * 2))
    mx2_attF mx2_attD mx2_ffnF l2_g1 l2_g2 eps.

  (* ---- The network ---- *)
  Definition MixtralMini := @GenNet b s (hk * g * (half * 2)) v eps
                              toks tok_table
                              mx_block1F mx_block2F rmsf_g whead.
  Definition mixtralmini_comm := @gennet_comm b s (hk * g * (half * 2)) v eps
                                   toks tok_table
                                   mx_block1C mx_block2C rmsf_g whead.

  Definition mixtralmini_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    gennet_fresh b s (hk * g * (half * 2)) v sw_attfresh output rho.

  (* ---- End-to-end theorem ---- *)
  Theorem A_MixtralMini :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    mixtralmini_fresh output rho ->
    mixtralmini_comm output rho p = A(output, MixtralMini) rho p.
  Proof.
    intros output rho p Hin Hfresh.
    exact (@A_GenNet b s (hk * g * (half * 2)) v eps toks tok_table
             mx_block1F mx_block2F mx_block1D mx_block2D
             mx_block1C mx_block2C
             mx_block1C_eq mx_block1D_read mx_block2C_eq mx_block2D_read
             rmsf_g whead sw_attfresh output rho p Hin Hfresh).
  Qed.

End MixtralMiniNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instances: shape checks of the symbolic networks and their        *)
(* commands at small sizes                                                     *)
(* -------------------------------------------------------------------------- *)

(* Qwen2-mini at b = 1, s = 4, h = 2, half = 1 (head dim 2, model dim 4),
   df = 4, v = 4. *)
Section Small_Qwen2.

  Context (eps4 base4 : exp num)
          (toks4 : fin 4 -> fin 4)
          (tok_tab4 : exp (ary '{4} (ary '{4} num)))
          (r1_1 r2_1 : exp (ary '{4} num))
          (wq1 wk1 wv1 : exp (ary '{4} (ary '{4} num)))
          (bq1 bk1 bv1 : exp (ary '{4} num))
          (wo1 : exp (ary '{4} (ary '{4} num)))
          (w1_1 w3_1 : exp (ary '{4} (ary '{4} num)))
          (w2_1 : exp (ary '{4} (ary '{4} num)))
          (r1_2 r2_2 : exp (ary '{4} num))
          (wq2 wk2 wv2 : exp (ary '{4} (ary '{4} num)))
          (bq2 bk2 bv2 : exp (ary '{4} num))
          (wo2 : exp (ary '{4} (ary '{4} num)))
          (w1_2 w3_2 : exp (ary '{4} (ary '{4} num)))
          (w2_2 : exp (ary '{4} (ary '{4} num)))
          (rf : exp (ary '{4} num))
          (wh : exp (ary '{4} (ary '{4} num)))
          (out4 : acc (ary '{1} (ary '{4} (ary '{4} num)))).

  Definition Qwen2Mini_1_4_2_1 : exp (ary '{1} (ary '{4} (ary '{4} num))) :=
    @Qwen2Mini 1 4 2 1 4 4 eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wq1 wk1 wv1 bq1 bk1 bv1 wo1 w1_1 w3_1 w2_1
      r1_2 r2_2 wq2 wk2 wv2 bq2 bk2 bv2 wo2 w1_2 w3_2 w2_2
      rf wh.

  Definition qwen2mini_comm_1_4_2_1 : comm :=
    @qwen2mini_comm 1 4 2 1 4 4 eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wq1 wk1 wv1 bq1 bk1 bv1 wo1 w1_1 w3_1 w2_1
      r1_2 r2_2 wq2 wk2 wv2 bq2 bk2 bv2 wo2 w1_2 w3_2 w2_2
      rf wh out4.

End Small_Qwen2.

(* Mistral-mini at b = 1, s = 4, hk = 1, g = 2 (h = 2 query heads), half = 1
   (head dim 2, model dim 4, KV width 2), df = 4, v = 4, window win = 2. *)
Section Small_Mistral.

  Context (eps4 base4 : exp num)
          (toks4 : fin 4 -> fin 4)
          (tok_tab4 : exp (ary '{4} (ary '{4} num)))
          (r1_1 r2_1 : exp (ary '{4} num))
          (wq1 wo1 : exp (ary '{4} (ary '{4} num)))
          (wk1 wv1 : exp (ary '{4} (ary '{2} num)))
          (w1_1 w3_1 : exp (ary '{4} (ary '{4} num)))
          (w2_1 : exp (ary '{4} (ary '{4} num)))
          (r1_2 r2_2 : exp (ary '{4} num))
          (wq2 wo2 : exp (ary '{4} (ary '{4} num)))
          (wk2 wv2 : exp (ary '{4} (ary '{2} num)))
          (w1_2 w3_2 : exp (ary '{4} (ary '{4} num)))
          (w2_2 : exp (ary '{4} (ary '{4} num)))
          (rf : exp (ary '{4} num))
          (wh : exp (ary '{4} (ary '{4} num)))
          (out4 : acc (ary '{1} (ary '{4} (ary '{4} num)))).

  Definition MistralMini_1_4_1_2 : exp (ary '{1} (ary '{4} (ary '{4} num))) :=
    @MistralMini 1 4 1 2 1 4 4 2 eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wq1 wk1 wv1 wo1 w1_1 w3_1 w2_1
      r1_2 r2_2 wq2 wk2 wv2 wo2 w1_2 w3_2 w2_2
      rf wh.

  Definition mistralmini_comm_1_4_1_2 : comm :=
    @mistralmini_comm 1 4 1 2 1 4 4 2 eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wq1 wk1 wv1 wo1 w1_1 w3_1 w2_1
      r1_2 r2_2 wq2 wk2 wv2 wo2 w1_2 w3_2 w2_2
      rf wh out4.

End Small_Mistral.

(* Mixtral-mini at the Mistral small size with E = 2 experts (top-2
   routing). *)
Section Small_Mixtral.

  Context (eps4 base4 : exp num)
          (toks4 : fin 4 -> fin 4)
          (tok_tab4 : exp (ary '{4} (ary '{4} num)))
          (r1_1 r2_1 : exp (ary '{4} num))
          (wq1 wo1 : exp (ary '{4} (ary '{4} num)))
          (wk1 wv1 : exp (ary '{4} (ary '{2} num)))
          (wg1 : exp (ary '{2} (ary '{4} num)))
          (w1s1 w3s1 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (w2s1 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (r1_2 r2_2 : exp (ary '{4} num))
          (wq2 wo2 : exp (ary '{4} (ary '{4} num)))
          (wk2 wv2 : exp (ary '{4} (ary '{2} num)))
          (wg2 : exp (ary '{2} (ary '{4} num)))
          (w1s2 w3s2 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (w2s2 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (rf : exp (ary '{4} num))
          (wh : exp (ary '{4} (ary '{4} num)))
          (out4 : acc (ary '{1} (ary '{4} (ary '{4} num)))).

  Definition MixtralMini_1_4_1_2 : exp (ary '{1} (ary '{4} (ary '{4} num))) :=
    @MixtralMini 1 4 1 2 1 4 4 2 2 eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wq1 wk1 wv1 wo1 wg1 w1s1 w3s1 w2s1
      r1_2 r2_2 wq2 wk2 wv2 wo2 wg2 w1s2 w3s2 w2s2
      rf wh.

  Definition mixtralmini_comm_1_4_1_2 : comm :=
    @mixtralmini_comm 1 4 1 2 1 4 4 2 2 eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wq1 wk1 wv1 wo1 wg1 w1s1 w3s1 w2s1
      r1_2 r2_2 wq2 wk2 wv2 wo2 wg2 w1s2 w3s2 w2s2
      rf wh out4.

End Small_Mixtral.

(* -------------------------------------------------------------------------- *)
(* Structural spot checks (conversion)                                        *)
(* -------------------------------------------------------------------------- *)

(* The generic block is the pre-norm decoder block: residual around the
   attention stage, residual around the FFN stage. *)
Example check_genblock_structure : forall (b s dm : nat)
  (attF ffnF : exp (ary '{b} (ary '{s} (ary '{dm} num)))
             -> exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (g1 g2 : exp (ary '{dm} num)) (eps : exp num)
  (x : exp (ary '{b} (ary '{s} (ary '{dm} num)))),
  @GenBlock b s dm attF ffnF g1 g2 eps x =
  Add3d (Add3d x (attF (RMSNorm3d x g1 eps)))
        (ffnF (RMSNorm3d (Add3d x (attF (RMSNorm3d x g1 eps))) g2 eps)).
Proof. reflexivity. Qed.

(* Qwen2 attention: biased q/k/v projections, RoPE on q/k, causal per-head
   attention, unbiased output projection. *)
Example check_qwen2attn_structure : forall (b s h half : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (bq bk bv : exp (ary '{h * (half * 2)} num))
  (wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num))),
  Qwen2Attn x base wq wk wv bq bk bv wo =
  BMatMul2d (MergeHeads
    (AttnHeads (RoPEHeads base (SplitHeads (Linear3d x wq bq)))
               (RoPEHeads base (SplitHeads (Linear3d x wk bk)))
               (SplitHeads (Linear3d x wv bv)))) wo.
Proof. reflexivity. Qed.

(* Mistral attention: k/v project to hk heads, are broadcast to hk*g query
   heads by GQAExpand, RoPE on q and the expanded k, sliding-window per-head
   attention. *)
Example check_swgqaattn_structure : forall (b s hk g half win : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{hk * g * (half * 2)} num))))
  (base : exp num)
  (wq : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num)))
  (wk wv : exp (ary '{hk * g * (half * 2)} (ary '{hk * (half * 2)} num)))
  (wo : exp (ary '{hk * g * (half * 2)} (ary '{hk * g * (half * 2)} num))),
  SWGQAAttn win x base wq wk wv wo =
  BMatMul2d (MergeHeads
    (SWAttnHeads win (RoPEHeads base (SplitHeads (BMatMul2d x wq)))
               (RoPEHeads base (GQAExpand (g:=g)
                                  (SplitHeads (BMatMul2d x wk))))
               (GQAExpand (g:=g) (SplitHeads (BMatMul2d x wv))))) wo.
Proof. reflexivity. Qed.

(* The sliding-window cell is softmax(SWMask(QK^T/sqrt(d)))V. *)
Example check_swcell_structure : forall (win s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num))),
  SWAttention_cell win q k v =
  MatMul2d (Softmax2d (SlidingWindowMask2d win
             (Mulc2d (attn_scale d) (MatMul2d q (Transpose2d k))))) v.
Proof. reflexivity. Qed.

(* The Mixtral FFN stage is the per-token MoE feed-forward. *)
Example check_mixtral_ffn_structure : forall (b s E dm df : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (wg : exp (ary '{E} (ary '{dm} num)))
  (w1s w3s : exp (ary '{E} (ary '{df} (ary '{dm} num))))
  (w2s : exp (ary '{E} (ary '{dm} (ary '{df} num)))),
  MoEFFN3d x wg w1s w3s w2s
  = mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s =>
      MoEFeedForward wg w1s w3s w2s (idx (idx x bb) ss))).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_SWAttention_cell.
Print Assumptions A_SWAttnHeads.
Print Assumptions qwen2attn_comm_eq_direct.
Print Assumptions A_Qwen2Attn.
Print Assumptions swgqaattn_comm_eq_direct.
Print Assumptions A_SWGQAAttn.
Print Assumptions A_SwiGLUFFN_flat.
Print Assumptions A_BEmbedG.
Print Assumptions genblock_comm_eq_direct.
Print Assumptions A_GenBlock.
Print Assumptions genblock_direct_read.
Print Assumptions gennet_comm_eq_direct.
Print Assumptions A_GenNet.
Print Assumptions A_Qwen2Mini.
Print Assumptions A_MistralMini.
Print Assumptions A_MixtralMini.
