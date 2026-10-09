(* DPIA-style Leibniz equivalence proofs for a LLaMA-style decoder block and
   a mini LLaMA network assembled from it (milestone N3b of the NLP/LLM
   extension, cf. doc/NLP与LLM扩展开发规划_20260911.md §2-N3) in the route-A
   R-based expression model.

   Delivered here (all closed with [Qed], no Admitted/Axiom):

   - [RoPEHeads]: rotary position embedding on a split (b, h, s, half*2)
     tensor, applying the [rope_cell] of Ionia.Ops_LLaMA per (batch, head,
     position); the position of a token is its sequence index.

   - [RopeMHABlock]: the RoPE variant of the multi-head causal self-attention
     block of Ionia.Attention_DPIA:
        q = x Wq, k = x Wk, v = x Wv          (batched, [BMatMul2d])
        split heads                            [SplitHeads]
        RoPE on q and k (per head/position)    [RoPEHeads]
        per-head causal attention              [AttnHeads]
        merge heads + output projection        [MergeHeads], [BMatMul2d]
     The imperative block [ropemhablock_comm] stages the computation through
     freshly allocated buffers llq..llmg with [new]/[bind_read], exactly as
     [mhablock_comm]; [ropemhablock_comm_eq_direct] collapses it to the
     buffer-free direct form, [ropemhablock_direct_bind] is the read-back
     lemma for the folded direct form (the [mhablock_direct_bind] pattern),
     and [A_RopeMHABlock] observes the block at an output path.

   - [LLaMABlock]: the pre-norm LLaMA decoder block
        r1 = x + RopeMHA(RMSNorm1(x))
        x2 = r1 + SwiGLU_FFN(RMSNorm2(r1))
     with SwiGLU_FFN = W2 (Swish(x W1) * (x W3)) (three projections, the
     LLaMA FFN; [SwiGLU3d] of Ionia.Ops_LLaMA between two [BMatMul2d]).
     [llamablock_comm] / [llamablock_direct] / [llamablock_comm_eq_direct] /
     [A_LLaMABlock] / [llamablock_direct_read] follow the [TransformerBlock]
     template of Ionia.MiniTransformer_DPIA.

   - [LLaMAMini]: a mini LLaMA decoder-only network, all sizes symbolic
     (batch b, sequence s, heads h, half head dimension half — head dim is
     half*2 —, FFN width df, vocab v):
        token embedding (Gather2d table lookup; no absolute position table —
        RoPE carries the position signal)
        -> LLaMABlock (layer 1) -> LLaMABlock (layer 2)
        -> final RMSNorm -> output head Linear (logits over vocab).
     The number of layers is fixed at N = 2 with per-layer parameters,
     exactly as MiniTransformer/ResNet50 enumerate their blocks.  Layer
     values are folded into [Opaque] constants [ll_x0..ll_x4].
     [A_LLaMAMini] is the end-to-end theorem: under freshness of the
     temporary buffers, the imperative network observed at an output path
     equals the functional network.

   - A concrete instantiation at b = 1, s = 8, h = 2, half = 8 (head dim 16,
     model dim 32), df = 32, v = 8, with [vm_compute]/conversion spot checks
     of the computable parts (embedding gather, RoPE-per-head entry, block
     structure). *)

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
(* [Add3d] / [A_Add3d] (residual). *)
Require Import Ionia.Ops_Elementwise.
(* T1 operators: [Gather2d], [SplitHeads], [MergeHeads]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [BMatMul2d], [AttnHeads] (causal attention cell). *)
Require Import Ionia.Attention_DPIA.
(* N3a: [RMSNorm3d], [SwiGLU3d], [rope_cell]/[rope_cell_comm]/[A_rope_cell]. *)
Require Import Ionia.Ops_LLaMA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* RoPE on a split (b, h, s, half*2) tensor                                    *)
(* -------------------------------------------------------------------------- *)

Definition RoPEHeads {b h s half : nat} (base : exp num)
  (input : exp (ary '{b} (ary '{h} (ary '{s} (ary '{half * 2} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{half * 2} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    mkvSeq (fun ss : fin s => mkvSeq (fun x : fin (half * 2) =>
      rope_cell base half (fin2nat ss) (idx (idx (idx input bb) hh) ss) x)))).

Definition RoPEHeads_comm {b h s half : nat} (base : exp num)
  (input : exp (ary '{b} (ary '{h} (ary '{s} (ary '{half * 2} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{half * 2} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh => mkvSeql (fun ss os =>
    mkvSeql (fun x ox =>
      rope_cell_comm base half (fin2nat ss) (idx (idx (idx input bb) hh) ss) x ox)
      os) oh) ob) output.

Lemma A_RoPEHeads : forall (b h s half : nat) (base : exp num)
  (input : exp (ary '{b} (ary '{h} (ary '{s} (ary '{half * 2} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{half * 2} num))))),
  A(output, RoPEHeads base input) = RoPEHeads_comm base input output.
Proof.
  intros. unfold RoPEHeads, RoPEHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro x.
  rewrite A_rope_cell. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* SwiGLU feed-forward network: W2 (Swish(x W1) * (x W3))                      *)
(* -------------------------------------------------------------------------- *)

Definition SwiGLUFFN {b s dm df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (w1 : exp (ary '{dm} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{dm} num)))
  (w3 : exp (ary '{dm} (ary '{df} num)))
  : exp (ary '{b} (ary '{s} (ary '{dm} num))) :=
  BMatMul2d (SwiGLU3d (BMatMul2d input w1) (BMatMul2d input w3)) w2.

(* -------------------------------------------------------------------------- *)
(* Multi-head attention block with RoPE                                        *)
(* -------------------------------------------------------------------------- *)

(* Functional block: qkv projections, head split, RoPE on q/k, per-head
   causal attention, head merge, output projection. *)
Definition RopeMHABlock {b s h half : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) :=
  let q := BMatMul2d input wq in
  let k := BMatMul2d input wk in
  let v := BMatMul2d input wv in
  let qr := RoPEHeads base (SplitHeads q) in
  let kr := RoPEHeads base (SplitHeads k) in
  let vs := SplitHeads v in
  let att := AttnHeads qr kr vs in
  let merged := MergeHeads att in
  BMatMul2d merged wo.

(* Imperative block: temporaries llq..llmg, output written in place (the
   [mhablock_comm] template, with the two RoPE stages added after the q/k
   splits). *)
Definition ropemhablock_comm {b s h half : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
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
  new (fun tkr => seq (RoPEHeads_comm base eks tkr)
  (bind_read tkr (fun ekr =>
  new (fun tv => seq (BMatMul2d_comm input wv tv)
  (bind_read tv (fun ev =>
  new (fun tvs => seq (SplitHeads_comm ev tvs)
  (bind_read tvs (fun evs =>
  new (fun tatt => seq (AttnHeads_comm eqr ekr evs tatt)
  (bind_read tatt (fun eatt =>
  new (fun tmg => seq (MergeHeads_comm eatt tmg)
  (bind_read tmg (fun emg =>
    BMatMul2d_comm emg wo output)))
  (acc' (Var "llmg")))))
  (acc' (Var "llatt")))))
  (acc' (Var "llvs")))))
  (acc' (Var "llv")))))
  (acc' (Var "llkr")))))
  (acc' (Var "llks")))))
  (acc' (Var "llk")))))
  (acc' (Var "llqr")))))
  (acc' (Var "llqs")))))
  (acc' (Var "llq")).

(* Direct (DPIA-normal) form of the block: a sequence of whole-array
   assignments of the functional stage values. *)
Definition ropemhablock_direct {b s h half : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
  let q := BMatMul2d input wq in
  let k := BMatMul2d input wk in
  let v := BMatMul2d input wv in
  let qs := SplitHeads q in
  let qr := RoPEHeads base qs in
  let ks := SplitHeads k in
  let kr := RoPEHeads base ks in
  let vs := SplitHeads v in
  let att := AttnHeads qr kr vs in
  let merged := MergeHeads att in
  seq (A(acc' (Var "llq"), q))
  (seq (A(acc' (Var "llqs"), qs))
  (seq (A(acc' (Var "llqr"), qr))
  (seq (A(acc' (Var "llk"), k))
  (seq (A(acc' (Var "llks"), ks))
  (seq (A(acc' (Var "llkr"), kr))
  (seq (A(acc' (Var "llv"), v))
  (seq (A(acc' (Var "llvs"), vs))
  (seq (A(acc' (Var "llatt"), att))
  (seq (A(acc' (Var "llmg"), merged))
       (A(output, BMatMul2d merged wo))))))))))).

Lemma ropemhablock_comm_eq_direct : forall (b s h half : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))),
  ropemhablock_comm input base wq wk wv wo output =
  ropemhablock_direct input base wq wk wv wo output.
Proof.
  intros.
  unfold ropemhablock_comm, ropemhablock_direct, new.
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
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
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

(* Reading the block's output buffer after the (folded) direct form yields
   the functional [RopeMHABlock] value (the [mhablock_direct_bind] pattern). *)
Lemma ropemhablock_direct_bind : forall (b s h half : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) -> comm),
  seq (ropemhablock_direct input base wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
  seq (ropemhablock_direct input base wq wk wv wo (acc' q))
      (k (RopeMHABlock input base wq wk wv wo)).
Proof.
  intros. fun_ext.
  unfold ropemhablock_direct, RopeMHABlock, seq, bind_read, A.
  cbv beta zeta.
  rewrite read_exp_assign. reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [RopeMHABlock] (the [A_MHABlock] shape). *)
Lemma A_RopeMHABlock : forall (b s h half : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rho : env) (p : path),
  in_acc p output ->
  ropemhablock_comm input base wq wk wv wo output rho p =
  A(output, RopeMHABlock input base wq wk wv wo) rho p.
Proof.
  intros. rewrite ropemhablock_comm_eq_direct.
  unfold ropemhablock_direct, RopeMHABlock, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pre-norm LLaMA decoder block                                                *)
(* -------------------------------------------------------------------------- *)

Definition LLaMABlock {b s h half df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rms1_g rms2_g : exp (ary '{h * (half * 2)} num))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * (half * 2)} num)))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) :=
  let r1 := Add3d input (RopeMHABlock (RMSNorm3d input rms1_g eps)
                                     base wq wk wv wo) in
  Add3d r1 (SwiGLUFFN (RMSNorm3d r1 rms2_g eps) w1 w2 w3).

(* Imperative block: temporaries lln1, llmha, llr1, lln2, llf1, llf3, llsg,
   llf2.  The attention stage reuses [ropemhablock_comm] (whose internal
   temporaries llq..llmg are distinct from all of the above); the normed
   value e4 feeds both the W1 and the W3 projection. *)
Definition llamablock_comm {b s h half df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rms1_g rms2_g : exp (ary '{h * (half * 2)} num))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * (half * 2)} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
  new (fun t1 => seq (RMSNorm3d_comm input rms1_g eps t1)
  (bind_read t1 (fun e1 =>
  new (fun t2 => seq (ropemhablock_comm e1 base wq wk wv wo t2)
  (bind_read t2 (fun e2 =>
  new (fun t3 => seq (Add3d_comm input e2 t3)
  (bind_read t3 (fun e3 =>
  new (fun t4 => seq (RMSNorm3d_comm e3 rms2_g eps t4)
  (bind_read t4 (fun e4 =>
  new (fun t5 => seq (BMatMul2d_comm e4 w1 t5)
  (bind_read t5 (fun e5 =>
  new (fun t6 => seq (BMatMul2d_comm e4 w3 t6)
  (bind_read t6 (fun e6 =>
  new (fun t7 => seq (SwiGLU3d_comm e5 e6 t7)
  (bind_read t7 (fun e7 =>
  new (fun t8 => seq (BMatMul2d_comm e7 w2 t8)
  (bind_read t8 (fun e8 =>
    Add3d_comm e3 e8 output)))
  (acc' (Var "llf2")))))
  (acc' (Var "llsg")))))
  (acc' (Var "llf3")))))
  (acc' (Var "llf1")))))
  (acc' (Var "lln2")))))
  (acc' (Var "llr1")))))
  (acc' (Var "llmha")))))
  (acc' (Var "lln1")).

(* Direct (DPIA-normal) form of the block, left-associated so the final
   assignment is exposed at the top level (the [transformerblock_direct]
   pattern). *)
Definition llamablock_direct {b s h half df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rms1_g rms2_g : exp (ary '{h * (half * 2)} num))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * (half * 2)} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
  let n1 := RMSNorm3d input rms1_g eps in
  let mha := RopeMHABlock n1 base wq wk wv wo in
  let r1 := Add3d input mha in
  let n2 := RMSNorm3d r1 rms2_g eps in
  let f1 := BMatMul2d n2 w1 in
  let f3 := BMatMul2d n2 w3 in
  let sg := SwiGLU3d f1 f3 in
  let f2 := BMatMul2d sg w2 in
  seq (seq (seq (seq (seq (seq (seq (seq
       (A(acc' (Var "lln1"), n1))
       (ropemhablock_direct n1 base wq wk wv wo (acc' (Var "llmha"))))
       (A(acc' (Var "llr1"), r1)))
       (A(acc' (Var "lln2"), n2)))
       (A(acc' (Var "llf1"), f1)))
       (A(acc' (Var "llf3"), f3)))
       (A(acc' (Var "llsg"), sg)))
       (A(acc' (Var "llf2"), f2)))
       (A(output, LLaMABlock input rms1_g rms2_g base wq wk wv wo
                              w1 w3 w2 eps)).

Lemma llamablock_comm_eq_direct : forall (b s h half df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rms1_g rms2_g : exp (ary '{h * (half * 2)} num))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * (half * 2)} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))),
  llamablock_comm input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps output =
  llamablock_direct input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps output.
Proof.
  intros.
  unfold llamablock_comm, llamablock_direct, new.
  cbv zeta beta.
  rewrite <- A_RMSNorm3d.
  rewrite bind_read_replace.
  rewrite ropemhablock_comm_eq_direct.
  rewrite ropemhablock_direct_bind.
  rewrite <- A_Add3d.
  rewrite bind_read_replace.
  rewrite <- A_RMSNorm3d.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_SwiGLU3d.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  rewrite bind_read_replace.
  rewrite <- A_Add3d.
  reflexivity.
Qed.

(* Block-level DPIA correctness (the [A_TransformerBlock] shape; the final
   assignment is env-independent, so no freshness premise on the temporaries
   is needed). *)
Lemma A_LLaMABlock : forall (b s h half df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rms1_g rms2_g : exp (ary '{h * (half * 2)} num))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * (half * 2)} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rho : env) (p : path),
  in_acc p output ->
  llamablock_comm input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps output rho p =
  A(output, LLaMABlock input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps) rho p.
Proof.
  intros. rewrite llamablock_comm_eq_direct.
  unfold llamablock_direct, LLaMABlock, SwiGLUFFN, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value (the [transformerblock_direct_read] pattern). *)
Lemma llamablock_direct_read : forall (b s h half df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
  (rms1_g rms2_g : exp (ary '{h * (half * 2)} num))
  (base : exp num)
  (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
  (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * (half * 2)} num)))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) -> comm) (c0 : comm),
  seq (llamablock_direct input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps
                         (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (llamablock_direct input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps
                         (acc' q))
      (seq (k (LLaMABlock input rms1_g rms2_g base wq wk wv wo w1 w3 w2 eps)) c0).
Proof.
  intros. unfold llamablock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* LLaMAMini: embedding + 2 x LLaMABlock + final RMSNorm + head                *)
(* -------------------------------------------------------------------------- *)

Section LLaMAMiniNet.

  (* All sizes symbolic: batch b, sequence s, heads h, half head dimension
     half (head dim half*2, model dim h*(half*2)), FFN width df, vocab v. *)
  Context (b s h half df v : nat).
  Context (eps base : exp num).

  (* Token indices (host-level index map, cf. [Gather2d]) and the token
     embedding table.  No absolute position table: RoPE carries the position
     signal inside the blocks. *)
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{h * (half * 2)} num))).

  (* Layer-1 parameters. *)
  Context (l1_rms1_g l1_rms2_g : exp (ary '{h * (half * 2)} num))
          (l1_wq l1_wk l1_wv l1_wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
          (l1_w1 l1_w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
          (l1_w2 : exp (ary '{df} (ary '{h * (half * 2)} num))).

  (* Layer-2 parameters. *)
  Context (l2_rms1_g l2_rms2_g : exp (ary '{h * (half * 2)} num))
          (l2_wq l2_wk l2_wv l2_wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
          (l2_w1 l2_w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
          (l2_w2 : exp (ary '{df} (ary '{h * (half * 2)} num))).

  (* Final RMSNorm and the output head (logits over the vocabulary). *)
  Context (rmsf_g : exp (ary '{h * (half * 2)} num))
          (whead : exp (ary '{h * (half * 2)} (ary '{v} num))).

  (* Batched embedding: the same token sequence in every batch element (the
     batch=1 use case; the table is an arbitrary parameter). *)
  Definition BEmbed : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))) :=
    mkvSeq (fun bb : fin b => Gather2d toks tok_table).

  Definition BEmbed_comm
    (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))) : comm :=
    mkvSeql (fun bb ob => Gather2d_comm toks tok_table ob) output.

  Lemma A_BEmbed : forall
    (output : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))),
    A(output, BEmbed) = BEmbed_comm output.
  Proof.
    intros. unfold BEmbed, BEmbed_comm.
    rewrite AmkvSeq.
    apply seqfor_extensionality. intro bb.
    rewrite A_Gather2d.
    reflexivity.
  Qed.

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  Definition ll_x0 := BEmbed.
  Definition ll_x1 := LLaMABlock ll_x0 l1_rms1_g l1_rms2_g base
                                 l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w3 l1_w2 eps.
  Definition ll_x2 := LLaMABlock ll_x1 l2_rms1_g l2_rms2_g base
                                 l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w3 l2_w2 eps.
  Definition ll_x3 := RMSNorm3d ll_x2 rmsf_g eps.
  Definition ll_x4 := BMatMul2d ll_x3 whead.

  Lemma ll_x0_body : ll_x0 = BEmbed.
  Proof. reflexivity. Qed.
  Lemma ll_x1_body : ll_x1 = LLaMABlock ll_x0 l1_rms1_g l1_rms2_g base
                                 l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w3 l1_w2 eps.
  Proof. reflexivity. Qed.
  Lemma ll_x2_body : ll_x2 = LLaMABlock ll_x1 l2_rms1_g l2_rms2_g base
                                 l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w3 l2_w2 eps.
  Proof. reflexivity. Qed.
  Lemma ll_x3_body : ll_x3 = RMSNorm3d ll_x2 rmsf_g eps.
  Proof. reflexivity. Qed.
  Lemma ll_x4_body : ll_x4 = BMatMul2d ll_x3 whead.
  Proof. reflexivity. Qed.

  Opaque ll_x0 ll_x1 ll_x2 ll_x3 ll_x4.

  Definition LLaMAMini : exp (ary '{b} (ary '{s} (ary '{v} num))) := ll_x4.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition llamamini_comm
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
new (fun t1 => seq (BEmbed_comm t1)
(new (fun t2 => seq (bind_read t1 (fun e1 =>
      llamablock_comm e1 l1_rms1_g l1_rms2_g base
                         l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w3 l1_w2 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 =>
      llamablock_comm e2 l2_rms1_g l2_rms2_g base
                         l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w3 l2_w2 eps t3))
(new (fun t4 => seq (bind_read t3 (fun e3 =>
      RMSNorm3d_comm e3 rmsf_g eps t4))
     (bind_read t4 (fun e4 => BMatMul2d_comm e4 whead output))
) (acc' (Var "l4")))
) (acc' (Var "l3")))
) (acc' (Var "l2")))
) (acc' (Var "l1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition llamamini_direct
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
    seq (A(acc' (Var "l1"), ll_x0))
    (seq (llamablock_direct ll_x0 l1_rms1_g l1_rms2_g base
                            l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w3 l1_w2 eps
                            (acc' (Var "l2")))
    (seq (llamablock_direct ll_x1 l2_rms1_g l2_rms2_g base
                            l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w3 l2_w2 eps
                            (acc' (Var "l3")))
    (seq (A(acc' (Var "l4"), ll_x3))
         (A(output, ll_x4))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition l1_acc : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))
    := acc' (Var "l1").
  Definition l2_acc : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))
    := acc' (Var "l2").
  Definition l3_acc : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))
    := acc' (Var "l3").
  Definition l4_acc : acc (ary '{b} (ary '{s} (ary '{h * (half * 2)} num)))
    := acc' (Var "l4").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries lln1..llf2 and the attention temporaries llq..llmg are
     shared between the two layers and are required to be fresh at every
     type (the [minitransformer_fresh] pattern). *)
  Definition llamamini_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    StructUndefined l1_acc rho /\
    StructUndefined l2_acc rho /\
    StructUndefined l3_acc rho /\
    StructUndefined l4_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "lln1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llmha") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llr1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "lln2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llf1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llf3") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llsg") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llf2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llq") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llqs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llqr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llk") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llks") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llkr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llv") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llvs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llatt") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "llmg") : acc d0) rho) /\
    (forall p, in_acc p output -> ~ in_acc p l1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l4_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "lln1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llmha") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llr1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "lln2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llf1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llf3") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llsg") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llf2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llq") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llqs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llqr") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llk") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llks") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llkr") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llv") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llvs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llatt") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "llmg") : acc d0)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma llamamini_comm_eq_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num)))),
    llamamini_comm output = llamamini_direct output.
  Proof.
    intros.
    unfold llamamini_comm, llamamini_direct, new.
    cbv beta.
    rewrite <- A_BEmbed.
    rewrite <- ll_x0_body.
    rewrite bind_read_replace_seq.
    rewrite llamablock_comm_eq_direct.
    rewrite llamablock_direct_read.
    rewrite <- ll_x1_body.
    rewrite llamablock_comm_eq_direct.
    rewrite llamablock_direct_read.
    rewrite <- ll_x2_body.
    rewrite <- A_RMSNorm3d.
    rewrite <- ll_x3_body.
    rewrite bind_read_replace.
    rewrite <- A_BMatMul2d.
    rewrite <- ll_x4_body.
    reflexivity.
  Qed.

  Lemma A_LLaMAMini_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    llamamini_fresh output rho ->
    llamamini_direct output rho p = A(output, LLaMAMini) rho p.
  Proof.
    intros.
    unfold llamamini_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold LLaMAMini. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of the mini LLaMA: under freshness of the
     temporary buffers, the imperative network observed at an output path
     computes the functional [LLaMAMini]. *)
  Theorem A_LLaMAMini :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    llamamini_fresh output rho ->
    llamamini_comm output rho p = A(output, LLaMAMini) rho p.
  Proof.
    intros. rewrite llamamini_comm_eq_direct.
    apply A_LLaMAMini_direct; assumption.
  Qed.

End LLaMAMiniNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: b = 1, s = 8, h = 2, half = 8 (head dim 16, model dim   *)
(* 32), df = 32, vocab v = 8                                                   *)
(* -------------------------------------------------------------------------- *)

Section Small_1_8_2_8.

  Context (eps8 base8 : exp num)
          (toks8 : fin 8 -> fin 8)
          (tok_tab8 : exp (ary '{8} (ary '{32} num)))
          (r1_1 r2_1 : exp (ary '{32} num))
          (wq1 wk1 wv1 wo1 : exp (ary '{32} (ary '{32} num)))
          (w1_1 w3_1 : exp (ary '{32} (ary '{32} num)))
          (w2_1 : exp (ary '{32} (ary '{32} num)))
          (r1_2 r2_2 : exp (ary '{32} num))
          (wq2 wk2 wv2 wo2 : exp (ary '{32} (ary '{32} num)))
          (w1_2 w3_2 : exp (ary '{32} (ary '{32} num)))
          (w2_2 : exp (ary '{32} (ary '{32} num)))
          (rf : exp (ary '{32} num))
          (wh : exp (ary '{32} (ary '{8} num)))
          (out8 : acc (ary '{1} (ary '{8} (ary '{8} num)))).

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition LLaMAMini_1_8_2_8 : exp (ary '{1} (ary '{8} (ary '{8} num))) :=
    @LLaMAMini 1 8 2 8 32 8
      eps8 base8 toks8 tok_tab8
      r1_1 r2_1 wq1 wk1 wv1 wo1 w1_1 w3_1 w2_1
      r1_2 r2_2 wq2 wk2 wv2 wo2 w1_2 w3_2 w2_2
      rf wh.

  Definition llamamini_comm_1_8_2_8 : comm :=
    @llamamini_comm 1 8 2 8 32 8
      eps8 base8 toks8 tok_tab8
      r1_1 r2_1 wq1 wk1 wv1 wo1 w1_1 w3_1 w2_1
      r1_2 r2_2 wq2 wk2 wv2 wo2 w1_2 w3_2 w2_2
      rf wh out8.

End Small_1_8_2_8.

(* [vm_compute]/conversion spot checks of the computable (structural) parts
   of the pipeline. *)

Definition lm_i1_4 : fin 4 := @nat2fin 4 1 (ltac:(lia)).

(* 4 x 2 embedding table, entry (i, j) = 10*i + j; token index map sends
   position 0 -> token 3, position 1 -> token 1. *)
Definition LT42 : exp (ary '{4} (ary '{2} num)) :=
  mkvSeq (fun i : fin 4 => mkvSeq (fun j : fin 2 =>
    (INR (fin2nat i * 10 + fin2nat j)%nat : exp num))).

Definition ltoks42 : fin 2 -> fin 4 :=
  fun i => if (fin2nat i =? 0)%nat then ll_i3_4 else lm_i1_4.

(* Embedding lookup: output position 0 selects row 3 of the table, whose
   entry 1 is 31. *)
Example check_ll_embed_row3 :
  idx (idx (Gather2d ltoks42 LT42) ll_i0_2) ll_i1_2 = INR 31.
Proof. vm_compute. reflexivity. Qed.

(* RoPEHeads: batch 1, head 1, sequence 2, head dim 4 (half = 2), entry x+1.
   Position 1, pair 1, component 0: x2 * cos(theta) - x3 * sin(theta) with
   theta = rope_theta base pos=1 pair=1. *)
Definition RH124 : exp (ary '{1} (ary '{1} (ary '{2} (ary '{2 * 2} num)))) :=
  mkvSeq (fun bb : fin 1 => mkvSeq (fun hh : fin 1 =>
    mkvSeq (fun ss : fin 2 => mkvSeq (fun x : fin 4 =>
      (INR (S (fin2nat x)) : exp num))))).

Example check_ropeheads_entry : forall (base : exp num),
  idx (idx (idx (idx (RoPEHeads base RH124) ll_i0_1) ll_i0_1) ll_i1_2) ll_i2_4
  = sub (mul (INR 3) (cosE (rope_theta (half:=2) base 1 ll_i1_2)))
        (mul (INR 4) (sinE (rope_theta (half:=2) base 1 ll_i1_2))).
Proof. vm_compute. reflexivity. Qed.

(* SwiGLU FFN structure: W2 (Swish(x W1) * (x W3)). *)
Example check_swigluffn_structure :
  forall (b s dm df : nat)
    (x : exp (ary '{b} (ary '{s} (ary '{dm} num))))
    (w1 : exp (ary '{dm} (ary '{df} num)))
    (w2 : exp (ary '{df} (ary '{dm} num)))
    (w3 : exp (ary '{dm} (ary '{df} num))),
  SwiGLUFFN x w1 w2 w3 =
  BMatMul2d (SwiGLU3d (BMatMul2d x w1) (BMatMul2d x w3)) w2.
Proof. reflexivity. Qed.

(* Block structure: pre-norm, RMSNorm -> RoPE-MHA -> residual -> RMSNorm ->
   SwiGLU FFN -> residual. *)
Example check_llamablock_structure :
  forall (b s h half df : nat)
    (x : exp (ary '{b} (ary '{s} (ary '{h * (half * 2)} num))))
    (g1 g2 : exp (ary '{h * (half * 2)} num))
    (base eps : exp num)
    (wq wk wv wo : exp (ary '{h * (half * 2)} (ary '{h * (half * 2)} num)))
    (w1 w3 : exp (ary '{h * (half * 2)} (ary '{df} num)))
    (w2 : exp (ary '{df} (ary '{h * (half * 2)} num))),
  LLaMABlock x g1 g2 base wq wk wv wo w1 w3 w2 eps =
  Add3d (Add3d x (RopeMHABlock (RMSNorm3d x g1 eps) base wq wk wv wo))
        (SwiGLUFFN (RMSNorm3d (Add3d x (RopeMHABlock (RMSNorm3d x g1 eps)
                                             base wq wk wv wo)) g2 eps)
                   w1 w2 w3).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_RoPEHeads.
Print Assumptions ropemhablock_comm_eq_direct.
Print Assumptions ropemhablock_direct_bind.
Print Assumptions A_RopeMHABlock.
Print Assumptions llamablock_comm_eq_direct.
Print Assumptions A_LLaMABlock.
Print Assumptions llamablock_direct_read.
Print Assumptions llamamini_comm_eq_direct.
Print Assumptions A_LLaMAMini.
