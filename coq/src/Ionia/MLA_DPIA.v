(* DPIA-style Leibniz equivalence proofs for MLA (Multi-head Latent
   Attention, the DeepSeek-V2/V3 attention form) and a mini DeepSeek-style
   network assembled from it — milestone M-c of the mainstream-LLM coverage
   plan (doc/主流大模型覆盖规划_20260914.md §3), in the route-A R-based
   expression model.

   The two architectural points of MLA (DeepSeek-V2):

   1. KV low-rank compression: the token is first projected to a latent
      vector c_t = W_DKV x_t (and c^Q_t = W_DQ x_t on the query side); K and
      V are DEcompressed from the latent at use time (k = W_UK c_t, v =
      W_UV c_t).  Both directions are Linear chains, delivered as the
      [MLACompress] / [MLAExpand] wrappers of [BMatMul2d] with the rules
      [A_MLA_Compress] / [A_MLA_Expand].

   2. Decoupled RoPE: only PART of each head's K/Q dimension carries the
      rotary position embedding; the rest (the "nope" part decompressed
      from the latent) does not.  Modelled by splitting the per-head
      dimension into dn (nope) + hr*2 (rope): the rope part is projected
      separately (W_QR / W_KR), rotated by the already-proved [RoPEHeads]
      of Ionia.LLaMAMini_DPIA, and concatenated back per head by the new
      [HeadConcat] operator (the per-head last-axis concatenation, built on
      the [Nat.ltb_spec0] index split of Ionia.Ops_Concat).

   Delivered here (all closed with [Qed], no Admitted/Axiom):

   - [HeadConcat]: per-head concatenation (b,h,s,dn) + (b,h,s,dr) ->
     (b,h,s,dn+dr), the Concat4dCell index-split pattern one head level
     down; [A_HeadConcat].

   - [Attention_cellV] / [AttnHeadsV]: the value-dim-polymorphic variants
     of the causal attention cell / per-head attention of
     Ionia.Attention_DPIA (q,k : s x dk, v : s x dv, out : s x dv) — MLA
     needs dk = dn + hr*2 (concatenated nope+rope) but dv = dn.  The scale
     factor is 1/sqrt(dk).

   - [A_MLA_Compress] / [A_MLA_Expand]: the compress/decompress rules
     (thin named wrappers of [A_BMatMul2d], kept as separate constants so
     the staged proofs can address the two directions individually).

   - [MoEFFN3d]: the per-token batching of [MoEFeedForward]
     (Ionia.Ops_MoE, milestone M-b) over (b, s) positions; [A_MoEFFN3d].

   - [MLABlock]: the MLA attention block
        c_q  = W_DQ x                       (Q low-rank compress)
        c_kv = W_DKV x                      (KV low-rank compress)
        q    = [ W_UQ c_q ; RoPE(W_QR c_q) ]   (per-head concat)
        k    = [ W_UK c_kv ; RoPE(W_KR x)  ]
        v    = W_UV c_kv
        out  = (MergeHeads (AttnHeadsV q k v)) Wo
     with the imperative block [mlablock_comm] staging the computation
     through 18 freshly allocated buffers mlcq..mlmg (the [mhablock_comm]
     template), [mlablock_comm_eq_direct] collapsing it to the buffer-free
     direct form, [mlablock_direct_bind] the read-back lemma, and
     [A_MLABlock] observing the block at an output path.

   - [DeepSeekBlock]: the pre-norm DeepSeek decoder block
        r1 = x + MLA(RMSNorm1(x))
        x2 = r1 + MoEFFN(RMSNorm2(r1))
     (the [LLaMABlock] template with RopeMHA -> MLA and SwiGLU-FFN ->
     MoE-FFN; the MoE stage needs no internal buffers since
     [MoEFeedForward_comm] is already a direct loop nest, so the FFN is a
     single staged assignment).

   - [DeepSeekMini]: token embedding (Gather2d broadcast, no absolute
     position table — RoPE carries the position signal) -> 2 x
     DeepSeekBlock -> final RMSNorm -> output head, all sizes symbolic.
     [A_DeepSeekMini] is the end-to-end theorem: under freshness of the
     temporary buffers, the imperative network observed at an output path
     equals the functional network (the [A_LLaMAMini] shape).

   - A concrete instantiation at b = 1, s = 4, h = 2, dn = 2, hr = 1
     (model dim 4, per-head dk = 4), dc = dq = 2, df = 4, E = 2 experts,
     vocab 4, with [vm_compute]/conversion spot checks. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Arith Lia.
Import Proof_CodeGen.
(* [bind_read] and the bind_read elimination lemmas. *)
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
(* [bind_read_replace_seq_r] (left-associated prefix variant). *)
Require Import Ionia.ResNet18_DPIA.
(* [Add3d] / [A_Add3d] (residual). *)
Require Import Ionia.Ops_Elementwise.
(* [Softmax2d]. *)
Require Import Ionia.Ops_Reduce.
(* T1 operators: [Gather2d], [SplitHeads], [MergeHeads]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [BMatMul2d], [AttnHeads], [attn_scale]. *)
Require Import Ionia.Attention_DPIA.
(* N3a: [RMSNorm3d], [rope_cell]; N3b: [RoPEHeads]. *)
Require Import Ionia.Ops_LLaMA.
Require Import Ionia.LLaMAMini_DPIA.
(* M-b: [MoEFeedForward]. *)
Require Import Ionia.Ops_MoE.
(* [concat_split_lt] (index-split bound for concatenation). *)
Require Import Ionia.Ops_Concat.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Per-head concatenation (nope part ++ rope part along the head dimension)    *)
(* -------------------------------------------------------------------------- *)

(* The index split is the [Concat4dCell] pattern of Ionia.Ops_Concat: the
   flat head-dim index [x : fin (dn + dr)] is split by the Coq-level boundary
   test [Nat.ltb_spec0]; the two branches read the nope tensor at [x] resp.
   the rope tensor at [x - dn], with the bounds discharged by
   [concat_split_lt] and [fin_proof]. *)
Definition HeadConcatCell {b h s dn dr : nat}
  (u : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dn} num)))))
  (w : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dr} num)))))
  (bb : fin b) (hh : fin h) (ss : fin s) (x : fin (dn + dr)) : exp num :=
  match Nat.ltb_spec0 (fin2nat x) dn with
  | ReflectT _ Hlt => idx (idx (idx (idx u bb) hh) ss) (nat2fin Hlt)
  | ReflectF _ Hge =>
      idx (idx (idx (idx w bb) hh) ss)
          (nat2fin (concat_split_lt (fin2nat x) dn dr Hge (fin_proof x)))
  end.

Definition HeadConcat {b h s dn dr : nat}
  (u : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dn} num)))))
  (w : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dr} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dn + dr} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    mkvSeq (fun ss : fin s => mkvSeq (fun x : fin (dn + dr) =>
      HeadConcatCell u w bb hh ss x)))).

Definition HeadConcat_comm {b h s dn dr : nat}
  (u : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dn} num)))))
  (w : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dr} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{dn + dr} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh => mkvSeql (fun ss os =>
    mkvSeql (fun x ox => ox |:= HeadConcatCell u w bb hh ss x) os) oh) ob)
    output.

Lemma A_HeadConcat : forall (b h s dn dr : nat)
  (u : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dn} num)))))
  (w : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dr} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{dn + dr} num))))),
  A(output, HeadConcat u w) = HeadConcat_comm u w output.
Proof.
  intros. unfold HeadConcat, HeadConcat_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro x.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Attention cell with a separate value dimension (q,k : s x dk, v : s x dv)   *)
(* -------------------------------------------------------------------------- *)

(* The scale factor uses the FULL per-head key dimension dk = dn + hr*2
   (the concatenated nope+rope part), as in DeepSeek-V2. *)
Definition Attention_cellV {s dk dv : nat}
  (q k : exp (ary '{s} (ary '{dk} num)))
  (v : exp (ary '{s} (ary '{dv} num)))
  : exp (ary '{s} (ary '{dv} num)) :=
  MatMul2d (Softmax2d (CausalMask2d (Mulc2d (attn_scale dk)
                                             (MatMul2d q (Transpose2d k))))) v.

Definition attention_cellV_comm {s dk dv : nat}
  (q k : exp (ary '{s} (ary '{dk} num)))
  (v : exp (ary '{s} (ary '{dv} num)))
  (output : acc (ary '{s} (ary '{dv} num))) : comm :=
  MatMul2d_comm (Softmax2d (CausalMask2d (Mulc2d (attn_scale dk)
                                                 (MatMul2d q (Transpose2d k)))))
                v output.

Lemma A_Attention_cellV : forall (s dk dv : nat)
  (q k : exp (ary '{s} (ary '{dk} num)))
  (v : exp (ary '{s} (ary '{dv} num)))
  (output : acc (ary '{s} (ary '{dv} num))),
  A(output, Attention_cellV q k v) = attention_cellV_comm q k v output.
Proof.
  intros. unfold Attention_cellV, attention_cellV_comm.
  apply A_MatMul2d.
Qed.

Definition AttnHeadsV {b h s dk dv : nat}
  (qs ks : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dk} num)))))
  (vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dv} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dv} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    Attention_cellV (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                    (idx (idx vs bb) hh))).

Definition AttnHeadsV_comm {b h s dk dv : nat}
  (qs ks : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dk} num)))))
  (vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dv} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{dv} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    attention_cellV_comm (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                         (idx (idx vs bb) hh) oh) ob) output.

Lemma A_AttnHeadsV : forall (b h s dk dv : nat)
  (qs ks : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dk} num)))))
  (vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{dv} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{dv} num))))),
  A(output, AttnHeadsV qs ks vs) = AttnHeadsV_comm qs ks vs output.
Proof.
  intros. unfold AttnHeadsV, AttnHeadsV_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_Attention_cellV.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* KV/Q low-rank compress and expand (the two directions of the MLA latent)    *)
(* -------------------------------------------------------------------------- *)

(* Compress: project the token to the latent vector (W_DKV x, W_DQ x). *)
Definition MLACompress {b s dm dc : nat}
  (x : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (w : exp (ary '{dm} (ary '{dc} num)))
  : exp (ary '{b} (ary '{s} (ary '{dc} num))) :=
  BMatMul2d x w.

Lemma A_MLA_Compress : forall (b s dm dc : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (w : exp (ary '{dm} (ary '{dc} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{dc} num)))),
  A(output, MLACompress x w) = BMatMul2d_comm x w output.
Proof. intros. apply A_BMatMul2d. Qed.

(* Expand: decompress K/V/Q from the latent at use time (W_UK c, W_UV c,
   W_UQ c_q; the rope parts W_KR x / W_QR c_q are plain [MLACompress]-shaped
   projections, addressed by [A_MLA_Compress]/[A_MLA_Expand] as well). *)
Definition MLAExpand {b s dc do : nat}
  (c : exp (ary '{b} (ary '{s} (ary '{dc} num))))
  (w : exp (ary '{dc} (ary '{do} num)))
  : exp (ary '{b} (ary '{s} (ary '{do} num))) :=
  BMatMul2d c w.

Lemma A_MLA_Expand : forall (b s dc do : nat)
  (c : exp (ary '{b} (ary '{s} (ary '{dc} num))))
  (w : exp (ary '{dc} (ary '{do} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{do} num)))),
  A(output, MLAExpand c w) = BMatMul2d_comm c w output.
Proof. intros. apply A_BMatMul2d. Qed.

(* -------------------------------------------------------------------------- *)
(* MoE feed-forward batched over (b, s) positions (reuses M-b MoEFeedForward)  *)
(* -------------------------------------------------------------------------- *)

Definition MoEFFN3d {b s E d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  : exp (ary '{b} (ary '{s} (ary '{d} num))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s =>
    MoEFeedForward Wg W1s W3s W2s (idx (idx input bb) ss))).

(* The command is the direct per-token nest: [MoEFeedForward_comm] already
   writes no temporary buffers (the LayerNorm recompute precedent), so no
   staging is needed. *)
Definition MoEFFN3d_comm {b s E d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun ss os =>
    MoEFeedForward_comm Wg W1s W3s W2s (idx (idx input bb) ss) os) ob) output.

Lemma A_MoEFFN3d : forall (b s E d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))),
  A(output, MoEFFN3d input Wg W1s W3s W2s)
  = MoEFFN3d_comm input Wg W1s W3s W2s output.
Proof.
  intros. unfold MoEFFN3d, MoEFFN3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite A_MoEFeedForward.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The MLA attention block (DeepSeek-V2): compress -> partial RoPE -> expand   *)
(* -> per-head causal attention -> merge -> output projection                  *)
(* -------------------------------------------------------------------------- *)

(* Model dim is h*dn (so the merged attention output h*dn and the residual
   stream share the width); dn = per-head nope dim, hr*2 = per-head rope
   dim, dc = KV latent dim, dq = Q latent dim. *)
Definition MLABlock {b s h dn hr dc dq : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * dn} num))) :=
  let c_q := MLACompress input w_dq in
  let c_kv := MLACompress input w_dkv in
  let q_n := MLAExpand c_q w_uq in
  let q_ns := SplitHeads q_n in
  let q_r := MLAExpand c_q w_qr in
  let q_rs := SplitHeads q_r in
  let q_rr := RoPEHeads base q_rs in
  let k_n := MLAExpand c_kv w_uk in
  let k_ns := SplitHeads k_n in
  let k_r := MLACompress input w_kr in
  let k_rs := SplitHeads k_r in
  let k_rr := RoPEHeads base k_rs in
  let v := MLAExpand c_kv w_uv in
  let vs := SplitHeads v in
  let q := HeadConcat q_ns q_rr in
  let k := HeadConcat k_ns k_rr in
  let att := AttnHeadsV q k vs in
  let merged := MergeHeads att in
  BMatMul2d merged wo.

(* Imperative block: temporaries mlcq..mlmg (18 buffers), output written in
   place (the [ropemhablock_comm] template, with the compress/expand and
   per-head concat stages added). *)
Definition mlablock_comm {b s h dn hr dc dq : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))) : comm :=
  new (fun tcq => seq (BMatMul2d_comm input w_dq tcq)
  (bind_read tcq (fun ecq =>
  new (fun tckv => seq (BMatMul2d_comm input w_dkv tckv)
  (bind_read tckv (fun eckv =>
  new (fun tqn => seq (BMatMul2d_comm ecq w_uq tqn)
  (bind_read tqn (fun eqn =>
  new (fun tqns => seq (SplitHeads_comm eqn tqns)
  (bind_read tqns (fun eqns =>
  new (fun tqr => seq (BMatMul2d_comm ecq w_qr tqr)
  (bind_read tqr (fun eqr =>
  new (fun tqrs => seq (SplitHeads_comm eqr tqrs)
  (bind_read tqrs (fun eqrs =>
  new (fun tqrr => seq (RoPEHeads_comm base eqrs tqrr)
  (bind_read tqrr (fun eqrr =>
  new (fun tkn => seq (BMatMul2d_comm eckv w_uk tkn)
  (bind_read tkn (fun ekn =>
  new (fun tkns => seq (SplitHeads_comm ekn tkns)
  (bind_read tkns (fun ekns =>
  new (fun tkr => seq (BMatMul2d_comm input w_kr tkr)
  (bind_read tkr (fun ekr =>
  new (fun tkrs => seq (SplitHeads_comm ekr tkrs)
  (bind_read tkrs (fun ekrs =>
  new (fun tkrr => seq (RoPEHeads_comm base ekrs tkrr)
  (bind_read tkrr (fun ekrr =>
  new (fun tv => seq (BMatMul2d_comm eckv w_uv tv)
  (bind_read tv (fun ev =>
  new (fun tvs => seq (SplitHeads_comm ev tvs)
  (bind_read tvs (fun evs =>
  new (fun tq => seq (HeadConcat_comm eqns eqrr tq)
  (bind_read tq (fun eqc =>
  new (fun tk => seq (HeadConcat_comm ekns ekrr tk)
  (bind_read tk (fun ekc =>
  new (fun tatt => seq (AttnHeadsV_comm eqc ekc evs tatt)
  (bind_read tatt (fun eatt =>
  new (fun tmg => seq (MergeHeads_comm eatt tmg)
  (bind_read tmg (fun emg =>
    BMatMul2d_comm emg wo output)))
  (acc' (Var "mlmg")))))
  (acc' (Var "mlatt")))))
  (acc' (Var "mlk")))))
  (acc' (Var "mlq")))))
  (acc' (Var "mlvs")))))
  (acc' (Var "mlv")))))
  (acc' (Var "mlkrr")))))
  (acc' (Var "mlkrs")))))
  (acc' (Var "mlkr")))))
  (acc' (Var "mlkns")))))
  (acc' (Var "mlkn")))))
  (acc' (Var "mlqrr")))))
  (acc' (Var "mlqrs")))))
  (acc' (Var "mlqr")))))
  (acc' (Var "mlqns")))))
  (acc' (Var "mlqn")))))
  (acc' (Var "mlckv")))))
  (acc' (Var "mlcq")).

(* Direct (DPIA-normal) form of the block: a sequence of whole-array
   assignments of the functional stage values. *)
Definition mlablock_direct {b s h dn hr dc dq : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))) : comm :=
  let c_q := MLACompress input w_dq in
  let c_kv := MLACompress input w_dkv in
  let q_n := MLAExpand c_q w_uq in
  let q_ns := SplitHeads q_n in
  let q_r := MLAExpand c_q w_qr in
  let q_rs := SplitHeads q_r in
  let q_rr := RoPEHeads base q_rs in
  let k_n := MLAExpand c_kv w_uk in
  let k_ns := SplitHeads k_n in
  let k_r := MLACompress input w_kr in
  let k_rs := SplitHeads k_r in
  let k_rr := RoPEHeads base k_rs in
  let v := MLAExpand c_kv w_uv in
  let vs := SplitHeads v in
  let q := HeadConcat q_ns q_rr in
  let k := HeadConcat k_ns k_rr in
  let att := AttnHeadsV q k vs in
  let merged := MergeHeads att in
  seq (A(acc' (Var "mlcq"), c_q))
  (seq (A(acc' (Var "mlckv"), c_kv))
  (seq (A(acc' (Var "mlqn"), q_n))
  (seq (A(acc' (Var "mlqns"), q_ns))
  (seq (A(acc' (Var "mlqr"), q_r))
  (seq (A(acc' (Var "mlqrs"), q_rs))
  (seq (A(acc' (Var "mlqrr"), q_rr))
  (seq (A(acc' (Var "mlkn"), k_n))
  (seq (A(acc' (Var "mlkns"), k_ns))
  (seq (A(acc' (Var "mlkr"), k_r))
  (seq (A(acc' (Var "mlkrs"), k_rs))
  (seq (A(acc' (Var "mlkrr"), k_rr))
  (seq (A(acc' (Var "mlv"), v))
  (seq (A(acc' (Var "mlvs"), vs))
  (seq (A(acc' (Var "mlq"), q))
  (seq (A(acc' (Var "mlk"), k))
  (seq (A(acc' (Var "mlatt"), att))
  (seq (A(acc' (Var "mlmg"), merged))
       (A(output, BMatMul2d merged wo))))))))))))))))))).

Lemma mlablock_comm_eq_direct : forall (b s h dn hr dc dq : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))),
  mlablock_comm input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo output =
  mlablock_direct input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo output.
Proof.
  intros.
  unfold mlablock_comm, mlablock_direct, new.
  cbv zeta beta.
  rewrite <- A_MLA_Compress.
  rewrite bind_read_replace.
  rewrite <- A_MLA_Compress.
  rewrite bind_read_replace.
  rewrite <- A_MLA_Expand.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_MLA_Expand.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_MLA_Expand.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_MLA_Compress.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_RoPEHeads.
  rewrite bind_read_replace.
  rewrite <- A_MLA_Expand.
  rewrite bind_read_replace.
  rewrite <- A_SplitHeads.
  rewrite bind_read_replace.
  rewrite <- A_HeadConcat.
  rewrite bind_read_replace.
  rewrite <- A_HeadConcat.
  rewrite bind_read_replace.
  rewrite <- A_AttnHeadsV.
  rewrite bind_read_replace.
  rewrite <- A_MergeHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional [MLABlock] value (the [ropemhablock_direct_bind] pattern). *)
Lemma mlablock_direct_bind : forall (b s h dn hr dc dq : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * dn} num))) -> comm),
  seq (mlablock_direct input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo
                       (acc' q))
      (bind_read (acc' q) k) =
  seq (mlablock_direct input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo
                       (acc' q))
      (k (MLABlock input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo)).
Proof.
  intros. fun_ext.
  unfold mlablock_direct, MLABlock, seq, bind_read, A.
  cbv beta zeta.
  rewrite read_exp_assign. reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MLABlock] (the [A_RopeMHABlock] shape). *)
Lemma A_MLABlock : forall (b s h dn hr dc dq : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rho : env) (p : path),
  in_acc p output ->
  mlablock_comm input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo output rho p =
  A(output, MLABlock input base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo) rho p.
Proof.
  intros. rewrite mlablock_comm_eq_direct.
  unfold mlablock_direct, MLABlock, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Pre-norm DeepSeek decoder block: MLA attention + MoE feed-forward           *)
(* -------------------------------------------------------------------------- *)

Definition DeepSeekBlock {b s h dn hr dc dq df E : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rms1_g rms2_g : exp (ary '{h * dn} num))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num))))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{h * dn} num))) :=
  let r1 := Add3d input (MLABlock (RMSNorm3d input rms1_g eps) base
                                  w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo) in
  Add3d r1 (MoEFFN3d (RMSNorm3d r1 rms2_g eps) wg w1s w3s w2s).

(* Imperative block: temporaries dsn1, dsmla, dsr1, dsn2, dsmoe.  The
   attention stage reuses [mlablock_comm] (whose internal temporaries
   mlcq..mlmg are distinct from all of the above); the MoE stage is a single
   assignment since [MoEFeedForward_comm] writes no temporaries. *)
Definition deepseekblock_comm {b s h dn hr dc dq df E : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rms1_g rms2_g : exp (ary '{h * dn} num))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num))))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))) : comm :=
  new (fun t1 => seq (RMSNorm3d_comm input rms1_g eps t1)
  (bind_read t1 (fun e1 =>
  new (fun t2 => seq (mlablock_comm e1 base w_dq w_uq w_qr
                                     w_dkv w_uk w_uv w_kr wo t2)
  (bind_read t2 (fun e2 =>
  new (fun t3 => seq (Add3d_comm input e2 t3)
  (bind_read t3 (fun e3 =>
  new (fun t4 => seq (RMSNorm3d_comm e3 rms2_g eps t4)
  (bind_read t4 (fun e4 =>
  new (fun t5 => seq (MoEFFN3d_comm e4 wg w1s w3s w2s t5)
  (bind_read t5 (fun e5 =>
    Add3d_comm e3 e5 output)))
  (acc' (Var "dsmoe")))))
  (acc' (Var "dsn2")))))
  (acc' (Var "dsr1")))))
  (acc' (Var "dsmla")))))
  (acc' (Var "dsn1")).

(* Direct (DPIA-normal) form of the block, left-associated so the final
   assignment is exposed at the top level (the [llamablock_direct] pattern). *)
Definition deepseekblock_direct {b s h dn hr dc dq df E : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rms1_g rms2_g : exp (ary '{h * dn} num))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num))))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))) : comm :=
  let n1 := RMSNorm3d input rms1_g eps in
  let mla := MLABlock n1 base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo in
  let r1 := Add3d input mla in
  let n2 := RMSNorm3d r1 rms2_g eps in
  let f := MoEFFN3d n2 wg w1s w3s w2s in
  seq (seq (seq (seq (seq
       (A(acc' (Var "dsn1"), n1))
       (mlablock_direct n1 base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo
                        (acc' (Var "dsmla"))))
       (A(acc' (Var "dsr1"), r1)))
       (A(acc' (Var "dsn2"), n2)))
       (A(acc' (Var "dsmoe"), f)))
       (A(output, DeepSeekBlock input rms1_g rms2_g base
                    w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo
                    wg w1s w3s w2s eps)).

Lemma deepseekblock_comm_eq_direct : forall (b s h dn hr dc dq df E : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rms1_g rms2_g : exp (ary '{h * dn} num))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num))))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))),
  deepseekblock_comm input rms1_g rms2_g base w_dq w_uq w_qr
                     w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps output =
  deepseekblock_direct input rms1_g rms2_g base w_dq w_uq w_qr
                       w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps output.
Proof.
  intros.
  unfold deepseekblock_comm, deepseekblock_direct, new.
  cbv zeta beta.
  rewrite <- A_RMSNorm3d.
  rewrite bind_read_replace.
  rewrite mlablock_comm_eq_direct.
  rewrite mlablock_direct_bind.
  rewrite <- A_Add3d.
  rewrite bind_read_replace.
  rewrite <- A_RMSNorm3d.
  rewrite bind_read_replace.
  rewrite <- A_MoEFFN3d.
  rewrite bind_read_replace.
  rewrite <- A_Add3d.
  reflexivity.
Qed.

(* Block-level DPIA correctness (the [A_LLaMABlock] shape). *)
Lemma A_DeepSeekBlock : forall (b s h dn hr dc dq df E : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rms1_g rms2_g : exp (ary '{h * dn} num))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num))))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rho : env) (p : path),
  in_acc p output ->
  deepseekblock_comm input rms1_g rms2_g base w_dq w_uq w_qr
                     w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps output rho p =
  A(output, DeepSeekBlock input rms1_g rms2_g base w_dq w_uq w_qr
              w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps) rho p.
Proof.
  intros. rewrite deepseekblock_comm_eq_direct.
  unfold deepseekblock_direct, DeepSeekBlock, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value (the [llamablock_direct_read] pattern). *)
Lemma deepseekblock_direct_read : forall (b s h dn hr dc dq df E : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (rms1_g rms2_g : exp (ary '{h * dn} num))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num))))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * dn} num))) -> comm) (c0 : comm),
  seq (deepseekblock_direct input rms1_g rms2_g base w_dq w_uq w_qr
                            w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps
                            (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (deepseekblock_direct input rms1_g rms2_g base w_dq w_uq w_qr
                            w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps
                            (acc' q))
      (seq (k (DeepSeekBlock input rms1_g rms2_g base w_dq w_uq w_qr
                 w_dkv w_uk w_uv w_kr wo wg w1s w3s w2s eps)) c0).
Proof.
  intros. unfold deepseekblock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* DeepSeekMini: embedding + 2 x DeepSeekBlock + final RMSNorm + head          *)
(* -------------------------------------------------------------------------- *)

Section DeepSeekMiniNet.

  (* All sizes symbolic: batch b, sequence s, heads h, per-head nope dim dn
     and rope half-dim hr (per-head key dim dn + hr*2), KV/Q latent dims
     dc/dq, expert FFN width df, experts E, vocab v.  Model dim = h*dn. *)
  Context (b s h dn hr dc dq df E v : nat).
  Context (eps base : exp num).

  (* Token indices (host-level index map, cf. [Gather2d]) and the token
     embedding table. *)
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{h * dn} num))).

  (* Layer-1 parameters. *)
  Context (l1_rms1_g l1_rms2_g : exp (ary '{h * dn} num))
          (l1_wdq : exp (ary '{h * dn} (ary '{dq} num)))
          (l1_wuq : exp (ary '{dq} (ary '{h * dn} num)))
          (l1_wqr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
          (l1_wdkv : exp (ary '{h * dn} (ary '{dc} num)))
          (l1_wuk l1_wuv : exp (ary '{dc} (ary '{h * dn} num)))
          (l1_wkr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
          (l1_wo : exp (ary '{h * dn} (ary '{h * dn} num)))
          (l1_wg : exp (ary '{E} (ary '{h * dn} num)))
          (l1_w1s l1_w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
          (l1_w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num)))).

  (* Layer-2 parameters. *)
  Context (l2_rms1_g l2_rms2_g : exp (ary '{h * dn} num))
          (l2_wdq : exp (ary '{h * dn} (ary '{dq} num)))
          (l2_wuq : exp (ary '{dq} (ary '{h * dn} num)))
          (l2_wqr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
          (l2_wdkv : exp (ary '{h * dn} (ary '{dc} num)))
          (l2_wuk l2_wuv : exp (ary '{dc} (ary '{h * dn} num)))
          (l2_wkr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
          (l2_wo : exp (ary '{h * dn} (ary '{h * dn} num)))
          (l2_wg : exp (ary '{E} (ary '{h * dn} num)))
          (l2_w1s l2_w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
          (l2_w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num)))).

  (* Final RMSNorm and the output head (logits over the vocabulary). *)
  Context (rmsf_g : exp (ary '{h * dn} num))
          (whead : exp (ary '{h * dn} (ary '{v} num))).

  (* Batched embedding: the same token sequence in every batch element. *)
  Definition DSEmbed : exp (ary '{b} (ary '{s} (ary '{h * dn} num))) :=
    mkvSeq (fun bb : fin b => Gather2d toks tok_table).

  Definition DSEmbed_comm
    (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))) : comm :=
    mkvSeql (fun bb ob => Gather2d_comm toks tok_table ob) output.

  Lemma A_DSEmbed : forall
    (output : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))),
    A(output, DSEmbed) = DSEmbed_comm output.
  Proof.
    intros. unfold DSEmbed, DSEmbed_comm.
    rewrite AmkvSeq.
    apply seqfor_extensionality. intro bb.
    rewrite A_Gather2d.
    reflexivity.
  Qed.

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  Definition ds_x0 := DSEmbed.
  Definition ds_x1 := DeepSeekBlock ds_x0 l1_rms1_g l1_rms2_g base
                        l1_wdq l1_wuq l1_wqr l1_wdkv l1_wuk l1_wuv l1_wkr
                        l1_wo l1_wg l1_w1s l1_w3s l1_w2s eps.
  Definition ds_x2 := DeepSeekBlock ds_x1 l2_rms1_g l2_rms2_g base
                        l2_wdq l2_wuq l2_wqr l2_wdkv l2_wuk l2_wuv l2_wkr
                        l2_wo l2_wg l2_w1s l2_w3s l2_w2s eps.
  Definition ds_x3 := RMSNorm3d ds_x2 rmsf_g eps.
  Definition ds_x4 := BMatMul2d ds_x3 whead.

  Lemma ds_x0_body : ds_x0 = DSEmbed.
  Proof. reflexivity. Qed.
  Lemma ds_x1_body : ds_x1 = DeepSeekBlock ds_x0 l1_rms1_g l1_rms2_g base
                        l1_wdq l1_wuq l1_wqr l1_wdkv l1_wuk l1_wuv l1_wkr
                        l1_wo l1_wg l1_w1s l1_w3s l1_w2s eps.
  Proof. reflexivity. Qed.
  Lemma ds_x2_body : ds_x2 = DeepSeekBlock ds_x1 l2_rms1_g l2_rms2_g base
                        l2_wdq l2_wuq l2_wqr l2_wdkv l2_wuk l2_wuv l2_wkr
                        l2_wo l2_wg l2_w1s l2_w3s l2_w2s eps.
  Proof. reflexivity. Qed.
  Lemma ds_x3_body : ds_x3 = RMSNorm3d ds_x2 rmsf_g eps.
  Proof. reflexivity. Qed.
  Lemma ds_x4_body : ds_x4 = BMatMul2d ds_x3 whead.
  Proof. reflexivity. Qed.

  Opaque ds_x0 ds_x1 ds_x2 ds_x3 ds_x4.

  Definition DeepSeekMini : exp (ary '{b} (ary '{s} (ary '{v} num))) := ds_x4.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition deepseekmini_comm
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
new (fun t1 => seq (DSEmbed_comm t1)
(new (fun t2 => seq (bind_read t1 (fun e1 =>
      deepseekblock_comm e1 l1_rms1_g l1_rms2_g base
                         l1_wdq l1_wuq l1_wqr l1_wdkv l1_wuk l1_wuv l1_wkr
                         l1_wo l1_wg l1_w1s l1_w3s l1_w2s eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 =>
      deepseekblock_comm e2 l2_rms1_g l2_rms2_g base
                         l2_wdq l2_wuq l2_wqr l2_wdkv l2_wuk l2_wuv l2_wkr
                         l2_wo l2_wg l2_w1s l2_w3s l2_w2s eps t3))
(new (fun t4 => seq (bind_read t3 (fun e3 =>
      RMSNorm3d_comm e3 rmsf_g eps t4))
     (bind_read t4 (fun e4 => BMatMul2d_comm e4 whead output))
) (acc' (Var "ds4")))
) (acc' (Var "ds3")))
) (acc' (Var "ds2")))
) (acc' (Var "ds1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition deepseekmini_direct
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
    seq (A(acc' (Var "ds1"), ds_x0))
    (seq (deepseekblock_direct ds_x0 l1_rms1_g l1_rms2_g base
                               l1_wdq l1_wuq l1_wqr l1_wdkv l1_wuk l1_wuv
                               l1_wkr l1_wo l1_wg l1_w1s l1_w3s l1_w2s eps
                               (acc' (Var "ds2")))
    (seq (deepseekblock_direct ds_x1 l2_rms1_g l2_rms2_g base
                               l2_wdq l2_wuq l2_wqr l2_wdkv l2_wuk l2_wuv
                               l2_wkr l2_wo l2_wg l2_w1s l2_w3s l2_w2s eps
                               (acc' (Var "ds3")))
    (seq (A(acc' (Var "ds4"), ds_x3))
         (A(output, ds_x4))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition ds1_acc : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))
    := acc' (Var "ds1").
  Definition ds2_acc : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))
    := acc' (Var "ds2").
  Definition ds3_acc : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))
    := acc' (Var "ds3").
  Definition ds4_acc : acc (ary '{b} (ary '{s} (ary '{h * dn} num)))
    := acc' (Var "ds4").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries dsn1..dsmoe and the MLA temporaries mlcq..mlmg are shared
     between the two layers and are required to be fresh at every type (the
     [llamamini_fresh] pattern). *)
  Definition deepseekmini_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    StructUndefined ds1_acc rho /\
    StructUndefined ds2_acc rho /\
    StructUndefined ds3_acc rho /\
    StructUndefined ds4_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "dsn1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "dsmla") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "dsr1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "dsn2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "dsmoe") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlcq") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlckv") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlqn") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlqns") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlqr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlqrs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlqrr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlkn") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlkns") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlkr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlkrs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlkrr") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlv") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlvs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlq") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlk") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlatt") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mlmg") : acc d0) rho) /\
    (forall p, in_acc p output -> ~ in_acc p ds1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p ds2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p ds3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p ds4_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dsn1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dsmla") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dsr1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dsn2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dsmoe") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlcq") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlckv") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlqn") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlqns") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlqr") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlqrs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlqrr") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlkn") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlkns") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlkr") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlkrs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlkrr") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlv") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlvs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlq") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlk") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlatt") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mlmg") : acc d0)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma deepseekmini_comm_eq_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num)))),
    deepseekmini_comm output = deepseekmini_direct output.
  Proof.
    intros.
    unfold deepseekmini_comm, deepseekmini_direct, new.
    cbv beta.
    rewrite <- A_DSEmbed.
    rewrite <- ds_x0_body.
    rewrite bind_read_replace_seq.
    rewrite deepseekblock_comm_eq_direct.
    rewrite deepseekblock_direct_read.
    rewrite <- ds_x1_body.
    rewrite deepseekblock_comm_eq_direct.
    rewrite deepseekblock_direct_read.
    rewrite <- ds_x2_body.
    rewrite <- A_RMSNorm3d.
    rewrite <- ds_x3_body.
    rewrite bind_read_replace.
    rewrite <- A_BMatMul2d.
    rewrite <- ds_x4_body.
    reflexivity.
  Qed.

  Lemma A_DeepSeekMini_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    deepseekmini_fresh output rho ->
    deepseekmini_direct output rho p = A(output, DeepSeekMini) rho p.
  Proof.
    intros.
    unfold deepseekmini_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold DeepSeekMini. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of the mini DeepSeek: under freshness of
     the temporary buffers, the imperative network observed at an output
     path computes the functional [DeepSeekMini]. *)
  Theorem A_DeepSeekMini :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    deepseekmini_fresh output rho ->
    deepseekmini_comm output rho p = A(output, DeepSeekMini) rho p.
  Proof.
    intros. rewrite deepseekmini_comm_eq_direct.
    apply A_DeepSeekMini_direct; assumption.
  Qed.

End DeepSeekMiniNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: b = 1, s = 4, h = 2, dn = 2, hr = 1 (model dim 4,        *)
(* per-head key dim 4), dc = dq = 2, df = 4, E = 2 experts, vocab v = 4        *)
(* -------------------------------------------------------------------------- *)

Section Small_1_4_2_2_1.

  Context (eps4 base4 : exp num)
          (toks4 : fin 4 -> fin 4)
          (tok_tab4 : exp (ary '{4} (ary '{4} num)))
          (r1_1 r2_1 : exp (ary '{4} num))
          (wdq1 : exp (ary '{4} (ary '{2} num)))
          (wuq1 : exp (ary '{2} (ary '{4} num)))
          (wqr1 : exp (ary '{2} (ary '{4} num)))
          (wdkv1 : exp (ary '{4} (ary '{2} num)))
          (wuk1 wuv1 : exp (ary '{2} (ary '{4} num)))
          (wkr1 wo1 : exp (ary '{4} (ary '{4} num)))
          (wg1 : exp (ary '{2} (ary '{4} num)))
          (w1s1 w3s1 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (w2s1 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (r1_2 r2_2 : exp (ary '{4} num))
          (wdq2 : exp (ary '{4} (ary '{2} num)))
          (wuq2 : exp (ary '{2} (ary '{4} num)))
          (wqr2 : exp (ary '{2} (ary '{4} num)))
          (wdkv2 : exp (ary '{4} (ary '{2} num)))
          (wuk2 wuv2 : exp (ary '{2} (ary '{4} num)))
          (wkr2 wo2 : exp (ary '{4} (ary '{4} num)))
          (wg2 : exp (ary '{2} (ary '{4} num)))
          (w1s2 w3s2 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (w2s2 : exp (ary '{2} (ary '{4} (ary '{4} num))))
          (rf : exp (ary '{4} num))
          (wh : exp (ary '{4} (ary '{4} num)))
          (out4 : acc (ary '{1} (ary '{4} (ary '{4} num)))).

  (* Shape check: the symbolic network and its command instantiate at the
     small size (h*dn = 4, h*(hr*2) = 4, w2s : (E, d, df) = (2, 4, 4)). *)
  Definition DeepSeekMini_1_4_2_2_1 : exp (ary '{1} (ary '{4} (ary '{4} num))) :=
    @DeepSeekMini 1 4 2 2 1 2 2 4 2 4
      eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wdq1 wuq1 wqr1 wdkv1 wuk1 wuv1 wkr1 wo1 wg1 w1s1 w3s1 w2s1
      r1_2 r2_2 wdq2 wuq2 wqr2 wdkv2 wuk2 wuv2 wkr2 wo2 wg2 w1s2 w3s2 w2s2
      rf wh.

  Definition deepseekmini_comm_1_4_2_2_1 : comm :=
    @deepseekmini_comm 1 4 2 2 1 2 2 4 2 4
      eps4 base4 toks4 tok_tab4
      r1_1 r2_1 wdq1 wuq1 wqr1 wdkv1 wuk1 wuv1 wkr1 wo1 wg1 w1s1 w3s1 w2s1
      r1_2 r2_2 wdq2 wuq2 wqr2 wdkv2 wuk2 wuv2 wkr2 wo2 wg2 w1s2 w3s2 w2s2
      rf wh out4.

End Small_1_4_2_2_1.

(* [vm_compute]/conversion spot checks of the computable (structural) parts
   of the pipeline. *)

(* HeadConcat: nope vector [5, 6], rope vector [7, 8] (single batch, head,
   position). *)
Definition HC_U : exp (ary '{1} (ary '{1} (ary '{1} (ary '{2} num)))) :=
  mkvSeq (fun bb : fin 1 => mkvSeq (fun hh : fin 1 => mkvSeq (fun ss : fin 1 =>
    mkvSeq (fun x : fin 2 => (INR (5 + fin2nat x)%nat : exp num))))).

Definition HC_W : exp (ary '{1} (ary '{1} (ary '{1} (ary '{2} num)))) :=
  mkvSeq (fun bb : fin 1 => mkvSeq (fun hh : fin 1 => mkvSeq (fun ss : fin 1 =>
    mkvSeq (fun x : fin 2 => (INR (7 + fin2nat x)%nat : exp num))))).

(* Low part: concatenated index 0 reads the nope vector's 5.  (The boundary
   test [Nat.ltb_spec0] carries opaque proof lemmas, so the check is proved
   by [destruct] on the spec0 instead of a plain [vm_compute].) *)
Definition hc_i0 : fin (2 + 2) := @nat2fin (2 + 2) 0 (ltac:(lia)).
Definition hc_i3 : fin (2 + 2) := @nat2fin (2 + 2) 3 (ltac:(lia)).

Example check_headconcat_lo :
  idx (idx (idx (idx (HeadConcat (dn:=2) (dr:=2) HC_U HC_W)
                    ll_i0_1) ll_i0_1) ll_i0_1) hc_i0 = INR 5.
Proof.
  unfold HeadConcat. rewrite !idx_mkvSeq by lia.
  unfold HeadConcatCell.
  destruct (Nat.ltb_spec0 (fin2nat hc_i0) 2) as [Hlt|Hge].
  - unfold HC_U. rewrite !idx_mkvSeq by lia.
    rewrite fin2nat_nat2fin.
    assert (fin2nat hc_i0 = 0) as H0 by (vm_compute; reflexivity).
    rewrite H0. vm_compute. reflexivity.
  - exfalso. apply Hge.
    assert (fin2nat hc_i0 = 0) as H0 by (vm_compute; reflexivity).
    rewrite H0. lia.
Qed.

(* High part: concatenated index 3 reads the rope vector's entry 3-2 = 1,
   i.e. 8. *)
Example check_headconcat_hi :
  idx (idx (idx (idx (HeadConcat (dn:=2) (dr:=2) HC_U HC_W)
                    ll_i0_1) ll_i0_1) ll_i0_1) hc_i3 = INR 8.
Proof.
  unfold HeadConcat. rewrite !idx_mkvSeq by lia.
  unfold HeadConcatCell.
  destruct (Nat.ltb_spec0 (fin2nat hc_i3) 2) as [Hlt|Hge].
  - assert (fin2nat hc_i3 = 3) as H0 by (vm_compute; reflexivity). lia.
  - unfold HC_W. rewrite !idx_mkvSeq by lia.
    rewrite fin2nat_nat2fin.
    assert (fin2nat hc_i3 = 3) as H0 by (vm_compute; reflexivity).
    rewrite H0. vm_compute. reflexivity.
Qed.

(* Compress-then-expand is the two-Linear chain W_U (W_D x). *)
Example check_mla_compress_expand : forall (b s dm dc do2 : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (wd : exp (ary '{dm} (ary '{dc} num)))
  (wu : exp (ary '{dc} (ary '{do2} num))),
  MLAExpand (MLACompress x wd) wu = BMatMul2d (BMatMul2d x wd) wu.
Proof. reflexivity. Qed.

(* Per-token MoE: position (bb, ss) runs the MoE feed-forward on that token
   vector. *)
Example check_moeffn3d_entry : forall (E d df : nat)
  (Wg : exp (ary '{E} (ary '{d} num)))
  (W1s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W3s : exp (ary '{E} (ary '{df} (ary '{d} num))))
  (W2s : exp (ary '{E} (ary '{d} (ary '{df} num))))
  (input : exp (ary '{1} (ary '{2} (ary '{d} num))))
  (ss : fin 2),
  idx (idx (MoEFFN3d (b:=1) (s:=2) input Wg W1s W3s W2s) ll_i0_1) ss
  = MoEFeedForward Wg W1s W3s W2s (idx (idx input ll_i0_1) ss).
Proof.
  intros. unfold MoEFFN3d. rewrite !idx_mkvSeq by lia. reflexivity.
Qed.

(* MLA block structure: two low-rank compressions, decoupled (partial) RoPE
   on the rope part only, per-head concat, value-dim-polymorphic attention,
   merge + output projection. *)
Example check_mlablock_structure : forall (b s h dn hr dc dq : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (base : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num))),
  MLABlock x base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo =
  BMatMul2d (MergeHeads (AttnHeadsV
    (HeadConcat (SplitHeads (BMatMul2d (BMatMul2d x w_dq) w_uq))
                (RoPEHeads base (SplitHeads (BMatMul2d (BMatMul2d x w_dq) w_qr))))
    (HeadConcat (SplitHeads (BMatMul2d (BMatMul2d x w_dkv) w_uk))
                (RoPEHeads base (SplitHeads (BMatMul2d x w_kr))))
    (SplitHeads (BMatMul2d (BMatMul2d x w_dkv) w_uv)))) wo.
Proof. reflexivity. Qed.

(* DeepSeek block structure: pre-norm, RMSNorm -> MLA -> residual ->
   RMSNorm -> MoE FFN -> residual. *)
Example check_deepseekblock_structure : forall (b s h dn hr dc dq df E : nat)
  (x : exp (ary '{b} (ary '{s} (ary '{h * dn} num))))
  (g1 g2 : exp (ary '{h * dn} num))
  (base eps : exp num)
  (w_dq : exp (ary '{h * dn} (ary '{dq} num)))
  (w_uq : exp (ary '{dq} (ary '{h * dn} num)))
  (w_qr : exp (ary '{dq} (ary '{h * (hr * 2)} num)))
  (w_dkv : exp (ary '{h * dn} (ary '{dc} num)))
  (w_uk : exp (ary '{dc} (ary '{h * dn} num)))
  (w_uv : exp (ary '{dc} (ary '{h * dn} num)))
  (w_kr : exp (ary '{h * dn} (ary '{h * (hr * 2)} num)))
  (wo : exp (ary '{h * dn} (ary '{h * dn} num)))
  (wg : exp (ary '{E} (ary '{h * dn} num)))
  (w1s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w3s : exp (ary '{E} (ary '{df} (ary '{h * dn} num))))
  (w2s : exp (ary '{E} (ary '{h * dn} (ary '{df} num)))),
  DeepSeekBlock x g1 g2 base w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo
                wg w1s w3s w2s eps =
  Add3d (Add3d x (MLABlock (RMSNorm3d x g1 eps) base
                           w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo))
        (MoEFFN3d (RMSNorm3d (Add3d x (MLABlock (RMSNorm3d x g1 eps) base
                              w_dq w_uq w_qr w_dkv w_uk w_uv w_kr wo)) g2 eps)
                  wg w1s w3s w2s).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_HeadConcat.
Print Assumptions A_Attention_cellV.
Print Assumptions A_AttnHeadsV.
Print Assumptions A_MLA_Compress.
Print Assumptions A_MLA_Expand.
Print Assumptions A_MoEFFN3d.
Print Assumptions mlablock_comm_eq_direct.
Print Assumptions mlablock_direct_bind.
Print Assumptions A_MLABlock.
Print Assumptions deepseekblock_comm_eq_direct.
Print Assumptions A_DeepSeekBlock.
Print Assumptions deepseekblock_direct_read.
Print Assumptions deepseekmini_comm_eq_direct.
Print Assumptions A_DeepSeekMini.
