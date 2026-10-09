(* DPIA-style Leibniz equivalence proofs for a full pre-norm Transformer
   block and a mini GPT-style decoder-only network assembled from it
   (milestones T3/T4 of the Transformer extension, cf.
   doc/Transformer扩展开发规划_20260829.md) in the route-A R-based expression
   model.

   Delivered here (all closed with [Qed], no Admitted/Axiom):

   - [GELU3d]: the (b, s, d) instance of the tanh-approximation GELU of
     Ionia.Ops_Transformer (which carries the 4d form), with the same
     elementwise proof template.

   - [TransformerBlock]: the pre-norm block
        r1 = x + MHA(LN1(x))          (multi-head causal self-attention of
        x2 = r1 + FFN(LN2(r1))         Ionia.Attention_DPIA)
     with FFN = Linear -> GELU -> Linear (right-multiplied projection
     matrices, bias-free; biases would be pointwise [Add] stages and add
     nothing to the argument).  The imperative block [transformerblock_comm]
     stages the computation through freshly allocated buffers with
     [new]/[bind_read]; the MHA stage reuses [mhablock_comm] of milestone T2
     as a sub-command.  [transformerblock_comm_eq_direct] collapses the block
     to the buffer-free direct form; the read of the MHA output buffer is
     collapsed by [mhablock_direct_bind], the direct analogue of the
     bind_read lemmas.  [A_TransformerBlock] observes the block at an output
     path (the [A_MHABlock] shape); [transformerblock_direct_read] lets the
     network-level proof advance past a folded block without unfolding it
     (the [bottleneck_id_direct_read] pattern of Ionia.ResNet50_DPIA).

   - [MiniTransformer]: a mini GPT-style decoder-only network, all sizes
     symbolic (batch b, sequence s, heads h, head dim d, FFN width df,
     vocab v):
        token embedding (Gather2d table lookup) + positional encoding
        -> TransformerBlock (layer 1) -> TransformerBlock (layer 2)
        -> final LayerNorm -> output head Linear (logits over vocab).
     Positional encoding is simplified to a learned position table
     broadcast over the batch (a sinusoidal table would need sin/cos,
     which add nothing to the Leibniz argument; the table is an arbitrary
     parameter either way).  The number of layers is fixed at N = 2 with
     per-layer parameters, exactly as ResNet50 enumerates its 16 blocks;
     deeper stacks are the same enumeration.  Layer values are folded into
     [Opaque] constants [mt_x0..mt_x4] (the ResNet50 wrapper pattern), so
     the network-level proof never inlines one stage into the next.
     [A_MiniTransformer] is the end-to-end theorem: under freshness of the
     temporary buffers, the imperative network observed at an output path
     equals the functional network.

   - A concrete instantiation at b = 1, s = 8, h = 2, d = 16 (model
     dimension 32), df = 32, v = 8, with [vm_compute]/conversion spot
     checks of the computable parts (embedding gather, residual add
     structure, GELU entry structure). *)

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
(* T1 operators: [LayerNorm3d], [gelu], [Gather2d]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [MHABlock], [mhablock_comm], [mhablock_direct], [BMatMul2d]. *)
Require Import Ionia.Attention_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* GELU on (b, s, d) tensors                                                   *)
(* -------------------------------------------------------------------------- *)

Definition GELU3d {b s d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  : exp (ary '{b} (ary '{s} (ary '{d} num))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun ss : fin s => mkvSeq (fun j : fin d =>
    gelu (idx (idx (idx input bb) ss) j)))).

Definition GELU3d_comm {b s d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))) : comm :=
  seqfor (fun bb : fin b => seqfor (fun ss : fin s => seqfor (fun j : fin d =>
    idxAcc (idxAcc (idxAcc output bb) ss) j |:=
      gelu (idx (idx (idx input bb) ss) j)))).

Lemma A_GELU3d : forall (b s d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{d} num))))
  (output : acc (ary '{b} (ary '{s} (ary '{d} num)))),
  A(output, GELU3d input) = GELU3d_comm input output.
Proof.
  intros. unfold GELU3d, GELU3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ss.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Position-wise feed-forward network: Linear -> GELU -> Linear               *)
(* (right-multiplied projection matrices, bias-free)                           *)
(* -------------------------------------------------------------------------- *)

Definition FFN {b s dm df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{dm} num))))
  (w1 : exp (ary '{dm} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{dm} num)))
  : exp (ary '{b} (ary '{s} (ary '{dm} num))) :=
  BMatMul2d (GELU3d (BMatMul2d input w1)) w2.

(* -------------------------------------------------------------------------- *)
(* Pre-norm Transformer block                                                  *)
(* -------------------------------------------------------------------------- *)

Definition TransformerBlock {b s h d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  let r1 := Add3d input (MHABlock (LayerNorm3d input ln1_g ln1_b eps)
                                  wq wk wv wo) in
  Add3d r1 (FFN (LayerNorm3d r1 ln2_g ln2_b eps) w1 w2).

(* Imperative block: temporaries bln1, bmha, br1, bln2, btf1, btg, btf2.
   The MHA stage reuses [mhablock_comm] (whose internal temporaries
   mtq..mtmg are distinct from all of the above). *)
Definition transformerblock_comm {b s h d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  new (fun t1 => seq (LayerNorm3d_comm input ln1_g ln1_b eps t1)
  (bind_read t1 (fun e1 =>
  new (fun t2 => seq (mhablock_comm e1 wq wk wv wo t2)
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
  (acc' (Var "btf2")))))
  (acc' (Var "btg")))))
  (acc' (Var "btf1")))))
  (acc' (Var "bln2")))))
  (acc' (Var "br1")))))
  (acc' (Var "bmha")))))
  (acc' (Var "bln1")).

(* Direct (DPIA-normal) form of the block: the MHA stage keeps its own
   direct form as a folded sub-command; the surrounding stages are plain
   whole-array assignments, left-associated so the final assignment is
   exposed at the top level (the [bottleneck_id_direct] pattern). *)
Definition transformerblock_direct {b s h d df : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  let ln1 := LayerNorm3d input ln1_g ln1_b eps in
  let mha := MHABlock ln1 wq wk wv wo in
  let r1 := Add3d input mha in
  let ln2 := LayerNorm3d r1 ln2_g ln2_b eps in
  let f1 := BMatMul2d ln2 w1 in
  let gg := GELU3d f1 in
  let f2 := BMatMul2d gg w2 in
  seq (seq (seq (seq (seq (seq (seq
       (A(acc' (Var "bln1"), ln1))
       (mhablock_direct ln1 wq wk wv wo (acc' (Var "bmha"))))
       (A(acc' (Var "br1"), r1)))
       (A(acc' (Var "bln2"), ln2)))
       (A(acc' (Var "btf1"), f1)))
       (A(acc' (Var "btg"), gg)))
       (A(acc' (Var "btf2"), f2)))
       (A(output, TransformerBlock input ln1_g ln1_b ln2_g ln2_b
                                   wq wk wv wo w1 w2 eps)).

(* Reading the MHA output buffer after the (folded) MHA direct form yields
   the functional [MHABlock] value.  [mhablock_direct] is right-associated,
   so [bind_read_replace_seq_r] does not apply syntactically; the proof
   instead unfolds to the underlying environment functions, where the
   association is irrelevant ([seq] is plain composition). *)
Lemma mhablock_direct_bind : forall (b s h d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm),
  seq (mhablock_direct input wq wk wv wo (acc' q)) (bind_read (acc' q) k) =
  seq (mhablock_direct input wq wk wv wo (acc' q))
      (k (MHABlock input wq wk wv wo)).
Proof.
  intros. fun_ext.
  unfold mhablock_direct, MHABlock, seq, bind_read, A.
  cbv beta zeta.
  rewrite read_exp_assign. reflexivity.
Qed.

Lemma transformerblock_comm_eq_direct : forall (b s h d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  transformerblock_comm input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output =
  transformerblock_direct input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output.
Proof.
  intros.
  unfold transformerblock_comm, transformerblock_direct, new.
  cbv zeta beta.
  rewrite <- A_LayerNorm3d.
  rewrite bind_read_replace.
  rewrite mhablock_comm_eq_direct.
  rewrite mhablock_direct_bind.
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

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [TransformerBlock] (the [A_MHABlock] shape;
   the final assignment is env-independent, so no freshness premise on the
   temporaries is needed). *)
Lemma A_TransformerBlock : forall (b s h d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  transformerblock_comm input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps output rho p =
  A(output, TransformerBlock input ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 eps) rho p.
Proof.
  intros. rewrite transformerblock_comm_eq_direct.
  unfold transformerblock_direct, TransformerBlock, FFN, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value; the network-level proof advances past a
   block without ever unfolding its direct form. *)
Lemma transformerblock_direct_read : forall (b s h d df : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (ln1_g ln1_b ln2_g ln2_b : exp (ary '{h * d} num))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (w1 : exp (ary '{h * d} (ary '{df} num)))
  (w2 : exp (ary '{df} (ary '{h * d} num)))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{b} (ary '{s} (ary '{h * d} num))) -> comm) (c0 : comm),
  seq (transformerblock_direct input ln1_g ln1_b ln2_g ln2_b
                               wq wk wv wo w1 w2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (transformerblock_direct input ln1_g ln1_b ln2_g ln2_b
                               wq wk wv wo w1 w2 eps (acc' q))
      (seq (k (TransformerBlock input ln1_g ln1_b ln2_g ln2_b
                                wq wk wv wo w1 w2 eps)) c0).
Proof.
  intros. unfold transformerblock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MiniTransformer: embedding + 2 x TransformerBlock + final LN + head        *)
(* -------------------------------------------------------------------------- *)

Section MiniTransformerNet.

  (* All sizes symbolic: batch b, sequence s, heads h, head dimension d
     (model dimension h*d), FFN width df, vocabulary v. *)
  Context (b s h d df v : nat).
  Context (eps : exp num).

  (* Token indices (host-level index map, cf. [Gather2d]) and the token /
     position embedding tables. *)
  Context (toks : fin s -> fin v).
  Context (tok_table : exp (ary '{v} (ary '{h * d} num)))
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

  (* Final LayerNorm and the output head (logits over the vocabulary). *)
  Context (lnf_g lnf_b : exp (ary '{h * d} num))
          (whead : exp (ary '{h * d} (ary '{v} num))).

  (* Batched embedding: the same token sequence / position table in every
     batch element (the batch=1 use case; the tables are arbitrary
     parameters). *)
  Definition BEmbed : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => Gather2d toks tok_table).
  Definition BPos : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
    mkvSeq (fun bb : fin b => pos_table).

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  Definition mt_x0 := Add3d BEmbed BPos.
  Definition mt_x1 := TransformerBlock mt_x0 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                                      l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps.
  Definition mt_x2 := TransformerBlock mt_x1 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                                      l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps.
  Definition mt_x3 := LayerNorm3d mt_x2 lnf_g lnf_b eps.
  Definition mt_x4 := BMatMul2d mt_x3 whead.

  Lemma mt_x0_body : mt_x0 = Add3d BEmbed BPos.
  Proof. reflexivity. Qed.
  Lemma mt_x1_body : mt_x1 = TransformerBlock mt_x0 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                                      l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps.
  Proof. reflexivity. Qed.
  Lemma mt_x2_body : mt_x2 = TransformerBlock mt_x1 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                                      l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps.
  Proof. reflexivity. Qed.
  Lemma mt_x3_body : mt_x3 = LayerNorm3d mt_x2 lnf_g lnf_b eps.
  Proof. reflexivity. Qed.
  Lemma mt_x4_body : mt_x4 = BMatMul2d mt_x3 whead.
  Proof. reflexivity. Qed.

  Opaque mt_x0 mt_x1 mt_x2 mt_x3 mt_x4.

  Definition MiniTransformer : exp (ary '{b} (ary '{s} (ary '{v} num))) := mt_x4.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition minitransformer_comm
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
new (fun t1 => seq (Add3d_comm BEmbed BPos t1)
(new (fun t2 => seq (bind_read t1 (fun e1 =>
      transformerblock_comm e1 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                            l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 =>
      transformerblock_comm e2 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                            l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps t3))
(new (fun t4 => seq (bind_read t3 (fun e3 =>
      LayerNorm3d_comm e3 lnf_g lnf_b eps t4))
     (bind_read t4 (fun e4 => BMatMul2d_comm e4 whead output))
) (acc' (Var "l4")))
) (acc' (Var "l3")))
) (acc' (Var "l2")))
) (acc' (Var "l1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition minitransformer_direct
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) : comm :=
    seq (A(acc' (Var "l1"), mt_x0))
    (seq (transformerblock_direct mt_x0 l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                                  l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 eps
                                  (acc' (Var "l2")))
    (seq (transformerblock_direct mt_x1 l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                                  l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 eps
                                  (acc' (Var "l3")))
    (seq (A(acc' (Var "l4"), mt_x3))
         (A(output, mt_x4))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition l1_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l1").
  Definition l2_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l2").
  Definition l3_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l3").
  Definition l4_acc : acc (ary '{b} (ary '{s} (ary '{h * d} num)))
    := acc' (Var "l4").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries bln1..btf2 and the MHA temporaries mtq..mtmg are shared
     between the two layers and are required to be fresh at every type
     (the [resnet50_fresh] pattern). *)
  Definition minitransformer_fresh
    (output : acc (ary '{b} (ary '{s} (ary '{v} num)))) (rho : env) : Prop :=
    StructUndefined l1_acc rho /\
    StructUndefined l2_acc rho /\
    StructUndefined l3_acc rho /\
    StructUndefined l4_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "bln1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bmha") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "br1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "bln2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "btf1") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "btg") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "btf2") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtq") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtqs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtk") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtks") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtv") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtvs") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtatt") : acc d0) rho) /\
    (forall d0 : data, StructUndefined (acc' (Var "mtmg") : acc d0) rho) /\
    (forall p, in_acc p output -> ~ in_acc p l1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p l4_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bln1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bmha") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "br1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bln2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "btf1") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "btg") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "btf2") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtq") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtqs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtk") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtks") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtv") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtvs") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtatt") : acc d0)) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "mtmg") : acc d0)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma minitransformer_comm_eq_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num)))),
    minitransformer_comm output = minitransformer_direct output.
  Proof.
    intros.
    unfold minitransformer_comm, minitransformer_direct, new.
    cbv beta.
    rewrite <- A_Add3d.
    rewrite <- mt_x0_body.
    rewrite bind_read_replace_seq.
    rewrite transformerblock_comm_eq_direct.
    rewrite transformerblock_direct_read.
    rewrite <- mt_x1_body.
    rewrite transformerblock_comm_eq_direct.
    rewrite transformerblock_direct_read.
    rewrite <- mt_x2_body.
    rewrite <- A_LayerNorm3d.
    rewrite <- mt_x3_body.
    rewrite bind_read_replace.
    rewrite <- A_BMatMul2d.
    rewrite <- mt_x4_body.
    reflexivity.
  Qed.

  Lemma A_MiniTransformer_direct :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    minitransformer_fresh output rho ->
    minitransformer_direct output rho p = A(output, MiniTransformer) rho p.
  Proof.
    intros.
    unfold minitransformer_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold MiniTransformer. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of the mini Transformer: under freshness
     of the temporary buffers, the imperative network observed at an output
     path computes the functional [MiniTransformer]. *)
  Theorem A_MiniTransformer :
    forall (output : acc (ary '{b} (ary '{s} (ary '{v} num))))
      (rho : env) (p : path),
    in_acc p output ->
    minitransformer_fresh output rho ->
    minitransformer_comm output rho p = A(output, MiniTransformer) rho p.
  Proof.
    intros. rewrite minitransformer_comm_eq_direct.
    apply A_MiniTransformer_direct; assumption.
  Qed.

End MiniTransformerNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: b = 1, s = 8, h = 2, d = 16 (model dim 32), df = 32,   *)
(* vocab v = 8                                                                *)
(* -------------------------------------------------------------------------- *)

Section Small_1_8_2_16.

  Context (eps8 : exp num)
          (toks8 : fin 8 -> fin 8)
          (tok_tab8 : exp (ary '{8} (ary '{32} num)))
          (pos_tab8 : exp (ary '{8} (ary '{32} num)))
          (g1_1 b1_1 g2_1 b2_1 : exp (ary '{32} num))
          (wq1 wk1 wv1 wo1 : exp (ary '{32} (ary '{32} num)))
          (w1_1 : exp (ary '{32} (ary '{32} num)))
          (w2_1 : exp (ary '{32} (ary '{32} num)))
          (g1_2 b1_2 g2_2 b2_2 : exp (ary '{32} num))
          (wq2 wk2 wv2 wo2 : exp (ary '{32} (ary '{32} num)))
          (w1_2 : exp (ary '{32} (ary '{32} num)))
          (w2_2 : exp (ary '{32} (ary '{32} num)))
          (gf bf : exp (ary '{32} num))
          (wh : exp (ary '{32} (ary '{8} num)))
          (out8 : acc (ary '{1} (ary '{8} (ary '{8} num)))).

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition MiniTransformer_1_8_2_16 : exp (ary '{1} (ary '{8} (ary '{8} num))) :=
    @MiniTransformer 1 8 2 16 32 8
      eps8 toks8 tok_tab8 pos_tab8
      g1_1 b1_1 g2_1 b2_1 wq1 wk1 wv1 wo1 w1_1 w2_1
      g1_2 b1_2 g2_2 b2_2 wq2 wk2 wv2 wo2 w1_2 w2_2
      gf bf wh.

  Definition minitransformer_comm_1_8_2_16 : comm :=
    @minitransformer_comm 1 8 2 16 32 8
      eps8 toks8 tok_tab8 pos_tab8
      g1_1 b1_1 g2_1 b2_1 wq1 wk1 wv1 wo1 w1_1 w2_1
      g1_2 b1_2 g2_2 b2_2 wq2 wk2 wv2 wo2 w1_2 w2_2
      gf bf wh out8.

End Small_1_8_2_16.

(* [vm_compute]/conversion spot checks of the computable (structural) parts
   of the pipeline. *)

Definition i0_2 : fin 2 := @nat2fin 2 0 (ltac:(lia)).
Definition i1_2s : fin 2 := @nat2fin 2 1 (ltac:(lia)).
Definition i1_4 : fin 4 := @nat2fin 4 1 (ltac:(lia)).
Definition i3_4 : fin 4 := @nat2fin 4 3 (ltac:(lia)).

(* 4 x 2 embedding table, entry (i, j) = 10*i + j. *)
Definition T42 : exp (ary '{4} (ary '{2} num)) :=
  mkvSeq (fun i : fin 4 => mkvSeq (fun j : fin 2 =>
    (INR (fin2nat i * 10 + fin2nat j)%nat : exp num))).

(* Token index map: position 0 -> token 3, position 1 -> token 1. *)
Definition toks42 : fin 2 -> fin 4 :=
  fun i => if (fin2nat i =? 0)%nat then i3_4 else i1_4.

(* Embedding lookup: output position 0 selects row 3 of the table, whose
   entry 1 is 31. *)
Example check_embed_row3 :
  idx (idx (Gather2d toks42 T42) i0_2) i1_2s = INR 31.
Proof. vm_compute. reflexivity. Qed.

(* Residual add entry structure (block residual and embedding+position add
   share [Add3d]). *)
Example check_residual_entry :
  forall (x y : exp (ary '{2} (ary '{2} (ary '{2} num)))),
  idx (idx (idx (Add3d x y) i0_2) i1_2s) i1_2s =
  add (idx (idx (idx x i0_2) i1_2s) i1_2s)
      (idx (idx (idx y i0_2) i1_2s) i1_2s).
Proof. reflexivity. Qed.

(* GELU entry structure. *)
Example check_gelu3d_entry :
  forall (x : exp (ary '{2} (ary '{2} (ary '{2} num)))),
  idx (idx (idx (GELU3d x) i0_2) i1_2s) i1_2s =
  gelu (idx (idx (idx x i0_2) i1_2s) i1_2s).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_GELU3d.
Print Assumptions mhablock_direct_bind.
Print Assumptions transformerblock_comm_eq_direct.
Print Assumptions A_TransformerBlock.
Print Assumptions minitransformer_comm_eq_direct.
Print Assumptions A_MiniTransformer.
