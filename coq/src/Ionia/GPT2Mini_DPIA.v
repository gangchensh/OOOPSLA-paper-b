(* DPIA-style Leibniz equivalence proofs for a GPT-2-style decoder-only
   network (milestone N2b of the NLP/LLM extension, cf.
   doc/NLP与LLM扩展开发规划_20260911.md §2-N2), built on the pre-norm
   Transformer block of Ionia.MiniTransformer_DPIA (route-A R-based
   expression model).  All proofs closed with [Qed]; no Admitted/Axiom.

   GPT-2 completion points beyond [MiniTransformer]:

   - Weight tying: the output head weight is the transpose of the token
     embedding matrix ([Transpose2d wte] of Ionia.Ops_Transformer).  On the
     proof side the head is still a [BMatMul2d] stage whose weight happens
     to be [Transpose2d wte], so tying is pure parameter sharing — the same
     [wte] expression feeds both the embedding gather and the head, and
     [A_BMatMul2d] covers the head stage unchanged.  Freshness / write-read
     ordering is unaffected: tied weights are read-only expressions, only
     the temporary buffers are ever written.

   - Layer parametrisation: the layer stack is the [nat]-indexed fold
     [gpt2_layers k x] with per-layer parameters supplied by the family
     [lps : nat -> GPT2LParams], replacing the fixed N = 2 enumeration of
     [MiniTransformer].  The imperative stack [gpt2stack_comm] is the
     matching command fold (one temporary buffer [gblk] reused across
     layers — the ResNet50 shared-temporary pattern; the value bound by
     [bind_read] is a closed expression, so the reuse is aliasing-free).
     The key lemma [gpt2stack_comm_direct_read] (induction on k) collapses
     a k-layer stack followed by a [bind_read] to the direct fold applied
     to the functional layer value; the N = 2 case is the
     [minitransformer_comm_eq_direct] argument.

   - Final LayerNorm + GPT-2 configuration: FFN width [df = 4 * (h*d)]
     (the GPT-2 d_ff = 4 * d_model ratio), learned position embedding [wpe]
     broadcast over the batch, final [LayerNorm3d] before the tied head.

   Delivered theorems (all [Qed]):
   - [A_GPT2Block]: block-level DPIA correctness (the [A_TransformerBlock]
     instance at df = 4 * d_model, parameters packaged as [GPT2LParams]);
   - [A_GPT2Mini]: end-to-end — under freshness of the temporary buffers,
     the imperative N-layer GPT-2 observed at an output path equals the
     functional network.

   Sizes symbolic (batch b, sequence s, heads h, head dim d, layers n,
   vocab v); small instance at b = 1, s = 8, h = 2, d = 16 (d_model 32,
   d_ff 128), n = 3, v = 8, with a layer-unroll conversion check and a
   [vm_compute] spot check of the tied-weight transpose. *)

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
(* [Add3d] / [A_Add3d] (embedding + position, residual). *)
Require Import Ionia.Ops_Elementwise.
(* T1 operators: [LayerNorm3d], [Gather2d], [Transpose2d]. *)
Require Import Ionia.Ops_Transformer.
(* T2: [BMatMul2d] / [A_BMatMul2d]. *)
Require Import Ionia.Attention_DPIA.
(* T3/T4: [TransformerBlock], [transformerblock_comm]/[_direct],
   [transformerblock_comm_eq_direct], [A_TransformerBlock]; small-instance
   indices [i1_2s]/[i3_4] and the table [T42] for the spot check. *)
Require Import Ionia.MiniTransformer_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Generic command helpers                                                     *)
(* -------------------------------------------------------------------------- *)

(* [seq] is function composition, so associativity is definitional. *)
Lemma seq_assoc : forall c1 c2 c3 : comm,
  seq (seq c1 c2) c3 = seq c1 (seq c2 c3).
Proof. reflexivity. Qed.

(* Pushing a trailing command into a [bind_read] continuation is
   definitional as well. *)
Lemma bind_read_seq : forall (d : data) (p : path) (k : exp d -> comm) (c : comm),
  seq (bind_read (acc' p) k) c = bind_read (acc' p) (fun e => seq (k e) c).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Per-layer parameter package (GPT-2 block: pre-norm MHA + FFN)               *)
(* -------------------------------------------------------------------------- *)

Record GPT2LParams (dm df : nat) : Type := mkGPT2LParams {
  gp_ln1_g : exp (ary '{dm} num);
  gp_ln1_b : exp (ary '{dm} num);
  gp_ln2_g : exp (ary '{dm} num);
  gp_ln2_b : exp (ary '{dm} num);
  gp_wq : exp (ary '{dm} (ary '{dm} num));
  gp_wk : exp (ary '{dm} (ary '{dm} num));
  gp_wv : exp (ary '{dm} (ary '{dm} num));
  gp_wo : exp (ary '{dm} (ary '{dm} num));
  gp_w1 : exp (ary '{dm} (ary '{df} num));
  gp_w2 : exp (ary '{df} (ary '{dm} num))
}.

(* -------------------------------------------------------------------------- *)
(* GPT-2 network: embedding + N x GPT2Block + final LN + tied head             *)
(* -------------------------------------------------------------------------- *)

Section GPT2Net.

  (* All sizes symbolic: batch b, sequence s, heads h, head dimension d
     (model dimension h*d), vocabulary v, layers n.  The FFN width is the
     GPT-2 ratio df = 4 * (h*d), fixed in the parameter types below. *)
  Context (b s h d v n : nat).
  Context (eps : exp num).

  (* Token indices (host-level index map, cf. [Gather2d]) and the learned
     embedding tables: [wte] is shared with the output head (weight tying),
     [wpe] is the learned position table. *)
  Context (toks : fin s -> fin v).
  Context (wte : exp (ary '{v} (ary '{h * d} num)))
          (wpe : exp (ary '{s} (ary '{h * d} num))).

  (* Final LayerNorm. *)
  Context (lnf_g lnf_b : exp (ary '{h * d} num)).

  (* Per-layer parameters, indexed by layer number. *)
  Context (lps : nat -> GPT2LParams (h * d) (4 * (h * d))).

  Local Notation T := (exp (ary '{b} (ary '{s} (ary '{h * d} num)))).
  Local Notation accT := (acc (ary '{b} (ary '{s} (ary '{h * d} num)))).
  Local Notation accV := (acc (ary '{b} (ary '{s} (ary '{v} num)))).
  Local Notation LP := (GPT2LParams (h * d) (4 * (h * d))).

  (* ---------------- GPT2Block: the block at df = 4 * d_model ------------ *)

  Definition GPT2Block (input : T) (lp : LP) : T :=
    TransformerBlock input
      (gp_ln1_g lp) (gp_ln1_b lp) (gp_ln2_g lp) (gp_ln2_b lp)
      (gp_wq lp) (gp_wk lp) (gp_wv lp) (gp_wo lp)
      (gp_w1 lp) (gp_w2 lp) eps.

  Definition gpt2block_comm (input : T) (lp : LP) (output : accT) : comm :=
    transformerblock_comm input
      (gp_ln1_g lp) (gp_ln1_b lp) (gp_ln2_g lp) (gp_ln2_b lp)
      (gp_wq lp) (gp_wk lp) (gp_wv lp) (gp_wo lp)
      (gp_w1 lp) (gp_w2 lp) eps output.

  Definition gpt2block_direct (input : T) (lp : LP) (output : accT) : comm :=
    transformerblock_direct input
      (gp_ln1_g lp) (gp_ln1_b lp) (gp_ln2_g lp) (gp_ln2_b lp)
      (gp_wq lp) (gp_wk lp) (gp_wv lp) (gp_wo lp)
      (gp_w1 lp) (gp_w2 lp) eps output.

  (* [exact] with an explicitly instantiated lemma: [apply] on these
     block-folded commands triggers pathological unification (minutes). *)
  Lemma gpt2block_comm_eq_direct : forall (input : T) (lp : LP) (output : accT),
    gpt2block_comm input lp output = gpt2block_direct input lp output.
  Proof.
    intros. exact (@transformerblock_comm_eq_direct b s h d (4 * (h * d)) input
      (gp_ln1_g lp) (gp_ln1_b lp) (gp_ln2_g lp) (gp_ln2_b lp)
      (gp_wq lp) (gp_wk lp) (gp_wv lp) (gp_wo lp)
      (gp_w1 lp) (gp_w2 lp) eps output).
  Qed.

  (* Block-level DPIA correctness (the [A_TransformerBlock] shape; the final
     assignment is env-independent, so no freshness premise is needed). *)
  Lemma A_GPT2Block : forall (input : T) (lp : LP) (output : accT)
    (rho : env) (p : path),
    in_acc p output ->
    gpt2block_comm input lp output rho p = A(output, GPT2Block input lp) rho p.
  Proof.
    intros. exact (@A_TransformerBlock b s h d (4 * (h * d)) input
      (gp_ln1_g lp) (gp_ln1_b lp) (gp_ln2_g lp) (gp_ln2_b lp)
      (gp_wq lp) (gp_wk lp) (gp_wv lp) (gp_wo lp)
      (gp_w1 lp) (gp_w2 lp) eps output rho p H).
  Qed.

  (* Reading the block's output buffer after the (folded) direct form yields
     the functional block value (tail variant of
     [transformerblock_direct_read], proved by unfolding like
     [mhablock_direct_bind]). *)
  Lemma gpt2block_direct_read0 : forall (input : T) (lp : LP)
    (q : path) (kk : T -> comm),
    seq (gpt2block_direct input lp (acc' q)) (bind_read (acc' q) kk) =
    seq (gpt2block_direct input lp (acc' q)) (kk (GPT2Block input lp)).
  Proof.
    intros. fun_ext.
    unfold gpt2block_direct, transformerblock_direct, GPT2Block,
           TransformerBlock, FFN, seq, bind_read, A.
    cbv beta zeta.
    rewrite read_exp_assign. reflexivity.
  Qed.

  (* ---------------- N-layer stack (inductive fold) ----------------------- *)

  (* Functional fold: layer k applies [GPT2Block] with parameters [lps k]. *)
  Fixpoint gpt2_layers (k : nat) (x : T) : T :=
    match k with
    | O => x
    | S k' => GPT2Block (gpt2_layers k' x) (lps k')
    end.

  (* Imperative fold: layer k reads the previous layer's value from the
     shared temporary [gblk] (as a closed expression via [bind_read]) and
     writes the block output to [output]. *)
  Fixpoint gpt2stack_comm (k : nat) (input : T) (output : accT) : comm :=
    match k with
    | O => A(output, input)
    | S k' =>
        new (fun t => seq (gpt2stack_comm k' input t)
                          (bind_read t (fun e => gpt2block_comm e (lps k') output)))
            (acc' (Var "gblk"))
    end.

  (* Direct (DPIA-normal) fold: left-associated, the last layer's block
     direct form exposed at the top level. *)
  Fixpoint gpt2stack_direct (k : nat) (input : T) (output : accT) : comm :=
    match k with
    | O => A(output, input)
    | S k' =>
        seq (gpt2stack_direct k' input (acc' (Var "gblk")))
            (gpt2block_direct (gpt2_layers k' input) (lps k') output)
    end.

  (* Key stack lemma, by induction on the number of layers: a k-layer
     imperative stack followed by a [bind_read] of its output buffer equals
     the direct fold followed by the continuation applied to the functional
     layer value. *)
  Lemma gpt2stack_comm_direct_read : forall (k : nat) (input : T) (q : path)
    (kk : T -> comm),
    seq (gpt2stack_comm k input (acc' q)) (bind_read (acc' q) kk) =
    seq (gpt2stack_direct k input (acc' q)) (kk (gpt2_layers k input)).
  Proof.
    induction k; intros.
    - cbn [gpt2stack_comm gpt2stack_direct gpt2_layers].
      apply bind_read_replace.
    - cbn [gpt2stack_comm gpt2stack_direct gpt2_layers].
      unfold new. cbv beta.
      rewrite seq_assoc. rewrite seq_assoc.
      rewrite bind_read_seq.
      rewrite IHk. cbv beta.
      rewrite gpt2block_comm_eq_direct.
      rewrite gpt2block_direct_read0.
      reflexivity.
  Qed.

  (* ---------------- Functional network (opaque layer wrappers) ---------- *)

  (* Batched embedding: the same token sequence / position table in every
     batch element (the batch=1 use case; the tables are arbitrary
     parameters). *)
  Definition BEmbed : T := mkvSeq (fun bb : fin b => Gather2d toks wte).
  Definition BPos : T := mkvSeq (fun bb : fin b => wpe).

  Definition gpt2_x0 : T := Add3d BEmbed BPos.
  Definition gpt2_xN : T := gpt2_layers n gpt2_x0.
  Definition gpt2_xf : T := LayerNorm3d gpt2_xN lnf_g lnf_b eps.

  Lemma gpt2_x0_body : gpt2_x0 = Add3d BEmbed BPos.
  Proof. reflexivity. Qed.
  Lemma gpt2_xN_body : gpt2_xN = gpt2_layers n gpt2_x0.
  Proof. reflexivity. Qed.
  Lemma gpt2_xf_body : gpt2_xf = LayerNorm3d gpt2_xN lnf_g lnf_b eps.
  Proof. reflexivity. Qed.

  Opaque gpt2_x0 gpt2_xN gpt2_xf.

  (* The full GPT-2 network: the output head shares the token embedding
     matrix (weight tying, head weight = [Transpose2d wte]). *)
  Definition GPT2Mini : exp (ary '{b} (ary '{s} (ary '{v} num))) :=
    BMatMul2d gpt2_xf (Transpose2d wte).

  Lemma GPT2Mini_body : GPT2Mini = BMatMul2d gpt2_xf (Transpose2d wte).
  Proof. reflexivity. Qed.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition gpt2mini_comm (output : accV) : comm :=
new (fun t0 => seq (Add3d_comm BEmbed BPos t0)
(bind_read t0 (fun e0 =>
new (fun tN => seq (gpt2stack_comm n e0 tN)
(bind_read tN (fun eN =>
new (fun tf => seq (LayerNorm3d_comm eN lnf_g lnf_b eps tf)
(bind_read tf (fun ef => BMatMul2d_comm ef (Transpose2d wte) output)))
(acc' (Var "glnf")))))
(acc' (Var "glx")))))
(acc' (Var "gemb")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition gpt2mini_direct (output : accV) : comm :=
    seq (A(acc' (Var "gemb"), gpt2_x0))
    (seq (gpt2stack_direct n gpt2_x0 (acc' (Var "glx")))
    (seq (A(acc' (Var "glnf"), gpt2_xf))
         (A(output, GPT2Mini)))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition gemb_acc : accT := acc' (Var "gemb").
  Definition glx_acc : accT := acc' (Var "glx").
  Definition glnf_acc : accT := acc' (Var "glnf").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The
     stack buffer [gblk], the block temporaries bln1..btf2 and the MHA
     temporaries mtq..mtmg are shared between all layers and are required
     to be fresh at every type (the [resnet50_fresh] pattern). *)
  Definition gpt2mini_fresh (output : accV) (rho : env) : Prop :=
    StructUndefined gemb_acc rho /\
    StructUndefined glx_acc rho /\
    StructUndefined glnf_acc rho /\
    (forall d0 : data, StructUndefined (acc' (Var "gblk") : acc d0) rho) /\
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
    (forall p, in_acc p output -> ~ in_acc p gemb_acc) /\
    (forall p, in_acc p output -> ~ in_acc p glx_acc) /\
    (forall p, in_acc p output -> ~ in_acc p glnf_acc) /\
    (forall (d0 : data) p, in_acc p output -> ~ in_acc p (acc' (Var "gblk") : acc d0)) /\
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

  Lemma gpt2mini_comm_eq_direct :
    forall (output : accV),
    gpt2mini_comm output = gpt2mini_direct output.
  Proof.
    intros.
    unfold gpt2mini_comm, gpt2mini_direct, new.
    cbv beta.
    rewrite <- A_Add3d.
    rewrite <- gpt2_x0_body.
    rewrite bind_read_replace.
    cbv beta.
    rewrite gpt2stack_comm_direct_read.
    cbv beta.
    rewrite <- gpt2_xN_body.
    rewrite <- A_LayerNorm3d.
    rewrite <- gpt2_xf_body.
    rewrite bind_read_replace.
    cbv beta.
    rewrite <- A_BMatMul2d.
    rewrite <- GPT2Mini_body.
    reflexivity.
  Qed.

  Lemma A_GPT2Mini_direct :
    forall (output : accV) (rho : env) (p : path),
    in_acc p output ->
    gpt2mini_fresh output rho ->
    gpt2mini_direct output rho p = A(output, GPT2Mini) rho p.
  Proof.
    intros.
    unfold gpt2mini_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - reflexivity.
  Qed.

  (* End-to-end DPIA correctness of GPT-2: under freshness of the temporary
     buffers, the imperative N-layer network observed at an output path
     computes the functional [GPT2Mini] (with tied output head). *)
  Theorem A_GPT2Mini :
    forall (output : accV) (rho : env) (p : path),
    in_acc p output ->
    gpt2mini_fresh output rho ->
    gpt2mini_comm output rho p = A(output, GPT2Mini) rho p.
  Proof.
    intros. rewrite gpt2mini_comm_eq_direct.
    apply A_GPT2Mini_direct; assumption.
  Qed.

  (* Layer-fold unroll check (conversion): two layers are two nested blocks. *)
  Example check_layers_unroll2 : forall x : T,
    gpt2_layers 2 x = GPT2Block (GPT2Block x (lps 0)) (lps 1).
  Proof. reflexivity. Qed.

End GPT2Net.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: b = 1, s = 8, h = 2, d = 16 (d_model 32, d_ff 128),    *)
(* layers n = 3, vocab v = 8                                                  *)
(* -------------------------------------------------------------------------- *)

Section Small_1_8_2_16_L3.

  Context (eps8 : exp num)
          (toks8 : fin 8 -> fin 8)
          (wte8 : exp (ary '{8} (ary '{32} num)))
          (wpe8 : exp (ary '{8} (ary '{32} num)))
          (lnf_g8 lnf_b8 : exp (ary '{32} num))
          (lp0 lp1 lp2 : GPT2LParams 32 128)
          (out8 : acc (ary '{1} (ary '{8} (ary '{8} num)))).

  (* A concrete 3-layer parameter family. *)
  Definition lps8 : nat -> GPT2LParams (2 * 16) (4 * (2 * 16)) :=
    fun k => match k with 0 => lp0 | 1 => lp1 | _ => lp2 end.

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition GPT2Mini_1_8_2_16_L3 : exp (ary '{1} (ary '{8} (ary '{8} num))) :=
    @GPT2Mini 1 8 2 16 8 3 eps8 toks8 wte8 wpe8 lnf_g8 lnf_b8 lps8.

  Definition gpt2mini_comm_1_8_2_16_L3 : comm :=
    @gpt2mini_comm 1 8 2 16 8 3 eps8 toks8 wte8 wpe8 lnf_g8 lnf_b8 lps8 out8.

End Small_1_8_2_16_L3.

(* [vm_compute] spot check of the tied-weight transpose: entry (j, i) of
   [Transpose2d wte] is entry (i, j) of the embedding table, so the head's
   logit column for token j reuses embedding row j.  Here the transposed
   4x2 table (entry (i, j) = 10*i + j) has entry (1, 3) = 31. *)
Example check_tied_transpose_entry :
  idx (idx (Transpose2d T42) i1_2s) i3_4 = INR 31.
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_GPT2Block.
Print Assumptions gpt2block_direct_read0.
Print Assumptions gpt2stack_comm_direct_read.
Print Assumptions gpt2mini_comm_eq_direct.
Print Assumptions A_GPT2Mini.
