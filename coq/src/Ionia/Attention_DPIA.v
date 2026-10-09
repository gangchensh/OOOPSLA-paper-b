(* DPIA-style Leibniz equivalence proofs for the Transformer attention block
   (milestone T2 of the Transformer extension, cf.
   doc/Transformer扩展开发规划_20260829.md) in the route-A R-based expression
   model.

   Delivered here (all closed with [Qed], no Admitted/Axiom):

   - [Attention_cell]: single-head scaled dot-product causal attention
       softmax(causal_mask(Q K^T / sqrt(d))) V
     on s x d query/key/value matrices.  The imperative counterpart
     [attention_cell_comm] is the MatMul2d loop nest whose first input is
     the composed score expression; this follows the route-A
     recompute-per-element philosophy (mean/variance in Ionia.Ops_BatchNorm
     are recomputed per element in the same way) and the composed-input
     final stage of ResNet18 ([Softmax2d_comm (Linear2d ...) output] in
     Ionia.ResNet18_DPIA).  Because the command writes no temporary
     buffers, the cell rule [A_Attention_cell] is a plain Leibniz command
     equality, exactly like the operator rules of milestone T1.

   - [MHABlock]: multi-head causal self-attention block over a
     batch x sequence x (heads*dim) input with right-multiplied projection
     matrices:
       q = x Wq, k = x Wk, v = x Wv       (batched, [BMatMul2d])
       split heads   (b,s,h*d) -> (b,h,s,d)   [SplitHeads]
       per-head [Attention_cell]              [AttnHeads]
       merge heads   (b,h,s,d) -> (b,s,h*d)   [MergeHeads]
       output projection  merged Wo           [BMatMul2d]
     The imperative block [mhablock_comm] stages the computation through
     freshly allocated buffers with [new]/[bind_read], exactly as the
     ResNet block combinators of Ionia.ResNet18_DPIA;
     [mhablock_comm_eq_direct] collapses it to the buffer-free direct form
     (a sequence of whole-array assignments), and [A_MHABlock] observes the
     block at an output path (the pointwise form of [A_BasicBlock_id]).
     Every stage collapses to a single [A] assignment because each stage
     command writes no temporary buffers, so the standard
     [bind_read_replace] chain applies without any whole-array read-back
     machinery.

   - A concrete instantiation at sequence length s = 8, head dimension
     d = 16, h = 2 heads, batch 1 (model dimension h*d = 32), with
     [vm_compute] spot checks of the computable parts of the pipeline
     (causal masking, head-split indexing, softmax entry structure).  The
     standard reals are not computable ([Rplus]/[exp] are opaque), so
     end-to-end numeric validation goes through extraction, as in
     Ionia.test_LongChain_numerical. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* [bind_read] and the bind_read elimination lemmas. *)
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
(* [Mulc2d] (pointwise scaling by 1/sqrt(d)). *)
Require Import Ionia.Ops_Elementwise.
(* [Softmax2d]. *)
Require Import Ionia.Ops_Reduce.
(* T1 operators: [MatMul2d], [Transpose2d], [CausalMask2d], [NEGINF],
   [SplitHeads], [MergeHeads]. *)
Require Import Ionia.Ops_Transformer.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Attention scale factor 1/sqrt(d)                                            *)
(* -------------------------------------------------------------------------- *)

Definition attn_scale (d : nat) : exp num := div one (sqrt (INR d)).

(* -------------------------------------------------------------------------- *)
(* Single-head attention cell                                                  *)
(* -------------------------------------------------------------------------- *)

(* softmax(CausalMask(Q K^T / sqrt(d))) V on s x d matrices. *)
Definition Attention_cell {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  : exp (ary '{s} (ary '{d} num)) :=
  let scores := MatMul2d q (Transpose2d k) in
  let scaled := Mulc2d (attn_scale d) scores in
  let masked := CausalMask2d scaled in
  let attn := Softmax2d masked in
  MatMul2d attn v.

(* The cell command is the final MatMul2d loop nest over the composed score
   expression; it writes only [output], so the cell rule is a plain command
   equality (the T1 operator style). *)
Definition attention_cell_comm {s d : nat}
  (q k v : exp (ary '{s} (ary '{d} num)))
  (output : acc (ary '{s} (ary '{d} num))) : comm :=
  MatMul2d_comm (Softmax2d (CausalMask2d (Mulc2d (attn_scale d)
                                                 (MatMul2d q (Transpose2d k)))))
                v output.

Lemma A_Attention_cell : forall (s d : nat)
  (q k v : exp (ary '{s} (ary '{d} num)))
  (output : acc (ary '{s} (ary '{d} num))),
  A(output, Attention_cell q k v) = attention_cell_comm q k v output.
Proof.
  intros. unfold Attention_cell, attention_cell_comm. cbv zeta.
  apply A_MatMul2d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Batched right-multiplication by a projection matrix                         *)
(* -------------------------------------------------------------------------- *)

Definition BMatMul2d {b m n p : nat}
  (a : exp (ary '{b} (ary '{m} (ary '{n} num))))
  (w : exp (ary '{n} (ary '{p} num)))
  : exp (ary '{b} (ary '{m} (ary '{p} num))) :=
  mkvSeq (fun bb : fin b => MatMul2d (idx a bb) w).

Definition BMatMul2d_comm {b m n p : nat}
  (a : exp (ary '{b} (ary '{m} (ary '{n} num))))
  (w : exp (ary '{n} (ary '{p} num)))
  (output : acc (ary '{b} (ary '{m} (ary '{p} num)))) : comm :=
  mkvSeql (fun bb ob => MatMul2d_comm (idx a bb) w ob) output.

Lemma A_BMatMul2d : forall (b m n p : nat)
  (a : exp (ary '{b} (ary '{m} (ary '{n} num))))
  (w : exp (ary '{n} (ary '{p} num)))
  (output : acc (ary '{b} (ary '{m} (ary '{p} num)))),
  A(output, BMatMul2d a w) = BMatMul2d_comm a w output.
Proof.
  intros. unfold BMatMul2d, BMatMul2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite A_MatMul2d.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Per-head attention over a (b, h, s, d) triple                               *)
(* -------------------------------------------------------------------------- *)

Definition AttnHeads {b h s d : nat}
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))) :=
  mkvSeq (fun bb : fin b => mkvSeq (fun hh : fin h =>
    Attention_cell (idx (idx qs bb) hh) (idx (idx ks bb) hh) (idx (idx vs bb) hh))).

Definition AttnHeads_comm {b h s d : nat}
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))) : comm :=
  mkvSeql (fun bb ob => mkvSeql (fun hh oh =>
    attention_cell_comm (idx (idx qs bb) hh) (idx (idx ks bb) hh)
                        (idx (idx vs bb) hh) oh) ob) output.

Lemma A_AttnHeads : forall (b h s d : nat)
  (qs ks vs : exp (ary '{b} (ary '{h} (ary '{s} (ary '{d} num)))))
  (output : acc (ary '{b} (ary '{h} (ary '{s} (ary '{d} num))))),
  A(output, AttnHeads qs ks vs) = AttnHeads_comm qs ks vs output.
Proof.
  intros. unfold AttnHeads, AttnHeads_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro bb.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro hh.
  rewrite A_Attention_cell.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Multi-head attention block                                                  *)
(* -------------------------------------------------------------------------- *)

(* Functional block: qkv projections, head split, per-head attention, head
   merge, output projection. *)
Definition MHABlock {b s h d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  : exp (ary '{b} (ary '{s} (ary '{h * d} num))) :=
  let q := BMatMul2d input wq in
  let k := BMatMul2d input wk in
  let v := BMatMul2d input wv in
  let qs := SplitHeads q in
  let ks := SplitHeads k in
  let vs := SplitHeads v in
  let att := AttnHeads qs ks vs in
  let merged := MergeHeads att in
  BMatMul2d merged wo.

(* Imperative block: temporaries mtq..mtmg, output written in place.  Each
   buffer is read by [bind_read] immediately after the assignment that
   produces it, and the read of a split buffer wraps all later stages
   (the [bt7] pattern of [basicblock_proj_comm] in Ionia.ResNet18_DPIA). *)
Definition mhablock_comm {b s h d : nat}
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
  new (fun tatt => seq (AttnHeads_comm eqs eks evs tatt)
  (bind_read tatt (fun eatt =>
  new (fun tmg => seq (MergeHeads_comm eatt tmg)
  (bind_read tmg (fun emg =>
    BMatMul2d_comm emg wo output)))
  (acc' (Var "mtmg")))))
  (acc' (Var "mtatt")))))
  (acc' (Var "mtvs")))))
  (acc' (Var "mtv")))))
  (acc' (Var "mtks")))))
  (acc' (Var "mtk")))))
  (acc' (Var "mtqs")))))
  (acc' (Var "mtq")).

(* Direct (DPIA-normal) form of the block: a sequence of whole-array
   assignments of the functional stage values. *)
Definition mhablock_direct {b s h d : nat}
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))) : comm :=
  let q := BMatMul2d input wq in
  let k := BMatMul2d input wk in
  let v := BMatMul2d input wv in
  let qs := SplitHeads q in
  let ks := SplitHeads k in
  let vs := SplitHeads v in
  let att := AttnHeads qs ks vs in
  let merged := MergeHeads att in
  seq (A(acc' (Var "mtq"), q))
  (seq (A(acc' (Var "mtqs"), qs))
  (seq (A(acc' (Var "mtk"), k))
  (seq (A(acc' (Var "mtks"), ks))
  (seq (A(acc' (Var "mtv"), v))
  (seq (A(acc' (Var "mtvs"), vs))
  (seq (A(acc' (Var "mtatt"), att))
  (seq (A(acc' (Var "mtmg"), merged))
       (A(output, BMatMul2d merged wo))))))))).

Lemma mhablock_comm_eq_direct : forall (b s h d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num)))),
  mhablock_comm input wq wk wv wo output =
  mhablock_direct input wq wk wv wo output.
Proof.
  intros.
  unfold mhablock_comm, mhablock_direct, new.
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
  rewrite <- A_AttnHeads.
  rewrite bind_read_replace.
  rewrite <- A_MergeHeads.
  rewrite bind_read_replace.
  rewrite <- A_BMatMul2d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MHABlock] (the [A_BasicBlock_id] shape of
   Ionia.ResNet18_DPIA; the final assignment is env-independent, so no
   freshness premise on the temporaries is needed). *)
Lemma A_MHABlock : forall (b s h d : nat)
  (input : exp (ary '{b} (ary '{s} (ary '{h * d} num))))
  (wq wk wv wo : exp (ary '{h * d} (ary '{h * d} num)))
  (output : acc (ary '{b} (ary '{s} (ary '{h * d} num))))
  (rho : env) (p : path),
  in_acc p output ->
  mhablock_comm input wq wk wv wo output rho p =
  A(output, MHABlock input wq wk wv wo) rho p.
Proof.
  intros. rewrite mhablock_comm_eq_direct.
  unfold mhablock_direct, MHABlock, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: s = 8, d = 16 per head, h = 2 heads, batch 1             *)
(* (model dimension h*d = 32)                                                  *)
(* -------------------------------------------------------------------------- *)

Section Small_8_16_2.

  Context (x32 : exp (ary '{1} (ary '{8} (ary '{32} num))))
          (wq32 wk32 wv32 wo32 : exp (ary '{32} (ary '{32} num)))
          (out32 : acc (ary '{1} (ary '{8} (ary '{32} num)))).

  (* Shape check: the symbolic block and its command instantiate at the
     small size. *)
  Definition MHABlock_8_16_2 : exp (ary '{1} (ary '{8} (ary '{32} num))) :=
    MHABlock (h:=2) (d:=16) x32 wq32 wk32 wv32 wo32.

  Definition mhablock_comm_8_16_2 : comm :=
    mhablock_comm (h:=2) (d:=16) x32 wq32 wk32 wv32 wo32 out32.

End Small_8_16_2.

(* [vm_compute] spot checks of the computable (structural) parts of the
   pipeline at the instance sizes.  Index literals carry [ltac:(lia)]
   proofs, which [fin2nat] erases computationally. *)

Definition i0_1 : fin 1 := @nat2fin 1 0 (ltac:(lia)).
Definition i1_2 : fin 2 := @nat2fin 2 1 (ltac:(lia)).
Definition i3_8 : fin 8 := @nat2fin 8 3 (ltac:(lia)).
Definition i5_8 : fin 8 := @nat2fin 8 5 (ltac:(lia)).
Definition i3_16 : fin 16 := @nat2fin 16 3 (ltac:(lia)).

(* row*10+col encoding of an 8x8 score matrix. *)
Definition M8 : exp (ary '{8} (ary '{8} num)) :=
  mkvSeq (fun i : fin 8 => mkvSeq (fun j : fin 8 =>
    (INR ((fin2nat i * 10 + fin2nat j)%nat) : exp num))).

(* Keep below the diagonal: position (5,3) keeps the score 53.  The mask
   checks use plain conversion rather than [vm_compute]: evaluating the full
   masked matrix would force the unary-nat literal 10^30 inside [NEGINF]. *)
Example check_mask_keep :
  idx (idx (CausalMask2d M8) i5_8) i3_8 = INR 53.
Proof. reflexivity. Qed.

(* Mask above the diagonal: position (3,5) becomes [NEGINF]. *)
Example check_mask_drop :
  idx (idx (CausalMask2d M8) i3_8) i5_8 = NEGINF.
Proof. reflexivity. Qed.

(* Value = merged feature index, batch 1 x seq 8 x model 32. *)
Definition X32 : exp (ary '{1} (ary '{8} (ary '{32} num))) :=
  mkvSeq (fun bb : fin 1 => mkvSeq (fun ss : fin 8 => mkvSeq (fun xx : fin 32 =>
    (INR (fin2nat xx) : exp num)))).

(* Head 1, dim 3 sits at merged feature index 1*16+3 = 19. *)
Example check_split_heads :
  idx (idx (idx (idx (SplitHeads (heads:=2) (dim:=16) X32) i0_1) i1_2) i5_8) i3_16
  = INR 19.
Proof. vm_compute. reflexivity. Qed.

(* One softmax entry at the instance size: numerator exp of the (5,3)
   element, denominator the row-5 exponential sum. *)
Example check_softmax_entry :
  idx (idx (Softmax2d M8) i5_8) i3_8 =
  div (pExp (INR 53))
      (sum (mkvSeq (fun i0 : fin 8 => pExp (idx (idx M8 i5_8) i0)))).
Proof. vm_compute. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Attention_cell.
Print Assumptions A_BMatMul2d.
Print Assumptions A_AttnHeads.
Print Assumptions mhablock_comm_eq_direct.
Print Assumptions A_MHABlock.
