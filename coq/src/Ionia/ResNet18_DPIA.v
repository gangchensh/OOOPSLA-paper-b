(* DPIA-style end-to-end Leibniz correctness proof for ResNet18 (route A).

   Structure: classic ResNet18 in 4d batched form, spatial size symbolic (m):
     conv1(7x7,p3,s2) - bn - relu - maxpool(3x3,s2,p1)
     stage1: 2 x BasicBlock(64,  identity shortcuts)
     stage2: 2 x BasicBlock(128, first block projects 64->128, stride 2)
     stage3: 2 x BasicBlock(256, first block projects 128->256, stride 2)
     stage4: 2 x BasicBlock(512, first block projects 256->512, stride 2)
     GlobalAvgPool - fc(1000) - softmax

   Each BasicBlock is
     conv3x3 - bn - relu - conv3x3 - bn   (main path)
     (+ 1x1 conv s2 - bn on the shortcut for projection blocks)
     Add(shortcut) - relu.
   BatchNorm uses the recomputed per-element mean/variance design of
   Ops_BatchNorm.v (only gamma/beta/eps are parameters).

   A note on operator reuse.  The proved specialisations
   [Conv4d_p1_k3_s2] / [Conv4d_p0_k1_s2] of Ops_Conv.v carry the output-size
   expressions [(h - 3 + 2*1)/2 + 1] and [(h - 1 + 0)/2 + 1], which are
   propositionally but not definitionally equal for symbolic [h]; the residual
   [Add4d] needs both branches at one convertible type, so the stride-2
   convolutions inside blocks are given here as canonical-size variants
   [Conv4d_3x3_s2] / [Conv4d_1x1_s2] with output size [half m = (m+1)/2]
   (equal to both specialisation sizes whenever m >= 3, with identical
   indexing).  Likewise [Conv4d_3x3_s1] is the same-size 3x3 stride-1
   convolution, avoiding the non-convertible [(h - 3 + 2*1)/1 + 1].  Their
   correctness lemmas are proved exactly like [A_Conv4d].  The stem reuses
   the proved [Conv4d_p3_k7_s2] and AlexNet's [Maxpool4d_pad] directly.

   Each block combinator [basicblock_*_comm] is proved equal to a buffer-free
   "direct" form ([basicblock_*_comm_eq_direct]); the network-level proof
   then mirrors AlexNet_DPIA.v: comm = direct form by rewriting, and the
   direct form observed at an output path equals the functional network. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
Require Import Ionia.AlexNet_DPIA.
Require Import Ionia.Ops_Conv.
Require Import Ionia.Ops_BatchNorm.
Require Import Ionia.Ops_Elementwise.
Require Import Ionia.Ops_PoolPad.
Require Import Ionia.Ops_Reduce.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Canonical output sizes                                                     *)
(* -------------------------------------------------------------------------- *)

(* Stride-2 output size (number of positions 0,2,4,... below m). *)
Definition half (m : nat) : nat := (m + 1) / 2.

(* Stem conv (7x7, p3, s2) output size, as in [Conv4d_p3_k7_s2]. *)
Definition s_stem (m : nat) : nat := (m - 7 + 2 * 3) / 2 + 1.

(* Stem maxpool (3x3, s2, p1) output size, as in [Maxpool4d_pad 3 2 1]. *)
Definition s_pool (m : nat) : nat := (s_stem m - 3 + 2 * 1) / 2 + 1.

(* -------------------------------------------------------------------------- *)
(* Conv4d_3x3_s1 : same-size 3x3 convolution, padding 1, stride 1             *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_3x3_s1 {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin m1 => mkvSeq (fun j0 : fin m2 =>
      add (sum (mkvSeq (fun c : fin inch =>
            sum (mkvSeq (fun i1 : fin 3 =>
              sum (mkvSeq (fun j1 : fin 3 =>
                mul (pad_idx2d 1 (idx (idx input b) c)
                               (fin2nat i0 + fin2nat i1)
                               (fin2nat j0 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition Conv4d_3x3_s1_comm {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin inch =>
             sum (mkvSeq (fun i1 : fin 3 =>
               sum (mkvSeq (fun j1 : fin 3 =>
                 mul (pad_idx2d 1 (idx (idx input b) c)
                                (fin2nat i0 + fin2nat i1)
                                (fin2nat j0 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_Conv4d_3x3_s1 : forall (batch inch outch m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  A(output, Conv4d_3x3_s1 bias w input) = Conv4d_3x3_s1_comm bias w input output.
Proof.
  intros. unfold Conv4d_3x3_s1, Conv4d_3x3_s1_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv4d_3x3_s2 : 3x3 convolution, padding 1, stride 2, output [half]        *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_3x3_s2 {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin (half m1) => mkvSeq (fun j0 : fin (half m2) =>
      add (sum (mkvSeq (fun c : fin inch =>
            sum (mkvSeq (fun i1 : fin 3 =>
              sum (mkvSeq (fun j1 : fin 3 =>
                mul (pad_idx2d 1 (idx (idx input b) c)
                               (fin2nat i0 * 2 + fin2nat i1)
                               (fin2nat j0 * 2 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition Conv4d_3x3_s2_comm {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin inch =>
             sum (mkvSeq (fun i1 : fin 3 =>
               sum (mkvSeq (fun j1 : fin 3 =>
                 mul (pad_idx2d 1 (idx (idx input b) c)
                                (fin2nat i0 * 2 + fin2nat i1)
                                (fin2nat j0 * 2 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_Conv4d_3x3_s2 : forall (batch inch outch m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  A(output, Conv4d_3x3_s2 bias w input) = Conv4d_3x3_s2_comm bias w input output.
Proof.
  intros. unfold Conv4d_3x3_s2, Conv4d_3x3_s2_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv4d_1x1_s2 : 1x1 convolution, stride 2, output [half] (projection)      *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_1x1_s2 {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin (half m1) => mkvSeq (fun j0 : fin (half m2) =>
      add (sum (mkvSeq (fun c : fin inch =>
            sum (mkvSeq (fun i1 : fin 1 =>
              sum (mkvSeq (fun j1 : fin 1 =>
                mul (pad_idx2d 0 (idx (idx input b) c)
                               (fin2nat i0 * 2 + fin2nat i1)
                               (fin2nat j0 * 2 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition Conv4d_1x1_s2_comm {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin inch =>
             sum (mkvSeq (fun i1 : fin 1 =>
               sum (mkvSeq (fun j1 : fin 1 =>
                 mul (pad_idx2d 0 (idx (idx input b) c)
                                (fin2nat i0 * 2 + fin2nat i1)
                                (fin2nat j0 * 2 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_Conv4d_1x1_s2 : forall (batch inch outch m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  A(output, Conv4d_1x1_s2 bias w input) = Conv4d_1x1_s2_comm bias w input output.
Proof.
  intros. unfold Conv4d_1x1_s2, Conv4d_1x1_s2_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* After a command that ends with an assignment of [e] to [acc' p], a
   subsequent [bind_read (acc' p)] yields [e].  This variant of
   [bind_read_replace_seq] (LeNet5_DPIA) matches a left-associated prefix
   [seq prefix (A(acc' p, e))], which is the shape produced by the block
   direct forms below. *)
Lemma bind_read_replace_seq_r :
  forall (d : data) (p : path) (e : exp d)
    (prefix : comm) (k : exp d -> comm) (c : comm),
  seq (seq prefix (A(acc' p, e))) (seq (bind_read (acc' p) k) c) =
  seq (seq prefix (A(acc' p, e))) (seq (k e) c).
Proof.
  intros. unfold seq, bind_read, A.
  fun_ext.
  rewrite read_exp_assign. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* BasicBlock with identity shortcut                                          *)
(* -------------------------------------------------------------------------- *)

Definition BasicBlock_id {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_3x3_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  ReLU4d (Add4d n2 input).

(* Imperative block: temporaries bt1..bt6, output written in place. *)
Definition basicblock_id_comm {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  new (fun t1 => seq (Conv4d_3x3_s1_comm b1 w1 input t1)
  (new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
  (new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
  (new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_3x3_s1_comm b2 w2 e3 t4))
  (new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
  (new (fun t6 => seq (bind_read t5 (fun e5 => Add4d_comm e5 input t6))
       (bind_read t6 (fun e6 => ReLU4d_comm e6 output))
  ) (acc' (Var "bt6")))
  ) (acc' (Var "bt5")))
  ) (acc' (Var "bt4")))
  ) (acc' (Var "bt3")))
  ) (acc' (Var "bt2")))
  ) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the identity block. *)
Definition basicblock_id_direct {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_3x3_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let a2 := Add4d n2 input in
  seq (seq (seq (seq (seq (seq (A(acc' (Var "bt1"), c1))
                                (A(acc' (Var "bt2"), n1)))
                             (A(acc' (Var "bt3"), r1)))
                          (A(acc' (Var "bt4"), c2)))
                       (A(acc' (Var "bt5"), n2)))
                    (A(acc' (Var "bt6"), a2)))
       (A(output, ReLU4d a2)).

Lemma basicblock_id_comm_eq_direct : forall (batch c m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  basicblock_id_comm input w1 b1 g1 z1 w2 b2 g2 z2 eps output =
  basicblock_id_direct input w1 b1 g1 z1 w2 b2 g2 z2 eps output.
Proof.
  intros.
  unfold basicblock_id_comm, basicblock_id_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Add4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [BasicBlock_id]. *)
Lemma A_BasicBlock_id : forall (batch c m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{c} num)) (g1 : exp (ary '{c} num)) (z1 : exp (ary '{c} num))
  (w2 : exp (ary '{c} (ary '{c} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c} num)) (g2 : exp (ary '{c} num)) (z2 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  basicblock_id_comm input w1 b1 g1 z1 w2 b2 g2 z2 eps output rho p =
  A(output, BasicBlock_id input w1 b1 g1 z1 w2 b2 g2 z2 eps) rho p.
Proof.
  intros. rewrite basicblock_id_comm_eq_direct.
  unfold basicblock_id_direct, BasicBlock_id, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* BasicBlock with projection shortcut (stride 2, 1x1 conv + BN)              *)
(* -------------------------------------------------------------------------- *)

Definition BasicBlock_proj {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{outch} num)) (g1 : exp (ary '{outch} num)) (z1 : exp (ary '{outch} num))
  (w2 : exp (ary '{outch} (ary '{outch} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{outch} num)) (g2 : exp (ary '{outch} num)) (z2 : exp (ary '{outch} num))
  (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{outch} num)) (gs : exp (ary '{outch} num)) (zs : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  let c1 := Conv4d_3x3_s2 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let sc := Conv4d_1x1_s2 bs ws input in
  let sn := BatchNorm4d sc gs zs eps in
  ReLU4d (Add4d n2 sn).

(* Imperative block: temporaries bt1..bt8, output written in place. *)
Definition basicblock_proj_comm {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{outch} num)) (g1 : exp (ary '{outch} num)) (z1 : exp (ary '{outch} num))
  (w2 : exp (ary '{outch} (ary '{outch} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{outch} num)) (g2 : exp (ary '{outch} num)) (z2 : exp (ary '{outch} num))
  (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{outch} num)) (gs : exp (ary '{outch} num)) (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  (* The shortcut branch is computed (and read) first so that every
     [bind_read] is adjacent to the assignment of the buffer it reads. *)
  : comm :=
  new (fun t6 => seq (Conv4d_1x1_s2_comm bs ws input t6)
  (new (fun t7 => seq (bind_read t6 (fun e6 => BatchNorm4d_comm e6 gs zs eps t7))
       (bind_read t7 (fun e7 =>
  new (fun t1 => seq (Conv4d_3x3_s2_comm b1 w1 input t1)
  (new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
  (new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
  (new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_3x3_s1_comm b2 w2 e3 t4))
  (new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
  (new (fun t8 => seq (bind_read t5 (fun e5 => Add4d_comm e5 e7 t8))
       (bind_read t8 (fun e8 => ReLU4d_comm e8 output))
  ) (acc' (Var "bt8")))
  ) (acc' (Var "bt5")))
  ) (acc' (Var "bt4")))
  ) (acc' (Var "bt3")))
  ) (acc' (Var "bt2")))
  ) (acc' (Var "bt1")))))
  (acc' (Var "bt7")))
  ) (acc' (Var "bt6")).

(* Direct (DPIA-normal) form of the projection block. *)
Definition basicblock_proj_direct {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{outch} num)) (g1 : exp (ary '{outch} num)) (z1 : exp (ary '{outch} num))
  (w2 : exp (ary '{outch} (ary '{outch} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{outch} num)) (g2 : exp (ary '{outch} num)) (z2 : exp (ary '{outch} num))
  (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{outch} num)) (gs : exp (ary '{outch} num)) (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  let c1 := Conv4d_3x3_s2 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let sc := Conv4d_1x1_s2 bs ws input in
  let sn := BatchNorm4d sc gs zs eps in
  let a2 := Add4d n2 sn in
  seq (seq (seq (seq (seq (seq (seq (seq (A(acc' (Var "bt6"), sc))
                                         (A(acc' (Var "bt7"), sn)))
                                      (A(acc' (Var "bt1"), c1)))
                                   (A(acc' (Var "bt2"), n1)))
                                (A(acc' (Var "bt3"), r1)))
                             (A(acc' (Var "bt4"), c2)))
                          (A(acc' (Var "bt5"), n2)))
                    (A(acc' (Var "bt8"), a2)))
       (A(output, ReLU4d a2)).

Lemma basicblock_proj_comm_eq_direct : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{outch} num)) (g1 : exp (ary '{outch} num)) (z1 : exp (ary '{outch} num))
  (w2 : exp (ary '{outch} (ary '{outch} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{outch} num)) (g2 : exp (ary '{outch} num)) (z2 : exp (ary '{outch} num))
  (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{outch} num)) (gs : exp (ary '{outch} num)) (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  basicblock_proj_comm input w1 b1 g1 z1 w2 b2 g2 z2 ws bs gs zs eps output =
  basicblock_proj_direct input w1 b1 g1 z1 w2 b2 g2 z2 ws bs gs zs eps output.
Proof.
  intros.
  unfold basicblock_proj_comm, basicblock_proj_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_3x3_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Add4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness for the projection block. *)
Lemma A_BasicBlock_proj : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (b1 : exp (ary '{outch} num)) (g1 : exp (ary '{outch} num)) (z1 : exp (ary '{outch} num))
  (w2 : exp (ary '{outch} (ary '{outch} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{outch} num)) (g2 : exp (ary '{outch} num)) (z2 : exp (ary '{outch} num))
  (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{outch} num)) (gs : exp (ary '{outch} num)) (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  basicblock_proj_comm input w1 b1 g1 z1 w2 b2 g2 z2 ws bs gs zs eps output rho p =
  A(output, BasicBlock_proj input w1 b1 g1 z1 w2 b2 g2 z2 ws bs gs zs eps) rho p.
Proof.
  intros. rewrite basicblock_proj_comm_eq_direct.
  unfold basicblock_proj_direct, BasicBlock_proj, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* ResNet18 (symbolic spatial size m, symbolic batch and input channels)      *)
(* -------------------------------------------------------------------------- *)

Section ResNet18.
  Context {batch channel m : nat}.
  Context (input : exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num))))).

  (* Stem *)
  Context (c1_w : exp (ary '{64} (ary '{channel} (ary '{7} (ary '{7} num)))))
          (c1_b : exp (ary '{64} num))
          (bn1_g : exp (ary '{64} num)) (bn1_z : exp (ary '{64} num))
          (eps : exp num).

  (* Stage 1, block 1 (identity, 64) *)
  Context (b11_w1 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b11_b1 b11_g1 b11_z1 : exp (ary '{64} num))
          (b11_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b11_b2 b11_g2 b11_z2 : exp (ary '{64} num)).
  (* Stage 1, block 2 (identity, 64) *)
  Context (b12_w1 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b12_b1 b12_g1 b12_z1 : exp (ary '{64} num))
          (b12_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b12_b2 b12_g2 b12_z2 : exp (ary '{64} num)).

  (* Stage 2, block 1 (projection 64 -> 128) *)
  Context (b21_w1 : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b21_b1 b21_g1 b21_z1 : exp (ary '{128} num))
          (b21_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b21_b2 b21_g2 b21_z2 : exp (ary '{128} num))
          (b21_ws : exp (ary '{128} (ary '{64} (ary '{1} (ary '{1} num)))))
          (b21_bs b21_gs b21_zs : exp (ary '{128} num)).
  (* Stage 2, block 2 (identity, 128) *)
  Context (b22_w1 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b22_b1 b22_g1 b22_z1 : exp (ary '{128} num))
          (b22_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b22_b2 b22_g2 b22_z2 : exp (ary '{128} num)).

  (* Stage 3, block 1 (projection 128 -> 256) *)
  Context (b31_w1 : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b31_b1 b31_g1 b31_z1 : exp (ary '{256} num))
          (b31_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b31_b2 b31_g2 b31_z2 : exp (ary '{256} num))
          (b31_ws : exp (ary '{256} (ary '{128} (ary '{1} (ary '{1} num)))))
          (b31_bs b31_gs b31_zs : exp (ary '{256} num)).
  (* Stage 3, block 2 (identity, 256) *)
  Context (b32_w1 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b32_b1 b32_g1 b32_z1 : exp (ary '{256} num))
          (b32_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b32_b2 b32_g2 b32_z2 : exp (ary '{256} num)).

  (* Stage 4, block 1 (projection 256 -> 512) *)
  Context (b41_w1 : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b41_b1 b41_g1 b41_z1 : exp (ary '{512} num))
          (b41_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
          (b41_b2 b41_g2 b41_z2 : exp (ary '{512} num))
          (b41_ws : exp (ary '{512} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b41_bs b41_gs b41_zs : exp (ary '{512} num)).
  (* Stage 4, block 2 (identity, 512) *)
  Context (b42_w1 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
          (b42_b1 b42_g1 b42_z1 : exp (ary '{512} num))
          (b42_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
          (b42_b2 b42_g2 b42_z2 : exp (ary '{512} num)).

  (* Classifier *)
  Context (fc_w : exp (ary '{1000} (ary '{512} num)))
          (fc_b : exp (ary '{1000} num)).

  (* ---------------- Functional ResNet18 (R-version expression) ----------- *)

  Definition ResNet18 : exp (ary '{batch} (ary '{1000} num)) :=
    let x1 := Conv4d_p3_k7_s2 input c1_w c1_b in
    let x2 := BatchNorm4d x1 bn1_g bn1_z eps in
    let x3 := ReLU4d x2 in
    let x4 := Maxpool4d_pad 3 2 1 x3 in
    let x5 := BasicBlock_id x4 b11_w1 b11_b1 b11_g1 b11_z1
                                 b11_w2 b11_b2 b11_g2 b11_z2 eps in
    let x6 := BasicBlock_id x5 b12_w1 b12_b1 b12_g1 b12_z1
                                 b12_w2 b12_b2 b12_g2 b12_z2 eps in
    let x7 := BasicBlock_proj x6 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_ws b21_bs b21_gs b21_zs eps in
    let x8 := BasicBlock_id x7 b22_w1 b22_b1 b22_g1 b22_z1
                                 b22_w2 b22_b2 b22_g2 b22_z2 eps in
    let x9 := BasicBlock_proj x8 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_ws b31_bs b31_gs b31_zs eps in
    let x10 := BasicBlock_id x9 b32_w1 b32_b1 b32_g1 b32_z1
                                  b32_w2 b32_b2 b32_g2 b32_z2 eps in
    let x11 := BasicBlock_proj x10 b41_w1 b41_b1 b41_g1 b41_z1
                                     b41_w2 b41_b2 b41_g2 b41_z2
                                     b41_ws b41_bs b41_gs b41_zs eps in
    let x12 := BasicBlock_id x11 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2 eps in
    let x13 := GlobalAvgPool4d x12 in
    Softmax2d (Linear2d fc_w fc_b x13).

  (* ---------------- Imperative ResNet18 (buffer-layered) ----------------- *)

  Definition resnet18_comm (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
    new (fun l1 => seq (Conv4d_p3_k7_s2_comm input c1_w c1_b l1)
    (new (fun l2 => seq (bind_read l1 (fun e1 => BatchNorm4d_comm e1 bn1_g bn1_z eps l2))
    (new (fun l3 => seq (bind_read l2 (fun e2 => ReLU4d_comm e2 l3))
    (new (fun l4 => seq (bind_read l3 (fun e3 => Maxpool4d_pad_comm 3 2 1 e3 l4))
    (new (fun l5 => seq (bind_read l4 (fun e4 =>
        basicblock_id_comm e4 b11_w1 b11_b1 b11_g1 b11_z1
                             b11_w2 b11_b2 b11_g2 b11_z2 eps l5))
    (new (fun l6 => seq (bind_read l5 (fun e5 =>
        basicblock_id_comm e5 b12_w1 b12_b1 b12_g1 b12_z1
                             b12_w2 b12_b2 b12_g2 b12_z2 eps l6))
    (new (fun l7 => seq (bind_read l6 (fun e6 =>
        basicblock_proj_comm e6 b21_w1 b21_b1 b21_g1 b21_z1
                               b21_w2 b21_b2 b21_g2 b21_z2
                               b21_ws b21_bs b21_gs b21_zs eps l7))
    (new (fun l8 => seq (bind_read l7 (fun e7 =>
        basicblock_id_comm e7 b22_w1 b22_b1 b22_g1 b22_z1
                             b22_w2 b22_b2 b22_g2 b22_z2 eps l8))
    (new (fun l9 => seq (bind_read l8 (fun e8 =>
        basicblock_proj_comm e8 b31_w1 b31_b1 b31_g1 b31_z1
                               b31_w2 b31_b2 b31_g2 b31_z2
                               b31_ws b31_bs b31_gs b31_zs eps l9))
    (new (fun l10 => seq (bind_read l9 (fun e9 =>
        basicblock_id_comm e9 b32_w1 b32_b1 b32_g1 b32_z1
                             b32_w2 b32_b2 b32_g2 b32_z2 eps l10))
    (new (fun l11 => seq (bind_read l10 (fun e10 =>
        basicblock_proj_comm e10 b41_w1 b41_b1 b41_g1 b41_z1
                                b41_w2 b41_b2 b41_g2 b41_z2
                                b41_ws b41_bs b41_gs b41_zs eps l11))
    (new (fun l12 => seq (bind_read l11 (fun e11 =>
        basicblock_id_comm e11 b42_w1 b42_b1 b42_g1 b42_z1
                              b42_w2 b42_b2 b42_g2 b42_z2 eps l12))
    (new (fun l13 => seq (bind_read l12 (fun e12 => GlobalAvgPool4d_comm e12 l13))
         (bind_read l13 (fun e13 => Softmax2d_comm (Linear2d fc_w fc_b e13) output))
    ) (acc' (Var "l13")))
    ) (acc' (Var "l12")))
    ) (acc' (Var "l11")))
    ) (acc' (Var "l10")))
    ) (acc' (Var "l9")))
    ) (acc' (Var "l8")))
    ) (acc' (Var "l7")))
    ) (acc' (Var "l6")))
    ) (acc' (Var "l5")))
    ) (acc' (Var "l4")))
    ) (acc' (Var "l3")))
    ) (acc' (Var "l2")))
    ) (acc' (Var "l1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition resnet18_comm_direct (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
    let x1 := Conv4d_p3_k7_s2 input c1_w c1_b in
    let x2 := BatchNorm4d x1 bn1_g bn1_z eps in
    let x3 := ReLU4d x2 in
    let x4 := Maxpool4d_pad 3 2 1 x3 in
    let x5 := BasicBlock_id x4 b11_w1 b11_b1 b11_g1 b11_z1
                                 b11_w2 b11_b2 b11_g2 b11_z2 eps in
    let x6 := BasicBlock_id x5 b12_w1 b12_b1 b12_g1 b12_z1
                                 b12_w2 b12_b2 b12_g2 b12_z2 eps in
    let x7 := BasicBlock_proj x6 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_ws b21_bs b21_gs b21_zs eps in
    let x8 := BasicBlock_id x7 b22_w1 b22_b1 b22_g1 b22_z1
                                 b22_w2 b22_b2 b22_g2 b22_z2 eps in
    let x9 := BasicBlock_proj x8 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_ws b31_bs b31_gs b31_zs eps in
    let x10 := BasicBlock_id x9 b32_w1 b32_b1 b32_g1 b32_z1
                                  b32_w2 b32_b2 b32_g2 b32_z2 eps in
    let x11 := BasicBlock_proj x10 b41_w1 b41_b1 b41_g1 b41_z1
                                     b41_w2 b41_b2 b41_g2 b41_z2
                                     b41_ws b41_bs b41_gs b41_zs eps in
    let x12 := BasicBlock_id x11 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2 eps in
    let x13 := GlobalAvgPool4d x12 in
    seq (A(acc' (Var "l1"), x1))
    (seq (A(acc' (Var "l2"), x2))
    (seq (A(acc' (Var "l3"), x3))
    (seq (A(acc' (Var "l4"), x4))
    (seq (basicblock_id_direct x4 b11_w1 b11_b1 b11_g1 b11_z1
                                 b11_w2 b11_b2 b11_g2 b11_z2 eps (acc' (Var "l5")))
    (seq (basicblock_id_direct x5 b12_w1 b12_b1 b12_g1 b12_z1
                                 b12_w2 b12_b2 b12_g2 b12_z2 eps (acc' (Var "l6")))
    (seq (basicblock_proj_direct x6 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_ws b21_bs b21_gs b21_zs eps (acc' (Var "l7")))
    (seq (basicblock_id_direct x7 b22_w1 b22_b1 b22_g1 b22_z1
                                 b22_w2 b22_b2 b22_g2 b22_z2 eps (acc' (Var "l8")))
    (seq (basicblock_proj_direct x8 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_ws b31_bs b31_gs b31_zs eps (acc' (Var "l9")))
    (seq (basicblock_id_direct x9 b32_w1 b32_b1 b32_g1 b32_z1
                                  b32_w2 b32_b2 b32_g2 b32_z2 eps (acc' (Var "l10")))
    (seq (basicblock_proj_direct x10 b41_w1 b41_b1 b41_g1 b41_z1
                                     b41_w2 b41_b2 b41_g2 b41_z2
                                     b41_ws b41_bs b41_gs b41_zs eps (acc' (Var "l11")))
    (seq (basicblock_id_direct x11 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2 eps (acc' (Var "l12")))
    (seq (A(acc' (Var "l13"), x13))
         (A(output, Softmax2d (Linear2d fc_w fc_b x13)))
    )))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition r1_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{batch} (ary '{64} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{batch} (ary '{64} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{batch} (ary '{64} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{batch} (ary '{128}
      (ary '{half (s_pool m)} (ary '{half (s_pool m)} num)))) := acc' (Var "l7").
  Definition r8_acc : acc (ary '{batch} (ary '{128}
      (ary '{half (s_pool m)} (ary '{half (s_pool m)} num)))) := acc' (Var "l8").
  Definition r9_acc : acc (ary '{batch} (ary '{256}
      (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num)))) := acc' (Var "l9").
  Definition r10_acc : acc (ary '{batch} (ary '{256}
      (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num)))) := acc' (Var "l10").
  Definition r11_acc : acc (ary '{batch} (ary '{512}
      (ary '{half (half (half (s_pool m)))} (ary '{half (half (half (s_pool m)))} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{batch} (ary '{512}
      (ary '{half (half (half (s_pool m)))} (ary '{half (half (half (s_pool m)))} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{batch} (ary '{512} num)) := acc' (Var "l13").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries bt1..bt8 are shared between blocks and are required to be
     fresh at every type. *)
  Definition resnet18_fresh
    (output : acc (ary '{batch} (ary '{1000} num))) (rho : env) : Prop :=
    StructUndefined r1_acc rho /\ StructUndefined r2_acc rho /\
    StructUndefined r3_acc rho /\ StructUndefined r4_acc rho /\
    StructUndefined r5_acc rho /\ StructUndefined r6_acc rho /\
    StructUndefined r7_acc rho /\ StructUndefined r8_acc rho /\
    StructUndefined r9_acc rho /\ StructUndefined r10_acc rho /\
    StructUndefined r11_acc rho /\ StructUndefined r12_acc rho /\
    StructUndefined r13_acc rho /\
    (forall d : data, StructUndefined (acc' (Var "bt1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt5") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt6") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt7") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt8") : acc d) rho) /\
    (forall p, in_acc p output -> ~ in_acc p r1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r4_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r5_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r6_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r7_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r8_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r9_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r10_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r11_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r12_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r13_acc) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt5") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt6") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt7") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt8") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma resnet18_comm_eq_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num))),
    resnet18_comm output = resnet18_comm_direct output.
  Proof.
    intros.
    unfold resnet18_comm, resnet18_comm_direct,
           basicblock_id_direct, basicblock_proj_direct, new.
    cbv zeta beta.
    rewrite <- A_Conv4d_p3_k7_s2.
    rewrite bind_read_replace_seq.
    rewrite <- A_BatchNorm4d.
    rewrite bind_read_replace_seq.
    rewrite <- A_ReLU4d.
    rewrite bind_read_replace_seq.
    rewrite <- A_Maxpool4d_pad.
    rewrite bind_read_replace_seq.
    rewrite basicblock_id_comm_eq_direct.
    unfold basicblock_id_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_id_comm_eq_direct.
    unfold basicblock_id_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_proj_comm_eq_direct.
    unfold basicblock_proj_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_id_comm_eq_direct.
    unfold basicblock_id_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_proj_comm_eq_direct.
    unfold basicblock_proj_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_id_comm_eq_direct.
    unfold basicblock_id_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_proj_comm_eq_direct.
    unfold basicblock_proj_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite basicblock_id_comm_eq_direct.
    unfold basicblock_id_direct. cbv beta zeta.
    rewrite bind_read_replace_seq_r.
    rewrite <- A_GlobalAvgPool4d.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    reflexivity.
  Qed.

  Lemma A_ResNet18_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    resnet18_fresh output rho ->
    resnet18_comm_direct output rho p = A(output, ResNet18) rho p.
  Proof.
    intros.
    unfold resnet18_comm_direct, ResNet18,
           basicblock_id_direct, basicblock_proj_direct,
           BasicBlock_id, BasicBlock_proj, A.
    cbv zeta beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - reflexivity.
  Qed.

  Theorem A_ResNet18 :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    resnet18_fresh output rho ->
    resnet18_comm output rho p = A(output, ResNet18) rho p.
  Proof.
    intros. rewrite resnet18_comm_eq_direct.
    apply A_ResNet18_direct; assumption.
  Qed.

End ResNet18.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Conv4d_3x3_s1.
Print Assumptions A_Conv4d_3x3_s2.
Print Assumptions A_Conv4d_1x1_s2.
Print Assumptions A_BasicBlock_id.
Print Assumptions A_BasicBlock_proj.
Print Assumptions A_ResNet18.
