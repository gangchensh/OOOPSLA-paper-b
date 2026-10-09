(* DPIA-style end-to-end Leibniz correctness proof for ResNet50 (route A).

   Structure: classic ResNet50 in 4d batched form, spatial size symbolic (m):
     conv1(7x7,p3,s2) - bn - relu - maxpool(3x3,s2,p1)
     stage1: 3 x Bottleneck(64->256,  mid 64;  first block stride-1 projection)
     stage2: 4 x Bottleneck(256->512, mid 128; first block stride-2 projection)
     stage3: 6 x Bottleneck(512->1024,mid 256; first block stride-2 projection)
     stage4: 3 x Bottleneck(1024->2048,mid 512;first block stride-2 projection)
     GlobalAvgPool - fc(1000) - softmax

   Each Bottleneck is
     conv1x1 - bn - relu - conv3x3 - bn - relu - conv1x1 - bn   (main path)
     (+ 1x1 conv - bn on the shortcut for projection blocks;
        stride 2 on the 3x3 conv and the shortcut for downsampling blocks)
     Add(shortcut) - relu.

   The stride-1/stride-2 convolutions reuse the canonical-size variants
   [Conv4d_3x3_s1] / [Conv4d_3x3_s2] / [Conv4d_1x1_s2] (output size
   [half m = (m+1)/2] for stride 2) proved in ResNet18_DPIA.v; the 1x1
   stride-1 same-size variant [Conv4d_1x1_s1] is added here, proved exactly
   like [A_Conv4d].  The stem reuses [Conv4d_p3_k7_s2] and [Maxpool4d_pad].

   As in ResNet18_DPIA.v, each block combinator [bottleneck_*_comm] is proved
   equal to a buffer-free "direct" form ([bottleneck_*_comm_eq_direct]); the
   network-level proof rewrites the comm form to the direct form, and the
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
Require Import Ionia.ResNet18_DPIA.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Conv4d_1x1_s1 : same-size 1x1 convolution, stride 1                         *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_1x1_s1 {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin m1 => mkvSeq (fun j0 : fin m2 =>
      add (sum (mkvSeq (fun c : fin inch =>
            sum (mkvSeq (fun i1 : fin 1 =>
              sum (mkvSeq (fun j1 : fin 1 =>
                mul (pad_idx2d 0 (idx (idx input b) c)
                               (fin2nat i0 + fin2nat i1)
                               (fin2nat j0 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition Conv4d_1x1_s1_comm {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin inch =>
             sum (mkvSeq (fun i1 : fin 1 =>
               sum (mkvSeq (fun j1 : fin 1 =>
                 mul (pad_idx2d 0 (idx (idx input b) c)
                                (fin2nat i0 + fin2nat i1)
                                (fin2nat j0 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_Conv4d_1x1_s1 : forall (batch inch outch m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  A(output, Conv4d_1x1_s1 bias w input) = Conv4d_1x1_s1_comm bias w input output.
Proof.
  intros. unfold Conv4d_1x1_s1, Conv4d_1x1_s1_comm.
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
(* Bottleneck with identity shortcut                                        *)
(* -------------------------------------------------------------------------- *)

Definition Bottleneck_id {batch c cm m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{c} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{c} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_1x1_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c3 := Conv4d_1x1_s1 b3 w3 r2 in
  let n3 := BatchNorm4d c3 g3 z3 eps in
  ReLU4d (Add4d n3 input).

(* Imperative block: temporaries bt1..bt9, output written in place. *)
Definition bottleneck_id_comm {batch c cm m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{c} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{c} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm b1 w1 input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_3x3_s1_comm b2 w2 e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => ReLU4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => Conv4d_1x1_s1_comm b3 w3 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => BatchNorm4d_comm e7 g3 z3 eps t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => Add4d_comm e8 input t9))
     (bind_read t9 (fun e9 => ReLU4d_comm e9 output))
) (acc' (Var "bt9")))
) (acc' (Var "bt8")))
) (acc' (Var "bt7")))
) (acc' (Var "bt6")))
) (acc' (Var "bt5")))
) (acc' (Var "bt4")))
) (acc' (Var "bt3")))
) (acc' (Var "bt2")))
) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition bottleneck_id_direct {batch c cm m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{c} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{c} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c3 := Conv4d_1x1_s1 b3 w3 r2 in
  let n3 := BatchNorm4d c3 g3 z3 eps in
  let a2 := Add4d n3 input in
  seq (seq (seq (seq (seq (seq (seq (seq (seq (A(acc' (Var "bt1"), c1))
                                (A(acc' (Var "bt2"), n1)))
                                (A(acc' (Var "bt3"), r1)))
                                (A(acc' (Var "bt4"), c2)))
                                (A(acc' (Var "bt5"), n2)))
                                (A(acc' (Var "bt6"), r2)))
                                (A(acc' (Var "bt7"), c3)))
                                (A(acc' (Var "bt8"), n3)))
                                (A(acc' (Var "bt9"), a2)))
       (A(output, Bottleneck_id input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps)).

Lemma bottleneck_id_comm_eq_direct : forall (batch c cm m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{c} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{c} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  bottleneck_id_comm input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps output =
  bottleneck_id_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps output.
Proof.
  intros.
  unfold bottleneck_id_comm, bottleneck_id_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Add4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [Bottleneck_id]. *)
Lemma A_Bottleneck_id : forall (batch c cm m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{c} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{c} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  bottleneck_id_comm input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps output rho p =
  A(output, Bottleneck_id input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps) rho p.
Proof.
  intros. rewrite bottleneck_id_comm_eq_direct.
  unfold bottleneck_id_direct, Bottleneck_id, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value.  This lets the network-level proof advance
   past a block without ever unfolding its direct form. *)
Lemma bottleneck_id_direct_read : forall (batch c cm m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{c} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{c} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (bottleneck_id_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (bottleneck_id_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps (acc' q))
      (seq (k (Bottleneck_id input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 eps)) c0).
Proof.
  intros. unfold bottleneck_id_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* Bottleneck with stride-1 projection shortcut (1x1 conv + BN)             *)
(* -------------------------------------------------------------------------- *)

Definition Bottleneck_proj1 {batch inch cm outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_1x1_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c3 := Conv4d_1x1_s1 b3 w3 r2 in
  let n3 := BatchNorm4d c3 g3 z3 eps in
  let sc := Conv4d_1x1_s1 bs ws input in
  let sn := BatchNorm4d sc gs zs eps in
  ReLU4d (Add4d n3 sn).

(* Imperative block: temporaries bt1..bt11, output written in place. *)
Definition bottleneck_proj1_comm {batch inch cm outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t10 => seq (Conv4d_1x1_s1_comm bs ws input t10)
(new (fun t11 => seq (bind_read t10 (fun e10 => BatchNorm4d_comm e10 gs zs eps t11))
     (bind_read t11 (fun e11 =>
  new (fun t1 => seq (Conv4d_1x1_s1_comm b1 w1 input t1)
  (new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
  (new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
  (new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_3x3_s1_comm b2 w2 e3 t4))
  (new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
  (new (fun t6 => seq (bind_read t5 (fun e5 => ReLU4d_comm e5 t6))
  (new (fun t7 => seq (bind_read t6 (fun e6 => Conv4d_1x1_s1_comm b3 w3 e6 t7))
  (new (fun t8 => seq (bind_read t7 (fun e7 => BatchNorm4d_comm e7 g3 z3 eps t8))
  (new (fun t9 => seq (bind_read t8 (fun e8 => Add4d_comm e8 e11 t9))
       (bind_read t9 (fun e9 => ReLU4d_comm e9 output))
  ) (acc' (Var "bt9")))
  ) (acc' (Var "bt8")))
  ) (acc' (Var "bt7")))
  ) (acc' (Var "bt6")))
  ) (acc' (Var "bt5")))
  ) (acc' (Var "bt4")))
  ) (acc' (Var "bt3")))
  ) (acc' (Var "bt2")))
  ) (acc' (Var "bt1")))))
(acc' (Var "bt11")))
) (acc' (Var "bt10")).

(* Direct (DPIA-normal) form of the block. *)
Definition bottleneck_proj1_direct {batch inch cm outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s1 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c3 := Conv4d_1x1_s1 b3 w3 r2 in
  let n3 := BatchNorm4d c3 g3 z3 eps in
  let sc := Conv4d_1x1_s1 bs ws input in
  let sn := BatchNorm4d sc gs zs eps in
  let a2 := Add4d n3 sn in
  seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (A(acc' (Var "bt10"), sc))
                                (A(acc' (Var "bt11"), sn)))
                                (A(acc' (Var "bt1"), c1)))
                                (A(acc' (Var "bt2"), n1)))
                                (A(acc' (Var "bt3"), r1)))
                                (A(acc' (Var "bt4"), c2)))
                                (A(acc' (Var "bt5"), n2)))
                                (A(acc' (Var "bt6"), r2)))
                                (A(acc' (Var "bt7"), c3)))
                                (A(acc' (Var "bt8"), n3)))
                                (A(acc' (Var "bt9"), a2)))
       (A(output, Bottleneck_proj1 input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps)).

Lemma bottleneck_proj1_comm_eq_direct : forall (batch inch cm outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  bottleneck_proj1_comm input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps output =
  bottleneck_proj1_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps output.
Proof.
  intros.
  unfold bottleneck_proj1_comm, bottleneck_proj1_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Add4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [Bottleneck_proj1]. *)
Lemma A_Bottleneck_proj1 : forall (batch inch cm outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  bottleneck_proj1_comm input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps output rho p =
  A(output, Bottleneck_proj1 input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps) rho p.
Proof.
  intros. rewrite bottleneck_proj1_comm_eq_direct.
  unfold bottleneck_proj1_direct, Bottleneck_proj1, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value.  This lets the network-level proof advance
   past a block without ever unfolding its direct form. *)
Lemma bottleneck_proj1_direct_read : forall (batch inch cm outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (bottleneck_proj1_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (bottleneck_proj1_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps (acc' q))
      (seq (k (Bottleneck_proj1 input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps)) c0).
Proof.
  intros. unfold bottleneck_proj1_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* Bottleneck with stride-2 projection shortcut (1x1 conv + BN)             *)
(* -------------------------------------------------------------------------- *)

Definition Bottleneck_proj2 {batch inch cm outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  let c1 := Conv4d_1x1_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s2 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c3 := Conv4d_1x1_s1 b3 w3 r2 in
  let n3 := BatchNorm4d c3 g3 z3 eps in
  let sc := Conv4d_1x1_s2 bs ws input in
  let sn := BatchNorm4d sc gs zs eps in
  ReLU4d (Add4d n3 sn).

(* Imperative block: temporaries bt1..bt11, output written in place. *)
Definition bottleneck_proj2_comm {batch inch cm outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
new (fun t10 => seq (Conv4d_1x1_s2_comm bs ws input t10)
(new (fun t11 => seq (bind_read t10 (fun e10 => BatchNorm4d_comm e10 gs zs eps t11))
     (bind_read t11 (fun e11 =>
  new (fun t1 => seq (Conv4d_1x1_s1_comm b1 w1 input t1)
  (new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
  (new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
  (new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_3x3_s2_comm b2 w2 e3 t4))
  (new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
  (new (fun t6 => seq (bind_read t5 (fun e5 => ReLU4d_comm e5 t6))
  (new (fun t7 => seq (bind_read t6 (fun e6 => Conv4d_1x1_s1_comm b3 w3 e6 t7))
  (new (fun t8 => seq (bind_read t7 (fun e7 => BatchNorm4d_comm e7 g3 z3 eps t8))
  (new (fun t9 => seq (bind_read t8 (fun e8 => Add4d_comm e8 e11 t9))
       (bind_read t9 (fun e9 => ReLU4d_comm e9 output))
  ) (acc' (Var "bt9")))
  ) (acc' (Var "bt8")))
  ) (acc' (Var "bt7")))
  ) (acc' (Var "bt6")))
  ) (acc' (Var "bt5")))
  ) (acc' (Var "bt4")))
  ) (acc' (Var "bt3")))
  ) (acc' (Var "bt2")))
  ) (acc' (Var "bt1")))))
(acc' (Var "bt11")))
) (acc' (Var "bt10")).

(* Direct (DPIA-normal) form of the block. *)
Definition bottleneck_proj2_direct {batch inch cm outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 b1 w1 input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c2 := Conv4d_3x3_s2 b2 w2 r1 in
  let n2 := BatchNorm4d c2 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c3 := Conv4d_1x1_s1 b3 w3 r2 in
  let n3 := BatchNorm4d c3 g3 z3 eps in
  let sc := Conv4d_1x1_s2 bs ws input in
  let sn := BatchNorm4d sc gs zs eps in
  let a2 := Add4d n3 sn in
  seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (A(acc' (Var "bt10"), sc))
                                (A(acc' (Var "bt11"), sn)))
                                (A(acc' (Var "bt1"), c1)))
                                (A(acc' (Var "bt2"), n1)))
                                (A(acc' (Var "bt3"), r1)))
                                (A(acc' (Var "bt4"), c2)))
                                (A(acc' (Var "bt5"), n2)))
                                (A(acc' (Var "bt6"), r2)))
                                (A(acc' (Var "bt7"), c3)))
                                (A(acc' (Var "bt8"), n3)))
                                (A(acc' (Var "bt9"), a2)))
       (A(output, Bottleneck_proj2 input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps)).

Lemma bottleneck_proj2_comm_eq_direct : forall (batch inch cm outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  bottleneck_proj2_comm input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps output =
  bottleneck_proj2_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps output.
Proof.
  intros.
  unfold bottleneck_proj2_comm, bottleneck_proj2_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Add4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [Bottleneck_proj2]. *)
Lemma A_Bottleneck_proj2 : forall (batch inch cm outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  bottleneck_proj2_comm input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps output rho p =
  A(output, Bottleneck_proj2 input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps) rho p.
Proof.
  intros. rewrite bottleneck_proj2_comm_eq_direct.
  unfold bottleneck_proj2_direct, Bottleneck_proj2, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value.  This lets the network-level proof advance
   past a block without ever unfolding its direct form. *)
Lemma bottleneck_proj2_direct_read : forall (batch inch cm outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{cm} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (b1 : exp (ary '{cm} num))
    (g1 : exp (ary '{cm} num))
    (z1 : exp (ary '{cm} num))
    (w2 : exp (ary '{cm} (ary '{cm} (ary '{3} (ary '{3} num)))))
    (b2 : exp (ary '{cm} num))
    (g2 : exp (ary '{cm} num))
    (z2 : exp (ary '{cm} num))
    (w3 : exp (ary '{outch} (ary '{cm} (ary '{1} (ary '{1} num)))))
    (b3 : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
    (ws : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bs : exp (ary '{outch} num))
    (gs : exp (ary '{outch} num))
    (zs : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) -> comm) (c0 : comm),
  seq (bottleneck_proj2_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (bottleneck_proj2_direct input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps (acc' q))
      (seq (k (Bottleneck_proj2 input w1 b1 g1 z1 w2 b2 g2 z2 w3 b3 g3 z3 ws bs gs zs eps)) c0).
Proof.
  intros. unfold bottleneck_proj2_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* ResNet50 (symbolic spatial size m, symbolic batch and input channels)      *)
(* -------------------------------------------------------------------------- *)

Section ResNet50.
  Context {batch channel m : nat}.
  Context (input : exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num))))).

  (* Stem *)
  Context (c1_w : exp (ary '{64} (ary '{channel} (ary '{7} (ary '{7} num)))))
          (c1_b : exp (ary '{64} num))
          (bn1_g : exp (ary '{64} num)) (bn1_z : exp (ary '{64} num))
          (eps : exp num).

  (* Stage 1, block 1 (projection s1, 64 -> 256) *)
  Context (b11_w1 : exp (ary '{64} (ary '{64} (ary '{1} (ary '{1} num)))))
          (b11_b1 b11_g1 b11_z1 : exp (ary '{64} num))
          (b11_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b11_b2 b11_g2 b11_z2 : exp (ary '{64} num))
          (b11_w3 : exp (ary '{256} (ary '{64} (ary '{1} (ary '{1} num)))))
          (b11_b3 b11_g3 b11_z3 : exp (ary '{256} num))
          (b11_ws : exp (ary '{256} (ary '{64} (ary '{1} (ary '{1} num)))))
          (b11_bs b11_gs b11_zs : exp (ary '{256} num)).
  (* Stage 1, block 2 (identity, 256) *)
  Context (b12_w1 : exp (ary '{64} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b12_b1 b12_g1 b12_z1 : exp (ary '{64} num))
          (b12_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b12_b2 b12_g2 b12_z2 : exp (ary '{64} num))
          (b12_w3 : exp (ary '{256} (ary '{64} (ary '{1} (ary '{1} num)))))
          (b12_b3 b12_g3 b12_z3 : exp (ary '{256} num)).
  (* Stage 1, block 3 (identity, 256) *)
  Context (b13_w1 : exp (ary '{64} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b13_b1 b13_g1 b13_z1 : exp (ary '{64} num))
          (b13_w2 : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
          (b13_b2 b13_g2 b13_z2 : exp (ary '{64} num))
          (b13_w3 : exp (ary '{256} (ary '{64} (ary '{1} (ary '{1} num)))))
          (b13_b3 b13_g3 b13_z3 : exp (ary '{256} num)).
  (* Stage 2, block 1 (projection s2, 256 -> 512) *)
  Context (b21_w1 : exp (ary '{128} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b21_b1 b21_g1 b21_z1 : exp (ary '{128} num))
          (b21_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b21_b2 b21_g2 b21_z2 : exp (ary '{128} num))
          (b21_w3 : exp (ary '{512} (ary '{128} (ary '{1} (ary '{1} num)))))
          (b21_b3 b21_g3 b21_z3 : exp (ary '{512} num))
          (b21_ws : exp (ary '{512} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b21_bs b21_gs b21_zs : exp (ary '{512} num)).
  (* Stage 2, block 2 (identity, 512) *)
  Context (b22_w1 : exp (ary '{128} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b22_b1 b22_g1 b22_z1 : exp (ary '{128} num))
          (b22_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b22_b2 b22_g2 b22_z2 : exp (ary '{128} num))
          (b22_w3 : exp (ary '{512} (ary '{128} (ary '{1} (ary '{1} num)))))
          (b22_b3 b22_g3 b22_z3 : exp (ary '{512} num)).
  (* Stage 2, block 3 (identity, 512) *)
  Context (b23_w1 : exp (ary '{128} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b23_b1 b23_g1 b23_z1 : exp (ary '{128} num))
          (b23_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b23_b2 b23_g2 b23_z2 : exp (ary '{128} num))
          (b23_w3 : exp (ary '{512} (ary '{128} (ary '{1} (ary '{1} num)))))
          (b23_b3 b23_g3 b23_z3 : exp (ary '{512} num)).
  (* Stage 2, block 4 (identity, 512) *)
  Context (b24_w1 : exp (ary '{128} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b24_b1 b24_g1 b24_z1 : exp (ary '{128} num))
          (b24_w2 : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
          (b24_b2 b24_g2 b24_z2 : exp (ary '{128} num))
          (b24_w3 : exp (ary '{512} (ary '{128} (ary '{1} (ary '{1} num)))))
          (b24_b3 b24_g3 b24_z3 : exp (ary '{512} num)).
  (* Stage 3, block 1 (projection s2, 512 -> 1024) *)
  Context (b31_w1 : exp (ary '{256} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b31_b1 b31_g1 b31_z1 : exp (ary '{256} num))
          (b31_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b31_b2 b31_g2 b31_z2 : exp (ary '{256} num))
          (b31_w3 : exp (ary '{1024} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b31_b3 b31_g3 b31_z3 : exp (ary '{1024} num))
          (b31_ws : exp (ary '{1024} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b31_bs b31_gs b31_zs : exp (ary '{1024} num)).
  (* Stage 3, block 2 (identity, 1024) *)
  Context (b32_w1 : exp (ary '{256} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b32_b1 b32_g1 b32_z1 : exp (ary '{256} num))
          (b32_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b32_b2 b32_g2 b32_z2 : exp (ary '{256} num))
          (b32_w3 : exp (ary '{1024} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b32_b3 b32_g3 b32_z3 : exp (ary '{1024} num)).
  (* Stage 3, block 3 (identity, 1024) *)
  Context (b33_w1 : exp (ary '{256} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b33_b1 b33_g1 b33_z1 : exp (ary '{256} num))
          (b33_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b33_b2 b33_g2 b33_z2 : exp (ary '{256} num))
          (b33_w3 : exp (ary '{1024} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b33_b3 b33_g3 b33_z3 : exp (ary '{1024} num)).
  (* Stage 3, block 4 (identity, 1024) *)
  Context (b34_w1 : exp (ary '{256} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b34_b1 b34_g1 b34_z1 : exp (ary '{256} num))
          (b34_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b34_b2 b34_g2 b34_z2 : exp (ary '{256} num))
          (b34_w3 : exp (ary '{1024} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b34_b3 b34_g3 b34_z3 : exp (ary '{1024} num)).
  (* Stage 3, block 5 (identity, 1024) *)
  Context (b35_w1 : exp (ary '{256} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b35_b1 b35_g1 b35_z1 : exp (ary '{256} num))
          (b35_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b35_b2 b35_g2 b35_z2 : exp (ary '{256} num))
          (b35_w3 : exp (ary '{1024} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b35_b3 b35_g3 b35_z3 : exp (ary '{1024} num)).
  (* Stage 3, block 6 (identity, 1024) *)
  Context (b36_w1 : exp (ary '{256} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b36_b1 b36_g1 b36_z1 : exp (ary '{256} num))
          (b36_w2 : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
          (b36_b2 b36_g2 b36_z2 : exp (ary '{256} num))
          (b36_w3 : exp (ary '{1024} (ary '{256} (ary '{1} (ary '{1} num)))))
          (b36_b3 b36_g3 b36_z3 : exp (ary '{1024} num)).
  (* Stage 4, block 1 (projection s2, 1024 -> 2048) *)
  Context (b41_w1 : exp (ary '{512} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b41_b1 b41_g1 b41_z1 : exp (ary '{512} num))
          (b41_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
          (b41_b2 b41_g2 b41_z2 : exp (ary '{512} num))
          (b41_w3 : exp (ary '{2048} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b41_b3 b41_g3 b41_z3 : exp (ary '{2048} num))
          (b41_ws : exp (ary '{2048} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (b41_bs b41_gs b41_zs : exp (ary '{2048} num)).
  (* Stage 4, block 2 (identity, 2048) *)
  Context (b42_w1 : exp (ary '{512} (ary '{2048} (ary '{1} (ary '{1} num)))))
          (b42_b1 b42_g1 b42_z1 : exp (ary '{512} num))
          (b42_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
          (b42_b2 b42_g2 b42_z2 : exp (ary '{512} num))
          (b42_w3 : exp (ary '{2048} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b42_b3 b42_g3 b42_z3 : exp (ary '{2048} num)).
  (* Stage 4, block 3 (identity, 2048) *)
  Context (b43_w1 : exp (ary '{512} (ary '{2048} (ary '{1} (ary '{1} num)))))
          (b43_b1 b43_g1 b43_z1 : exp (ary '{512} num))
          (b43_w2 : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
          (b43_b2 b43_g2 b43_z2 : exp (ary '{512} num))
          (b43_w3 : exp (ary '{2048} (ary '{512} (ary '{1} (ary '{1} num)))))
          (b43_b3 b43_g3 b43_z3 : exp (ary '{2048} num)).

  (* Classifier *)
  Context (fc_w : exp (ary '{1000} (ary '{2048} num)))
          (fc_b : exp (ary '{1000} num)).

  (* ---------------- Functional ResNet50 (opaque layer wrappers) -----------
     Each layer value is a separate definition; after the body lemmas they
     are made [Opaque] so that the network-level proofs never inline a layer
     into the next one (quadratic/exponential goal blow-up otherwise). *)

  Definition rn50_x1 := Conv4d_p3_k7_s2 input c1_w c1_b.
  Definition rn50_x2 := BatchNorm4d rn50_x1 bn1_g bn1_z eps.
  Definition rn50_x3 := ReLU4d rn50_x2.
  Definition rn50_x4 := Maxpool4d_pad 3 2 1 rn50_x3.
  Definition rn50_x5 := Bottleneck_proj1 rn50_x4 b11_w1 b11_b1 b11_g1 b11_z1
                                   b11_w2 b11_b2 b11_g2 b11_z2
                                   b11_w3 b11_b3 b11_g3 b11_z3
                                   b11_ws b11_bs b11_gs b11_zs eps.
  Definition rn50_x6 := Bottleneck_id rn50_x5 b12_w1 b12_b1 b12_g1 b12_z1
                                   b12_w2 b12_b2 b12_g2 b12_z2
                                   b12_w3 b12_b3 b12_g3 b12_z3 eps.
  Definition rn50_x7 := Bottleneck_id rn50_x6 b13_w1 b13_b1 b13_g1 b13_z1
                                   b13_w2 b13_b2 b13_g2 b13_z2
                                   b13_w3 b13_b3 b13_g3 b13_z3 eps.
  Definition rn50_x8 := Bottleneck_proj2 rn50_x7 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_w3 b21_b3 b21_g3 b21_z3
                                   b21_ws b21_bs b21_gs b21_zs eps.
  Definition rn50_x9 := Bottleneck_id rn50_x8 b22_w1 b22_b1 b22_g1 b22_z1
                                   b22_w2 b22_b2 b22_g2 b22_z2
                                   b22_w3 b22_b3 b22_g3 b22_z3 eps.
  Definition rn50_x10 := Bottleneck_id rn50_x9 b23_w1 b23_b1 b23_g1 b23_z1
                                   b23_w2 b23_b2 b23_g2 b23_z2
                                   b23_w3 b23_b3 b23_g3 b23_z3 eps.
  Definition rn50_x11 := Bottleneck_id rn50_x10 b24_w1 b24_b1 b24_g1 b24_z1
                                   b24_w2 b24_b2 b24_g2 b24_z2
                                   b24_w3 b24_b3 b24_g3 b24_z3 eps.
  Definition rn50_x12 := Bottleneck_proj2 rn50_x11 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_w3 b31_b3 b31_g3 b31_z3
                                   b31_ws b31_bs b31_gs b31_zs eps.
  Definition rn50_x13 := Bottleneck_id rn50_x12 b32_w1 b32_b1 b32_g1 b32_z1
                                   b32_w2 b32_b2 b32_g2 b32_z2
                                   b32_w3 b32_b3 b32_g3 b32_z3 eps.
  Definition rn50_x14 := Bottleneck_id rn50_x13 b33_w1 b33_b1 b33_g1 b33_z1
                                   b33_w2 b33_b2 b33_g2 b33_z2
                                   b33_w3 b33_b3 b33_g3 b33_z3 eps.
  Definition rn50_x15 := Bottleneck_id rn50_x14 b34_w1 b34_b1 b34_g1 b34_z1
                                   b34_w2 b34_b2 b34_g2 b34_z2
                                   b34_w3 b34_b3 b34_g3 b34_z3 eps.
  Definition rn50_x16 := Bottleneck_id rn50_x15 b35_w1 b35_b1 b35_g1 b35_z1
                                   b35_w2 b35_b2 b35_g2 b35_z2
                                   b35_w3 b35_b3 b35_g3 b35_z3 eps.
  Definition rn50_x17 := Bottleneck_id rn50_x16 b36_w1 b36_b1 b36_g1 b36_z1
                                   b36_w2 b36_b2 b36_g2 b36_z2
                                   b36_w3 b36_b3 b36_g3 b36_z3 eps.
  Definition rn50_x18 := Bottleneck_proj2 rn50_x17 b41_w1 b41_b1 b41_g1 b41_z1
                                   b41_w2 b41_b2 b41_g2 b41_z2
                                   b41_w3 b41_b3 b41_g3 b41_z3
                                   b41_ws b41_bs b41_gs b41_zs eps.
  Definition rn50_x19 := Bottleneck_id rn50_x18 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2
                                   b42_w3 b42_b3 b42_g3 b42_z3 eps.
  Definition rn50_x20 := Bottleneck_id rn50_x19 b43_w1 b43_b1 b43_g1 b43_z1
                                   b43_w2 b43_b2 b43_g2 b43_z2
                                   b43_w3 b43_b3 b43_g3 b43_z3 eps.
  Definition rn50_x21 := GlobalAvgPool4d rn50_x20.
  Definition rn50_x22 := Softmax2d (Linear2d fc_w fc_b rn50_x21).

  Lemma rn50_x1_body : rn50_x1 = Conv4d_p3_k7_s2 input c1_w c1_b.
  Proof. reflexivity. Qed.
  Lemma rn50_x2_body : rn50_x2 = BatchNorm4d rn50_x1 bn1_g bn1_z eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x3_body : rn50_x3 = ReLU4d rn50_x2.
  Proof. reflexivity. Qed.
  Lemma rn50_x4_body : rn50_x4 = Maxpool4d_pad 3 2 1 rn50_x3.
  Proof. reflexivity. Qed.
  Lemma rn50_x5_body : rn50_x5 = Bottleneck_proj1 rn50_x4 b11_w1 b11_b1 b11_g1 b11_z1
                                   b11_w2 b11_b2 b11_g2 b11_z2
                                   b11_w3 b11_b3 b11_g3 b11_z3
                                   b11_ws b11_bs b11_gs b11_zs eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x6_body : rn50_x6 = Bottleneck_id rn50_x5 b12_w1 b12_b1 b12_g1 b12_z1
                                   b12_w2 b12_b2 b12_g2 b12_z2
                                   b12_w3 b12_b3 b12_g3 b12_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x7_body : rn50_x7 = Bottleneck_id rn50_x6 b13_w1 b13_b1 b13_g1 b13_z1
                                   b13_w2 b13_b2 b13_g2 b13_z2
                                   b13_w3 b13_b3 b13_g3 b13_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x8_body : rn50_x8 = Bottleneck_proj2 rn50_x7 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_w3 b21_b3 b21_g3 b21_z3
                                   b21_ws b21_bs b21_gs b21_zs eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x9_body : rn50_x9 = Bottleneck_id rn50_x8 b22_w1 b22_b1 b22_g1 b22_z1
                                   b22_w2 b22_b2 b22_g2 b22_z2
                                   b22_w3 b22_b3 b22_g3 b22_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x10_body : rn50_x10 = Bottleneck_id rn50_x9 b23_w1 b23_b1 b23_g1 b23_z1
                                   b23_w2 b23_b2 b23_g2 b23_z2
                                   b23_w3 b23_b3 b23_g3 b23_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x11_body : rn50_x11 = Bottleneck_id rn50_x10 b24_w1 b24_b1 b24_g1 b24_z1
                                   b24_w2 b24_b2 b24_g2 b24_z2
                                   b24_w3 b24_b3 b24_g3 b24_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x12_body : rn50_x12 = Bottleneck_proj2 rn50_x11 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_w3 b31_b3 b31_g3 b31_z3
                                   b31_ws b31_bs b31_gs b31_zs eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x13_body : rn50_x13 = Bottleneck_id rn50_x12 b32_w1 b32_b1 b32_g1 b32_z1
                                   b32_w2 b32_b2 b32_g2 b32_z2
                                   b32_w3 b32_b3 b32_g3 b32_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x14_body : rn50_x14 = Bottleneck_id rn50_x13 b33_w1 b33_b1 b33_g1 b33_z1
                                   b33_w2 b33_b2 b33_g2 b33_z2
                                   b33_w3 b33_b3 b33_g3 b33_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x15_body : rn50_x15 = Bottleneck_id rn50_x14 b34_w1 b34_b1 b34_g1 b34_z1
                                   b34_w2 b34_b2 b34_g2 b34_z2
                                   b34_w3 b34_b3 b34_g3 b34_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x16_body : rn50_x16 = Bottleneck_id rn50_x15 b35_w1 b35_b1 b35_g1 b35_z1
                                   b35_w2 b35_b2 b35_g2 b35_z2
                                   b35_w3 b35_b3 b35_g3 b35_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x17_body : rn50_x17 = Bottleneck_id rn50_x16 b36_w1 b36_b1 b36_g1 b36_z1
                                   b36_w2 b36_b2 b36_g2 b36_z2
                                   b36_w3 b36_b3 b36_g3 b36_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x18_body : rn50_x18 = Bottleneck_proj2 rn50_x17 b41_w1 b41_b1 b41_g1 b41_z1
                                   b41_w2 b41_b2 b41_g2 b41_z2
                                   b41_w3 b41_b3 b41_g3 b41_z3
                                   b41_ws b41_bs b41_gs b41_zs eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x19_body : rn50_x19 = Bottleneck_id rn50_x18 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2
                                   b42_w3 b42_b3 b42_g3 b42_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x20_body : rn50_x20 = Bottleneck_id rn50_x19 b43_w1 b43_b1 b43_g1 b43_z1
                                   b43_w2 b43_b2 b43_g2 b43_z2
                                   b43_w3 b43_b3 b43_g3 b43_z3 eps.
  Proof. reflexivity. Qed.
  Lemma rn50_x21_body : rn50_x21 = GlobalAvgPool4d rn50_x20.
  Proof. reflexivity. Qed.
  Lemma rn50_x22_body : rn50_x22 = Softmax2d (Linear2d fc_w fc_b rn50_x21).
  Proof. reflexivity. Qed.

  Opaque rn50_x1 rn50_x2 rn50_x3 rn50_x4 rn50_x5 rn50_x6 rn50_x7 rn50_x8 rn50_x9 rn50_x10 rn50_x11 rn50_x12 rn50_x13 rn50_x14 rn50_x15 rn50_x16 rn50_x17 rn50_x18 rn50_x19 rn50_x20 rn50_x21 rn50_x22.

  Definition ResNet50 : exp (ary '{batch} (ary '{1000} num)) := rn50_x22.

  (* ---------------- Imperative ResNet50 (buffer-layered) ----------------- *)

  Definition resnet50_comm (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
new (fun t1 => seq (Conv4d_p3_k7_s2_comm input c1_w c1_b t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 bn1_g bn1_z eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Maxpool4d_pad_comm 3 2 1 e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 =>
        bottleneck_proj1_comm e4 b11_w1 b11_b1 b11_g1 b11_z1
                                   b11_w2 b11_b2 b11_g2 b11_z2
                                   b11_w3 b11_b3 b11_g3 b11_z3
                                   b11_ws b11_bs b11_gs b11_zs eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 =>
        bottleneck_id_comm e5 b12_w1 b12_b1 b12_g1 b12_z1
                                   b12_w2 b12_b2 b12_g2 b12_z2
                                   b12_w3 b12_b3 b12_g3 b12_z3 eps t6))
(new (fun t7 => seq (bind_read t6 (fun e6 =>
        bottleneck_id_comm e6 b13_w1 b13_b1 b13_g1 b13_z1
                                   b13_w2 b13_b2 b13_g2 b13_z2
                                   b13_w3 b13_b3 b13_g3 b13_z3 eps t7))
(new (fun t8 => seq (bind_read t7 (fun e7 =>
        bottleneck_proj2_comm e7 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_w3 b21_b3 b21_g3 b21_z3
                                   b21_ws b21_bs b21_gs b21_zs eps t8))
(new (fun t9 => seq (bind_read t8 (fun e8 =>
        bottleneck_id_comm e8 b22_w1 b22_b1 b22_g1 b22_z1
                                   b22_w2 b22_b2 b22_g2 b22_z2
                                   b22_w3 b22_b3 b22_g3 b22_z3 eps t9))
(new (fun t10 => seq (bind_read t9 (fun e9 =>
        bottleneck_id_comm e9 b23_w1 b23_b1 b23_g1 b23_z1
                                   b23_w2 b23_b2 b23_g2 b23_z2
                                   b23_w3 b23_b3 b23_g3 b23_z3 eps t10))
(new (fun t11 => seq (bind_read t10 (fun e10 =>
        bottleneck_id_comm e10 b24_w1 b24_b1 b24_g1 b24_z1
                                   b24_w2 b24_b2 b24_g2 b24_z2
                                   b24_w3 b24_b3 b24_g3 b24_z3 eps t11))
(new (fun t12 => seq (bind_read t11 (fun e11 =>
        bottleneck_proj2_comm e11 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_w3 b31_b3 b31_g3 b31_z3
                                   b31_ws b31_bs b31_gs b31_zs eps t12))
(new (fun t13 => seq (bind_read t12 (fun e12 =>
        bottleneck_id_comm e12 b32_w1 b32_b1 b32_g1 b32_z1
                                   b32_w2 b32_b2 b32_g2 b32_z2
                                   b32_w3 b32_b3 b32_g3 b32_z3 eps t13))
(new (fun t14 => seq (bind_read t13 (fun e13 =>
        bottleneck_id_comm e13 b33_w1 b33_b1 b33_g1 b33_z1
                                   b33_w2 b33_b2 b33_g2 b33_z2
                                   b33_w3 b33_b3 b33_g3 b33_z3 eps t14))
(new (fun t15 => seq (bind_read t14 (fun e14 =>
        bottleneck_id_comm e14 b34_w1 b34_b1 b34_g1 b34_z1
                                   b34_w2 b34_b2 b34_g2 b34_z2
                                   b34_w3 b34_b3 b34_g3 b34_z3 eps t15))
(new (fun t16 => seq (bind_read t15 (fun e15 =>
        bottleneck_id_comm e15 b35_w1 b35_b1 b35_g1 b35_z1
                                   b35_w2 b35_b2 b35_g2 b35_z2
                                   b35_w3 b35_b3 b35_g3 b35_z3 eps t16))
(new (fun t17 => seq (bind_read t16 (fun e16 =>
        bottleneck_id_comm e16 b36_w1 b36_b1 b36_g1 b36_z1
                                   b36_w2 b36_b2 b36_g2 b36_z2
                                   b36_w3 b36_b3 b36_g3 b36_z3 eps t17))
(new (fun t18 => seq (bind_read t17 (fun e17 =>
        bottleneck_proj2_comm e17 b41_w1 b41_b1 b41_g1 b41_z1
                                   b41_w2 b41_b2 b41_g2 b41_z2
                                   b41_w3 b41_b3 b41_g3 b41_z3
                                   b41_ws b41_bs b41_gs b41_zs eps t18))
(new (fun t19 => seq (bind_read t18 (fun e18 =>
        bottleneck_id_comm e18 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2
                                   b42_w3 b42_b3 b42_g3 b42_z3 eps t19))
(new (fun t20 => seq (bind_read t19 (fun e19 =>
        bottleneck_id_comm e19 b43_w1 b43_b1 b43_g1 b43_z1
                                   b43_w2 b43_b2 b43_g2 b43_z2
                                   b43_w3 b43_b3 b43_g3 b43_z3 eps t20))
(new (fun t21 => seq (bind_read t20 (fun e20 => GlobalAvgPool4d_comm e20 t21))
     (bind_read t21 (fun e21 => Softmax2d_comm (Linear2d fc_w fc_b e21) output))
) (acc' (Var "l21")))
) (acc' (Var "l20")))
) (acc' (Var "l19")))
) (acc' (Var "l18")))
) (acc' (Var "l17")))
) (acc' (Var "l16")))
) (acc' (Var "l15")))
) (acc' (Var "l14")))
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

  Definition resnet50_comm_direct (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
    seq (A(acc' (Var "l1"), rn50_x1))
    (seq (A(acc' (Var "l2"), rn50_x2))
    (seq (A(acc' (Var "l3"), rn50_x3))
    (seq (A(acc' (Var "l4"), rn50_x4))
    (seq (bottleneck_proj1_direct rn50_x4 b11_w1 b11_b1 b11_g1 b11_z1
                                   b11_w2 b11_b2 b11_g2 b11_z2
                                   b11_w3 b11_b3 b11_g3 b11_z3
                                   b11_ws b11_bs b11_gs b11_zs eps (acc' (Var "l5")))
    (seq (bottleneck_id_direct rn50_x5 b12_w1 b12_b1 b12_g1 b12_z1
                                   b12_w2 b12_b2 b12_g2 b12_z2
                                   b12_w3 b12_b3 b12_g3 b12_z3 eps (acc' (Var "l6")))
    (seq (bottleneck_id_direct rn50_x6 b13_w1 b13_b1 b13_g1 b13_z1
                                   b13_w2 b13_b2 b13_g2 b13_z2
                                   b13_w3 b13_b3 b13_g3 b13_z3 eps (acc' (Var "l7")))
    (seq (bottleneck_proj2_direct rn50_x7 b21_w1 b21_b1 b21_g1 b21_z1
                                   b21_w2 b21_b2 b21_g2 b21_z2
                                   b21_w3 b21_b3 b21_g3 b21_z3
                                   b21_ws b21_bs b21_gs b21_zs eps (acc' (Var "l8")))
    (seq (bottleneck_id_direct rn50_x8 b22_w1 b22_b1 b22_g1 b22_z1
                                   b22_w2 b22_b2 b22_g2 b22_z2
                                   b22_w3 b22_b3 b22_g3 b22_z3 eps (acc' (Var "l9")))
    (seq (bottleneck_id_direct rn50_x9 b23_w1 b23_b1 b23_g1 b23_z1
                                   b23_w2 b23_b2 b23_g2 b23_z2
                                   b23_w3 b23_b3 b23_g3 b23_z3 eps (acc' (Var "l10")))
    (seq (bottleneck_id_direct rn50_x10 b24_w1 b24_b1 b24_g1 b24_z1
                                   b24_w2 b24_b2 b24_g2 b24_z2
                                   b24_w3 b24_b3 b24_g3 b24_z3 eps (acc' (Var "l11")))
    (seq (bottleneck_proj2_direct rn50_x11 b31_w1 b31_b1 b31_g1 b31_z1
                                   b31_w2 b31_b2 b31_g2 b31_z2
                                   b31_w3 b31_b3 b31_g3 b31_z3
                                   b31_ws b31_bs b31_gs b31_zs eps (acc' (Var "l12")))
    (seq (bottleneck_id_direct rn50_x12 b32_w1 b32_b1 b32_g1 b32_z1
                                   b32_w2 b32_b2 b32_g2 b32_z2
                                   b32_w3 b32_b3 b32_g3 b32_z3 eps (acc' (Var "l13")))
    (seq (bottleneck_id_direct rn50_x13 b33_w1 b33_b1 b33_g1 b33_z1
                                   b33_w2 b33_b2 b33_g2 b33_z2
                                   b33_w3 b33_b3 b33_g3 b33_z3 eps (acc' (Var "l14")))
    (seq (bottleneck_id_direct rn50_x14 b34_w1 b34_b1 b34_g1 b34_z1
                                   b34_w2 b34_b2 b34_g2 b34_z2
                                   b34_w3 b34_b3 b34_g3 b34_z3 eps (acc' (Var "l15")))
    (seq (bottleneck_id_direct rn50_x15 b35_w1 b35_b1 b35_g1 b35_z1
                                   b35_w2 b35_b2 b35_g2 b35_z2
                                   b35_w3 b35_b3 b35_g3 b35_z3 eps (acc' (Var "l16")))
    (seq (bottleneck_id_direct rn50_x16 b36_w1 b36_b1 b36_g1 b36_z1
                                   b36_w2 b36_b2 b36_g2 b36_z2
                                   b36_w3 b36_b3 b36_g3 b36_z3 eps (acc' (Var "l17")))
    (seq (bottleneck_proj2_direct rn50_x17 b41_w1 b41_b1 b41_g1 b41_z1
                                   b41_w2 b41_b2 b41_g2 b41_z2
                                   b41_w3 b41_b3 b41_g3 b41_z3
                                   b41_ws b41_bs b41_gs b41_zs eps (acc' (Var "l18")))
    (seq (bottleneck_id_direct rn50_x18 b42_w1 b42_b1 b42_g1 b42_z1
                                   b42_w2 b42_b2 b42_g2 b42_z2
                                   b42_w3 b42_b3 b42_g3 b42_z3 eps (acc' (Var "l19")))
    (seq (bottleneck_id_direct rn50_x19 b43_w1 b43_b1 b43_g1 b43_z1
                                   b43_w2 b43_b2 b43_g2 b43_z2
                                   b43_w3 b43_b3 b43_g3 b43_z3 eps (acc' (Var "l20")))
    (seq (A(acc' (Var "l21"), rn50_x21))
    ((A(output, rn50_x22))))))))))))))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition r1_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{batch} (ary '{64} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{batch} (ary '{256} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{batch} (ary '{256} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{batch} (ary '{256} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l7").
  Definition r8_acc : acc (ary '{batch} (ary '{512} (ary '{half (s_pool m)} (ary '{half (s_pool m)} num))))
    := acc' (Var "l8").
  Definition r9_acc : acc (ary '{batch} (ary '{512} (ary '{half (s_pool m)} (ary '{half (s_pool m)} num))))
    := acc' (Var "l9").
  Definition r10_acc : acc (ary '{batch} (ary '{512} (ary '{half (s_pool m)} (ary '{half (s_pool m)} num))))
    := acc' (Var "l10").
  Definition r11_acc : acc (ary '{batch} (ary '{512} (ary '{half (s_pool m)} (ary '{half (s_pool m)} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{batch} (ary '{1024} (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{batch} (ary '{1024} (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num))))
    := acc' (Var "l13").
  Definition r14_acc : acc (ary '{batch} (ary '{1024} (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num))))
    := acc' (Var "l14").
  Definition r15_acc : acc (ary '{batch} (ary '{1024} (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num))))
    := acc' (Var "l15").
  Definition r16_acc : acc (ary '{batch} (ary '{1024} (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num))))
    := acc' (Var "l16").
  Definition r17_acc : acc (ary '{batch} (ary '{1024} (ary '{half (half (s_pool m))} (ary '{half (half (s_pool m))} num))))
    := acc' (Var "l17").
  Definition r18_acc : acc (ary '{batch} (ary '{2048} (ary '{half (half (half (s_pool m)))} (ary '{half (half (half (s_pool m)))} num))))
    := acc' (Var "l18").
  Definition r19_acc : acc (ary '{batch} (ary '{2048} (ary '{half (half (half (s_pool m)))} (ary '{half (half (half (s_pool m)))} num))))
    := acc' (Var "l19").
  Definition r20_acc : acc (ary '{batch} (ary '{2048} (ary '{half (half (half (s_pool m)))} (ary '{half (half (half (s_pool m)))} num))))
    := acc' (Var "l20").
  Definition r21_acc : acc (ary '{batch} (ary '{2048} num))
    := acc' (Var "l21").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries bt1..bt11 are shared between blocks and are required to be
     fresh at every type. *)
  Definition resnet50_fresh
    (output : acc (ary '{batch} (ary '{1000} num))) (rho : env) : Prop :=
    StructUndefined r1_acc rho /\
    StructUndefined r2_acc rho /\
    StructUndefined r3_acc rho /\
    StructUndefined r4_acc rho /\
    StructUndefined r5_acc rho /\
    StructUndefined r6_acc rho /\
    StructUndefined r7_acc rho /\
    StructUndefined r8_acc rho /\
    StructUndefined r9_acc rho /\
    StructUndefined r10_acc rho /\
    StructUndefined r11_acc rho /\
    StructUndefined r12_acc rho /\
    StructUndefined r13_acc rho /\
    StructUndefined r14_acc rho /\
    StructUndefined r15_acc rho /\
    StructUndefined r16_acc rho /\
    StructUndefined r17_acc rho /\
    StructUndefined r18_acc rho /\
    StructUndefined r19_acc rho /\
    StructUndefined r20_acc rho /\
    StructUndefined r21_acc rho /\
    (forall d : data, StructUndefined (acc' (Var "bt1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt5") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt6") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt7") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt8") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt9") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt10") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt11") : acc d) rho) /\
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
    (forall p, in_acc p output -> ~ in_acc p r14_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r15_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r16_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r17_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r18_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r19_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r20_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r21_acc) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt5") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt6") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt7") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt8") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt9") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt10") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt11") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  (* The proof keeps the goal small throughout: layer values are folded to
     their opaque [rn50_xK] constants as soon as they are assigned, and block
     direct forms are never unfolded at the network level
     ([bottleneck_*_direct_read] advances past them). *)
  Lemma resnet50_comm_eq_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num))),
    resnet50_comm output = resnet50_comm_direct output.
  Proof.
    intros.
    unfold resnet50_comm, resnet50_comm_direct, new.
    cbv beta.
    rewrite <- A_Conv4d_p3_k7_s2.
    rewrite <- rn50_x1_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_BatchNorm4d.
    rewrite bind_read_replace_seq.
    rewrite <- rn50_x2_body.
    rewrite <- A_ReLU4d.
    rewrite bind_read_replace_seq.
    rewrite <- rn50_x3_body.
    rewrite <- A_Maxpool4d_pad.
    rewrite bind_read_replace_seq.
    rewrite <- rn50_x4_body.
    rewrite bottleneck_proj1_comm_eq_direct.
    rewrite bottleneck_proj1_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x5_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x6_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_proj2_comm_eq_direct.
    rewrite <- rn50_x7_body.
    rewrite bottleneck_proj2_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x8_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x9_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x10_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_proj2_comm_eq_direct.
    rewrite <- rn50_x11_body.
    rewrite bottleneck_proj2_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x12_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x13_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x14_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x15_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x16_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_proj2_comm_eq_direct.
    rewrite <- rn50_x17_body.
    rewrite bottleneck_proj2_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x18_body.
    rewrite bottleneck_id_direct_read.
    rewrite bottleneck_id_comm_eq_direct.
    rewrite <- rn50_x19_body.
    rewrite bottleneck_id_direct_read.
    rewrite <- rn50_x20_body.
    rewrite <- A_GlobalAvgPool4d.
    rewrite <- rn50_x21_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    rewrite <- rn50_x22_body.
    reflexivity.
  Qed.

  Lemma A_ResNet50_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    resnet50_fresh output rho ->
    resnet50_comm_direct output rho p = A(output, ResNet50) rho p.
  Proof.
    intros.
    unfold resnet50_comm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold ResNet50. reflexivity.
  Qed.

  Theorem A_ResNet50 :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    resnet50_fresh output rho ->
    resnet50_comm output rho p = A(output, ResNet50) rho p.
  Proof.
    intros. rewrite resnet50_comm_eq_direct.
    apply A_ResNet50_direct; assumption.
  Qed.

End ResNet50.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Conv4d_1x1_s1.
Print Assumptions A_Bottleneck_id.
Print Assumptions A_Bottleneck_proj1.
Print Assumptions A_Bottleneck_proj2.
Print Assumptions A_ResNet50.
