(* DPIA-style end-to-end Leibniz correctness proof for DenseNet121 (route A).

   Structure: classic DenseNet121 in 4d batched form, spatial size symbolic (m):
     conv1(7x7,p3,s2) - bn - relu - maxpool(3x3,s2,p1)
     DenseBlock1: 6  x DenseLayer(64  +32 per layer; in 64,   out 256)
     Transition1: bn - relu - conv1x1(256->128) - avgpool(2x2,s2)
     DenseBlock2: 12 x DenseLayer(128 +32 per layer; in 128,  out 512)
     Transition2: bn - relu - conv1x1(512->256) - avgpool(2x2,s2)
     DenseBlock3: 24 x DenseLayer(256 +32 per layer; in 256,  out 1024)
     Transition3: bn - relu - conv1x1(1024->512) - avgpool(2x2,s2)
     DenseBlock4: 16 x DenseLayer(512 +32 per layer; in 512,  out 1024)
     GlobalAvgPool - fc(1000) - softmax

   Each DenseLayer (growth rate k=32, bottleneck 4k=128) is
     bn - relu - conv1x1(128) - bn - relu - conv3x3(32)   (new features)
     Concat4d(input, new)                                  (channel append)
   so layer j of a block reads the whole accumulated feature tensor and
   writes a fresh buffer with 32 more channels.  Each Transition is
     bn - relu - conv1x1(compression) - avgpool(2x2, s2).

   As in ResNet50_DPIA.v, each block combinator is proved equal to a
   buffer-free "direct" form ([dense_layer_comm_eq_direct],
   [transition_comm_eq_direct]); the network-level proof rewrites the comm
   form to the direct form, folds each layer value to its opaque [dn_xK]
   constant, and observes that the direct form at an output path equals the
   functional network.  The 1x1/3x3 convolutions reuse [Conv4d_1x1_s1]
   (ResNet50_DPIA.v) and [Conv4d_3x3_s1] (ResNet18_DPIA.v); the channel
   concatenation reuses [Concat4d] (Ops_Concat.v). *)

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
Require Import Ionia.Ops_Concat.
Require Import Ionia.ResNet18_DPIA.
Require Import Ionia.ResNet50_DPIA.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* DenseLayer : bn-relu-conv1x1(4k) - bn-relu-conv3x3(k) - Concat (k = 32)     *)
(* -------------------------------------------------------------------------- *)

Definition DenseLayer {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{128} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{128} num))
  (g2 : exp (ary '{128} num))
  (z2 : exp (ary '{128} num))
  (w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{32} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{(c + 32)} (ary '{m1} (ary '{m2} num)))) :=
  let n1 := BatchNorm4d input g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c1 := Conv4d_1x1_s1 b1 w1 r1 in
  let n2 := BatchNorm4d c1 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c2 := Conv4d_3x3_s1 b2 w2 r2 in
  Concat4d input c2.

(* Imperative block: temporaries dt1..dt6, concatenated output written to a
   fresh buffer (the accumulated feature tensor grows by 32 channels). *)
Definition dense_layer_comm {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{128} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{128} num))
  (g2 : exp (ary '{128} num))
  (z2 : exp (ary '{128} num))
  (w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{32} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{(c + 32)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (BatchNorm4d_comm input g1 z1 eps t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => ReLU4d_comm e1 t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Conv4d_1x1_s1_comm b1 w1 e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => BatchNorm4d_comm e3 g2 z2 eps t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => ReLU4d_comm e4 t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Conv4d_3x3_s1_comm b2 w2 e5 t6))
     (bind_read t6 (fun e6 => Concat4d_comm input e6 output))
) (acc' (Var "dt6")))
) (acc' (Var "dt5")))
) (acc' (Var "dt4")))
) (acc' (Var "dt3")))
) (acc' (Var "dt2")))
) (acc' (Var "dt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition dense_layer_direct {batch c m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{128} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{128} num))
  (g2 : exp (ary '{128} num))
  (z2 : exp (ary '{128} num))
  (w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{32} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{(c + 32)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let n1 := BatchNorm4d input g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c1 := Conv4d_1x1_s1 b1 w1 r1 in
  let n2 := BatchNorm4d c1 g2 z2 eps in
  let r2 := ReLU4d n2 in
  let c2 := Conv4d_3x3_s1 b2 w2 r2 in
  seq (seq (seq (seq (seq (seq (A(acc' (Var "dt1"), n1))
                                (A(acc' (Var "dt2"), r1)))
                                (A(acc' (Var "dt3"), c1)))
                                (A(acc' (Var "dt4"), n2)))
                                (A(acc' (Var "dt5"), r2)))
                                (A(acc' (Var "dt6"), c2)))
       (A(output, DenseLayer input g1 z1 w1 b1 g2 z2 w2 b2 eps)).

Lemma dense_layer_comm_eq_direct : forall (batch c m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{128} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{128} num))
  (g2 : exp (ary '{128} num))
  (z2 : exp (ary '{128} num))
  (w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{32} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{(c + 32)} (ary '{m1} (ary '{m2} num))))),
  dense_layer_comm input g1 z1 w1 b1 g2 z2 w2 b2 eps output =
  dense_layer_direct input g1 z1 w1 b1 g2 z2 w2 b2 eps output.
Proof.
  intros.
  unfold dense_layer_comm, dense_layer_direct, new.
  cbv zeta beta.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace.
  rewrite <- A_Concat4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [DenseLayer]. *)
Lemma A_DenseLayer : forall (batch c m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{128} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{128} num))
  (g2 : exp (ary '{128} num))
  (z2 : exp (ary '{128} num))
  (w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{32} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{(c + 32)} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  dense_layer_comm input g1 z1 w1 b1 g2 z2 w2 b2 eps output rho p =
  A(output, DenseLayer input g1 z1 w1 b1 g2 z2 w2 b2 eps) rho p.
Proof.
  intros. rewrite dense_layer_comm_eq_direct.
  unfold dense_layer_direct, DenseLayer, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma dense_layer_direct_read : forall (batch c m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{128} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{128} num))
  (g2 : exp (ary '{128} num))
  (z2 : exp (ary '{128} num))
  (w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{32} num))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{batch} (ary '{(c + 32)} (ary '{m1} (ary '{m2} num)))) -> comm)
  (c0 : comm),
  seq (dense_layer_direct input g1 z1 w1 b1 g2 z2 w2 b2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (dense_layer_direct input g1 z1 w1 b1 g2 z2 w2 b2 eps (acc' q))
      (seq (k (DenseLayer input g1 z1 w1 b1 g2 z2 w2 b2 eps)) c0).
Proof.
  intros. unfold dense_layer_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* Transition : bn - relu - conv1x1(compression) - avgpool(2x2, s2)            *)
(* -------------------------------------------------------------------------- *)

Definition Transition {batch c co m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{co} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{co} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{co} (ary '{(m1 / 2)} (ary '{(m2 / 2)} num)))) :=
  let n1 := BatchNorm4d input g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c1 := Conv4d_1x1_s1 b1 w1 r1 in
  Avgpool4d 2 c1.

(* Imperative block: temporaries dt1..dt3, output written in place. *)
Definition transition_comm {batch c co m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{co} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{co} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{co} (ary '{(m1 / 2)} (ary '{(m2 / 2)} num)))))
  : comm :=
new (fun t1 => seq (BatchNorm4d_comm input g1 z1 eps t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => ReLU4d_comm e1 t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Conv4d_1x1_s1_comm b1 w1 e2 t3))
     (bind_read t3 (fun e3 => Avgpool4d_comm 2 e3 output))
) (acc' (Var "dt3")))
) (acc' (Var "dt2")))
) (acc' (Var "dt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition transition_direct {batch c co m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{co} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{co} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{co} (ary '{(m1 / 2)} (ary '{(m2 / 2)} num)))))
  : comm :=
  let n1 := BatchNorm4d input g1 z1 eps in
  let r1 := ReLU4d n1 in
  let c1 := Conv4d_1x1_s1 b1 w1 r1 in
  seq (seq (seq (A(acc' (Var "dt1"), n1))
                (A(acc' (Var "dt2"), r1)))
                (A(acc' (Var "dt3"), c1)))
       (A(output, Transition input g1 z1 w1 b1 eps)).

Lemma transition_comm_eq_direct : forall (batch c co m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{co} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{co} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{co} (ary '{(m1 / 2)} (ary '{(m2 / 2)} num))))),
  transition_comm input g1 z1 w1 b1 eps output =
  transition_direct input g1 z1 w1 b1 eps output.
Proof.
  intros.
  unfold transition_comm, transition_direct, new.
  cbv zeta beta.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace.
  rewrite <- A_Avgpool4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [Transition]. *)
Lemma A_Transition : forall (batch c co m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{co} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{co} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{co} (ary '{(m1 / 2)} (ary '{(m2 / 2)} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  transition_comm input g1 z1 w1 b1 eps output rho p =
  A(output, Transition input g1 z1 w1 b1 eps) rho p.
Proof.
  intros. rewrite transition_comm_eq_direct.
  unfold transition_direct, Transition, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma transition_direct_read : forall (batch c co m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (g1 : exp (ary '{c} num))
  (z1 : exp (ary '{c} num))
  (w1 : exp (ary '{co} (ary '{c} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{co} num))
  (eps : exp num)
  (q : path)
  (k : exp (ary '{batch} (ary '{co} (ary '{(m1 / 2)} (ary '{(m2 / 2)} num)))) -> comm)
  (c0 : comm),
  seq (transition_direct input g1 z1 w1 b1 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (transition_direct input g1 z1 w1 b1 eps (acc' q))
      (seq (k (Transition input g1 z1 w1 b1 eps)) c0).
Proof.
  intros. unfold transition_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.
Section DenseNet121.
  Context {batch channel m : nat}.
  Context (input : exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num))))).

  (* Spatial sizes: stem pool output, then one avgpool(2x2,s2) per transition. *)
  Definition sp0 : nat := s_pool m.
  Definition sp1 : nat := sp0 / 2.
  Definition sp2 : nat := sp1 / 2.
  Definition sp3 : nat := sp2 / 2.

  (* Stem *)
  Context (c1_w : exp (ary '{64} (ary '{channel} (ary '{7} (ary '{7} num)))))
          (c1_b : exp (ary '{64} num))
          (bn1_g : exp (ary '{64} num)) (bn1_z : exp (ary '{64} num))
          (eps : exp num).
  (* Dense block 1, layer 1 (in 64, +32) *)
  Context (d1_1_g1 d1_1_z1 : exp (ary '{64} num))
          (d1_1_w1 : exp (ary '{128} (ary '{64} (ary '{1} (ary '{1} num)))))
          (d1_1_b1 : exp (ary '{128} num))
          (d1_1_g2 d1_1_z2 : exp (ary '{128} num))
          (d1_1_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d1_1_b2 : exp (ary '{32} num)).
  (* Dense block 1, layer 2 (in 96, +32) *)
  Context (d1_2_g1 d1_2_z1 : exp (ary '{96} num))
          (d1_2_w1 : exp (ary '{128} (ary '{96} (ary '{1} (ary '{1} num)))))
          (d1_2_b1 : exp (ary '{128} num))
          (d1_2_g2 d1_2_z2 : exp (ary '{128} num))
          (d1_2_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d1_2_b2 : exp (ary '{32} num)).
  (* Dense block 1, layer 3 (in 128, +32) *)
  Context (d1_3_g1 d1_3_z1 : exp (ary '{128} num))
          (d1_3_w1 : exp (ary '{128} (ary '{128} (ary '{1} (ary '{1} num)))))
          (d1_3_b1 : exp (ary '{128} num))
          (d1_3_g2 d1_3_z2 : exp (ary '{128} num))
          (d1_3_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d1_3_b2 : exp (ary '{32} num)).
  (* Dense block 1, layer 4 (in 160, +32) *)
  Context (d1_4_g1 d1_4_z1 : exp (ary '{160} num))
          (d1_4_w1 : exp (ary '{128} (ary '{160} (ary '{1} (ary '{1} num)))))
          (d1_4_b1 : exp (ary '{128} num))
          (d1_4_g2 d1_4_z2 : exp (ary '{128} num))
          (d1_4_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d1_4_b2 : exp (ary '{32} num)).
  (* Dense block 1, layer 5 (in 192, +32) *)
  Context (d1_5_g1 d1_5_z1 : exp (ary '{192} num))
          (d1_5_w1 : exp (ary '{128} (ary '{192} (ary '{1} (ary '{1} num)))))
          (d1_5_b1 : exp (ary '{128} num))
          (d1_5_g2 d1_5_z2 : exp (ary '{128} num))
          (d1_5_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d1_5_b2 : exp (ary '{32} num)).
  (* Dense block 1, layer 6 (in 224, +32) *)
  Context (d1_6_g1 d1_6_z1 : exp (ary '{224} num))
          (d1_6_w1 : exp (ary '{128} (ary '{224} (ary '{1} (ary '{1} num)))))
          (d1_6_b1 : exp (ary '{128} num))
          (d1_6_g2 d1_6_z2 : exp (ary '{128} num))
          (d1_6_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d1_6_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 1 (in 128, +32) *)
  Context (d2_1_g1 d2_1_z1 : exp (ary '{128} num))
          (d2_1_w1 : exp (ary '{128} (ary '{128} (ary '{1} (ary '{1} num)))))
          (d2_1_b1 : exp (ary '{128} num))
          (d2_1_g2 d2_1_z2 : exp (ary '{128} num))
          (d2_1_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_1_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 2 (in 160, +32) *)
  Context (d2_2_g1 d2_2_z1 : exp (ary '{160} num))
          (d2_2_w1 : exp (ary '{128} (ary '{160} (ary '{1} (ary '{1} num)))))
          (d2_2_b1 : exp (ary '{128} num))
          (d2_2_g2 d2_2_z2 : exp (ary '{128} num))
          (d2_2_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_2_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 3 (in 192, +32) *)
  Context (d2_3_g1 d2_3_z1 : exp (ary '{192} num))
          (d2_3_w1 : exp (ary '{128} (ary '{192} (ary '{1} (ary '{1} num)))))
          (d2_3_b1 : exp (ary '{128} num))
          (d2_3_g2 d2_3_z2 : exp (ary '{128} num))
          (d2_3_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_3_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 4 (in 224, +32) *)
  Context (d2_4_g1 d2_4_z1 : exp (ary '{224} num))
          (d2_4_w1 : exp (ary '{128} (ary '{224} (ary '{1} (ary '{1} num)))))
          (d2_4_b1 : exp (ary '{128} num))
          (d2_4_g2 d2_4_z2 : exp (ary '{128} num))
          (d2_4_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_4_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 5 (in 256, +32) *)
  Context (d2_5_g1 d2_5_z1 : exp (ary '{256} num))
          (d2_5_w1 : exp (ary '{128} (ary '{256} (ary '{1} (ary '{1} num)))))
          (d2_5_b1 : exp (ary '{128} num))
          (d2_5_g2 d2_5_z2 : exp (ary '{128} num))
          (d2_5_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_5_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 6 (in 288, +32) *)
  Context (d2_6_g1 d2_6_z1 : exp (ary '{288} num))
          (d2_6_w1 : exp (ary '{128} (ary '{288} (ary '{1} (ary '{1} num)))))
          (d2_6_b1 : exp (ary '{128} num))
          (d2_6_g2 d2_6_z2 : exp (ary '{128} num))
          (d2_6_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_6_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 7 (in 320, +32) *)
  Context (d2_7_g1 d2_7_z1 : exp (ary '{320} num))
          (d2_7_w1 : exp (ary '{128} (ary '{320} (ary '{1} (ary '{1} num)))))
          (d2_7_b1 : exp (ary '{128} num))
          (d2_7_g2 d2_7_z2 : exp (ary '{128} num))
          (d2_7_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_7_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 8 (in 352, +32) *)
  Context (d2_8_g1 d2_8_z1 : exp (ary '{352} num))
          (d2_8_w1 : exp (ary '{128} (ary '{352} (ary '{1} (ary '{1} num)))))
          (d2_8_b1 : exp (ary '{128} num))
          (d2_8_g2 d2_8_z2 : exp (ary '{128} num))
          (d2_8_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_8_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 9 (in 384, +32) *)
  Context (d2_9_g1 d2_9_z1 : exp (ary '{384} num))
          (d2_9_w1 : exp (ary '{128} (ary '{384} (ary '{1} (ary '{1} num)))))
          (d2_9_b1 : exp (ary '{128} num))
          (d2_9_g2 d2_9_z2 : exp (ary '{128} num))
          (d2_9_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_9_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 10 (in 416, +32) *)
  Context (d2_10_g1 d2_10_z1 : exp (ary '{416} num))
          (d2_10_w1 : exp (ary '{128} (ary '{416} (ary '{1} (ary '{1} num)))))
          (d2_10_b1 : exp (ary '{128} num))
          (d2_10_g2 d2_10_z2 : exp (ary '{128} num))
          (d2_10_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_10_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 11 (in 448, +32) *)
  Context (d2_11_g1 d2_11_z1 : exp (ary '{448} num))
          (d2_11_w1 : exp (ary '{128} (ary '{448} (ary '{1} (ary '{1} num)))))
          (d2_11_b1 : exp (ary '{128} num))
          (d2_11_g2 d2_11_z2 : exp (ary '{128} num))
          (d2_11_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_11_b2 : exp (ary '{32} num)).
  (* Dense block 2, layer 12 (in 480, +32) *)
  Context (d2_12_g1 d2_12_z1 : exp (ary '{480} num))
          (d2_12_w1 : exp (ary '{128} (ary '{480} (ary '{1} (ary '{1} num)))))
          (d2_12_b1 : exp (ary '{128} num))
          (d2_12_g2 d2_12_z2 : exp (ary '{128} num))
          (d2_12_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d2_12_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 1 (in 256, +32) *)
  Context (d3_1_g1 d3_1_z1 : exp (ary '{256} num))
          (d3_1_w1 : exp (ary '{128} (ary '{256} (ary '{1} (ary '{1} num)))))
          (d3_1_b1 : exp (ary '{128} num))
          (d3_1_g2 d3_1_z2 : exp (ary '{128} num))
          (d3_1_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_1_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 2 (in 288, +32) *)
  Context (d3_2_g1 d3_2_z1 : exp (ary '{288} num))
          (d3_2_w1 : exp (ary '{128} (ary '{288} (ary '{1} (ary '{1} num)))))
          (d3_2_b1 : exp (ary '{128} num))
          (d3_2_g2 d3_2_z2 : exp (ary '{128} num))
          (d3_2_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_2_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 3 (in 320, +32) *)
  Context (d3_3_g1 d3_3_z1 : exp (ary '{320} num))
          (d3_3_w1 : exp (ary '{128} (ary '{320} (ary '{1} (ary '{1} num)))))
          (d3_3_b1 : exp (ary '{128} num))
          (d3_3_g2 d3_3_z2 : exp (ary '{128} num))
          (d3_3_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_3_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 4 (in 352, +32) *)
  Context (d3_4_g1 d3_4_z1 : exp (ary '{352} num))
          (d3_4_w1 : exp (ary '{128} (ary '{352} (ary '{1} (ary '{1} num)))))
          (d3_4_b1 : exp (ary '{128} num))
          (d3_4_g2 d3_4_z2 : exp (ary '{128} num))
          (d3_4_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_4_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 5 (in 384, +32) *)
  Context (d3_5_g1 d3_5_z1 : exp (ary '{384} num))
          (d3_5_w1 : exp (ary '{128} (ary '{384} (ary '{1} (ary '{1} num)))))
          (d3_5_b1 : exp (ary '{128} num))
          (d3_5_g2 d3_5_z2 : exp (ary '{128} num))
          (d3_5_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_5_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 6 (in 416, +32) *)
  Context (d3_6_g1 d3_6_z1 : exp (ary '{416} num))
          (d3_6_w1 : exp (ary '{128} (ary '{416} (ary '{1} (ary '{1} num)))))
          (d3_6_b1 : exp (ary '{128} num))
          (d3_6_g2 d3_6_z2 : exp (ary '{128} num))
          (d3_6_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_6_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 7 (in 448, +32) *)
  Context (d3_7_g1 d3_7_z1 : exp (ary '{448} num))
          (d3_7_w1 : exp (ary '{128} (ary '{448} (ary '{1} (ary '{1} num)))))
          (d3_7_b1 : exp (ary '{128} num))
          (d3_7_g2 d3_7_z2 : exp (ary '{128} num))
          (d3_7_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_7_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 8 (in 480, +32) *)
  Context (d3_8_g1 d3_8_z1 : exp (ary '{480} num))
          (d3_8_w1 : exp (ary '{128} (ary '{480} (ary '{1} (ary '{1} num)))))
          (d3_8_b1 : exp (ary '{128} num))
          (d3_8_g2 d3_8_z2 : exp (ary '{128} num))
          (d3_8_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_8_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 9 (in 512, +32) *)
  Context (d3_9_g1 d3_9_z1 : exp (ary '{512} num))
          (d3_9_w1 : exp (ary '{128} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d3_9_b1 : exp (ary '{128} num))
          (d3_9_g2 d3_9_z2 : exp (ary '{128} num))
          (d3_9_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_9_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 10 (in 544, +32) *)
  Context (d3_10_g1 d3_10_z1 : exp (ary '{544} num))
          (d3_10_w1 : exp (ary '{128} (ary '{544} (ary '{1} (ary '{1} num)))))
          (d3_10_b1 : exp (ary '{128} num))
          (d3_10_g2 d3_10_z2 : exp (ary '{128} num))
          (d3_10_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_10_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 11 (in 576, +32) *)
  Context (d3_11_g1 d3_11_z1 : exp (ary '{576} num))
          (d3_11_w1 : exp (ary '{128} (ary '{576} (ary '{1} (ary '{1} num)))))
          (d3_11_b1 : exp (ary '{128} num))
          (d3_11_g2 d3_11_z2 : exp (ary '{128} num))
          (d3_11_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_11_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 12 (in 608, +32) *)
  Context (d3_12_g1 d3_12_z1 : exp (ary '{608} num))
          (d3_12_w1 : exp (ary '{128} (ary '{608} (ary '{1} (ary '{1} num)))))
          (d3_12_b1 : exp (ary '{128} num))
          (d3_12_g2 d3_12_z2 : exp (ary '{128} num))
          (d3_12_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_12_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 13 (in 640, +32) *)
  Context (d3_13_g1 d3_13_z1 : exp (ary '{640} num))
          (d3_13_w1 : exp (ary '{128} (ary '{640} (ary '{1} (ary '{1} num)))))
          (d3_13_b1 : exp (ary '{128} num))
          (d3_13_g2 d3_13_z2 : exp (ary '{128} num))
          (d3_13_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_13_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 14 (in 672, +32) *)
  Context (d3_14_g1 d3_14_z1 : exp (ary '{672} num))
          (d3_14_w1 : exp (ary '{128} (ary '{672} (ary '{1} (ary '{1} num)))))
          (d3_14_b1 : exp (ary '{128} num))
          (d3_14_g2 d3_14_z2 : exp (ary '{128} num))
          (d3_14_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_14_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 15 (in 704, +32) *)
  Context (d3_15_g1 d3_15_z1 : exp (ary '{704} num))
          (d3_15_w1 : exp (ary '{128} (ary '{704} (ary '{1} (ary '{1} num)))))
          (d3_15_b1 : exp (ary '{128} num))
          (d3_15_g2 d3_15_z2 : exp (ary '{128} num))
          (d3_15_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_15_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 16 (in 736, +32) *)
  Context (d3_16_g1 d3_16_z1 : exp (ary '{736} num))
          (d3_16_w1 : exp (ary '{128} (ary '{736} (ary '{1} (ary '{1} num)))))
          (d3_16_b1 : exp (ary '{128} num))
          (d3_16_g2 d3_16_z2 : exp (ary '{128} num))
          (d3_16_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_16_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 17 (in 768, +32) *)
  Context (d3_17_g1 d3_17_z1 : exp (ary '{768} num))
          (d3_17_w1 : exp (ary '{128} (ary '{768} (ary '{1} (ary '{1} num)))))
          (d3_17_b1 : exp (ary '{128} num))
          (d3_17_g2 d3_17_z2 : exp (ary '{128} num))
          (d3_17_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_17_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 18 (in 800, +32) *)
  Context (d3_18_g1 d3_18_z1 : exp (ary '{800} num))
          (d3_18_w1 : exp (ary '{128} (ary '{800} (ary '{1} (ary '{1} num)))))
          (d3_18_b1 : exp (ary '{128} num))
          (d3_18_g2 d3_18_z2 : exp (ary '{128} num))
          (d3_18_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_18_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 19 (in 832, +32) *)
  Context (d3_19_g1 d3_19_z1 : exp (ary '{832} num))
          (d3_19_w1 : exp (ary '{128} (ary '{832} (ary '{1} (ary '{1} num)))))
          (d3_19_b1 : exp (ary '{128} num))
          (d3_19_g2 d3_19_z2 : exp (ary '{128} num))
          (d3_19_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_19_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 20 (in 864, +32) *)
  Context (d3_20_g1 d3_20_z1 : exp (ary '{864} num))
          (d3_20_w1 : exp (ary '{128} (ary '{864} (ary '{1} (ary '{1} num)))))
          (d3_20_b1 : exp (ary '{128} num))
          (d3_20_g2 d3_20_z2 : exp (ary '{128} num))
          (d3_20_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_20_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 21 (in 896, +32) *)
  Context (d3_21_g1 d3_21_z1 : exp (ary '{896} num))
          (d3_21_w1 : exp (ary '{128} (ary '{896} (ary '{1} (ary '{1} num)))))
          (d3_21_b1 : exp (ary '{128} num))
          (d3_21_g2 d3_21_z2 : exp (ary '{128} num))
          (d3_21_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_21_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 22 (in 928, +32) *)
  Context (d3_22_g1 d3_22_z1 : exp (ary '{928} num))
          (d3_22_w1 : exp (ary '{128} (ary '{928} (ary '{1} (ary '{1} num)))))
          (d3_22_b1 : exp (ary '{128} num))
          (d3_22_g2 d3_22_z2 : exp (ary '{128} num))
          (d3_22_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_22_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 23 (in 960, +32) *)
  Context (d3_23_g1 d3_23_z1 : exp (ary '{960} num))
          (d3_23_w1 : exp (ary '{128} (ary '{960} (ary '{1} (ary '{1} num)))))
          (d3_23_b1 : exp (ary '{128} num))
          (d3_23_g2 d3_23_z2 : exp (ary '{128} num))
          (d3_23_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_23_b2 : exp (ary '{32} num)).
  (* Dense block 3, layer 24 (in 992, +32) *)
  Context (d3_24_g1 d3_24_z1 : exp (ary '{992} num))
          (d3_24_w1 : exp (ary '{128} (ary '{992} (ary '{1} (ary '{1} num)))))
          (d3_24_b1 : exp (ary '{128} num))
          (d3_24_g2 d3_24_z2 : exp (ary '{128} num))
          (d3_24_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d3_24_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 1 (in 512, +32) *)
  Context (d4_1_g1 d4_1_z1 : exp (ary '{512} num))
          (d4_1_w1 : exp (ary '{128} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d4_1_b1 : exp (ary '{128} num))
          (d4_1_g2 d4_1_z2 : exp (ary '{128} num))
          (d4_1_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_1_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 2 (in 544, +32) *)
  Context (d4_2_g1 d4_2_z1 : exp (ary '{544} num))
          (d4_2_w1 : exp (ary '{128} (ary '{544} (ary '{1} (ary '{1} num)))))
          (d4_2_b1 : exp (ary '{128} num))
          (d4_2_g2 d4_2_z2 : exp (ary '{128} num))
          (d4_2_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_2_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 3 (in 576, +32) *)
  Context (d4_3_g1 d4_3_z1 : exp (ary '{576} num))
          (d4_3_w1 : exp (ary '{128} (ary '{576} (ary '{1} (ary '{1} num)))))
          (d4_3_b1 : exp (ary '{128} num))
          (d4_3_g2 d4_3_z2 : exp (ary '{128} num))
          (d4_3_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_3_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 4 (in 608, +32) *)
  Context (d4_4_g1 d4_4_z1 : exp (ary '{608} num))
          (d4_4_w1 : exp (ary '{128} (ary '{608} (ary '{1} (ary '{1} num)))))
          (d4_4_b1 : exp (ary '{128} num))
          (d4_4_g2 d4_4_z2 : exp (ary '{128} num))
          (d4_4_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_4_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 5 (in 640, +32) *)
  Context (d4_5_g1 d4_5_z1 : exp (ary '{640} num))
          (d4_5_w1 : exp (ary '{128} (ary '{640} (ary '{1} (ary '{1} num)))))
          (d4_5_b1 : exp (ary '{128} num))
          (d4_5_g2 d4_5_z2 : exp (ary '{128} num))
          (d4_5_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_5_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 6 (in 672, +32) *)
  Context (d4_6_g1 d4_6_z1 : exp (ary '{672} num))
          (d4_6_w1 : exp (ary '{128} (ary '{672} (ary '{1} (ary '{1} num)))))
          (d4_6_b1 : exp (ary '{128} num))
          (d4_6_g2 d4_6_z2 : exp (ary '{128} num))
          (d4_6_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_6_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 7 (in 704, +32) *)
  Context (d4_7_g1 d4_7_z1 : exp (ary '{704} num))
          (d4_7_w1 : exp (ary '{128} (ary '{704} (ary '{1} (ary '{1} num)))))
          (d4_7_b1 : exp (ary '{128} num))
          (d4_7_g2 d4_7_z2 : exp (ary '{128} num))
          (d4_7_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_7_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 8 (in 736, +32) *)
  Context (d4_8_g1 d4_8_z1 : exp (ary '{736} num))
          (d4_8_w1 : exp (ary '{128} (ary '{736} (ary '{1} (ary '{1} num)))))
          (d4_8_b1 : exp (ary '{128} num))
          (d4_8_g2 d4_8_z2 : exp (ary '{128} num))
          (d4_8_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_8_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 9 (in 768, +32) *)
  Context (d4_9_g1 d4_9_z1 : exp (ary '{768} num))
          (d4_9_w1 : exp (ary '{128} (ary '{768} (ary '{1} (ary '{1} num)))))
          (d4_9_b1 : exp (ary '{128} num))
          (d4_9_g2 d4_9_z2 : exp (ary '{128} num))
          (d4_9_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_9_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 10 (in 800, +32) *)
  Context (d4_10_g1 d4_10_z1 : exp (ary '{800} num))
          (d4_10_w1 : exp (ary '{128} (ary '{800} (ary '{1} (ary '{1} num)))))
          (d4_10_b1 : exp (ary '{128} num))
          (d4_10_g2 d4_10_z2 : exp (ary '{128} num))
          (d4_10_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_10_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 11 (in 832, +32) *)
  Context (d4_11_g1 d4_11_z1 : exp (ary '{832} num))
          (d4_11_w1 : exp (ary '{128} (ary '{832} (ary '{1} (ary '{1} num)))))
          (d4_11_b1 : exp (ary '{128} num))
          (d4_11_g2 d4_11_z2 : exp (ary '{128} num))
          (d4_11_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_11_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 12 (in 864, +32) *)
  Context (d4_12_g1 d4_12_z1 : exp (ary '{864} num))
          (d4_12_w1 : exp (ary '{128} (ary '{864} (ary '{1} (ary '{1} num)))))
          (d4_12_b1 : exp (ary '{128} num))
          (d4_12_g2 d4_12_z2 : exp (ary '{128} num))
          (d4_12_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_12_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 13 (in 896, +32) *)
  Context (d4_13_g1 d4_13_z1 : exp (ary '{896} num))
          (d4_13_w1 : exp (ary '{128} (ary '{896} (ary '{1} (ary '{1} num)))))
          (d4_13_b1 : exp (ary '{128} num))
          (d4_13_g2 d4_13_z2 : exp (ary '{128} num))
          (d4_13_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_13_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 14 (in 928, +32) *)
  Context (d4_14_g1 d4_14_z1 : exp (ary '{928} num))
          (d4_14_w1 : exp (ary '{128} (ary '{928} (ary '{1} (ary '{1} num)))))
          (d4_14_b1 : exp (ary '{128} num))
          (d4_14_g2 d4_14_z2 : exp (ary '{128} num))
          (d4_14_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_14_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 15 (in 960, +32) *)
  Context (d4_15_g1 d4_15_z1 : exp (ary '{960} num))
          (d4_15_w1 : exp (ary '{128} (ary '{960} (ary '{1} (ary '{1} num)))))
          (d4_15_b1 : exp (ary '{128} num))
          (d4_15_g2 d4_15_z2 : exp (ary '{128} num))
          (d4_15_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_15_b2 : exp (ary '{32} num)).
  (* Dense block 4, layer 16 (in 992, +32) *)
  Context (d4_16_g1 d4_16_z1 : exp (ary '{992} num))
          (d4_16_w1 : exp (ary '{128} (ary '{992} (ary '{1} (ary '{1} num)))))
          (d4_16_b1 : exp (ary '{128} num))
          (d4_16_g2 d4_16_z2 : exp (ary '{128} num))
          (d4_16_w2 : exp (ary '{32} (ary '{128} (ary '{3} (ary '{3} num)))))
          (d4_16_b2 : exp (ary '{32} num)).
  (* Transition 1 (256 -> 128) *)
  Context (t1_g1 t1_z1 : exp (ary '{256} num))
          (t1_w1 : exp (ary '{128} (ary '{256} (ary '{1} (ary '{1} num)))))
          (t1_b1 : exp (ary '{128} num)).
  (* Transition 2 (512 -> 256) *)
  Context (t2_g1 t2_z1 : exp (ary '{512} num))
          (t2_w1 : exp (ary '{256} (ary '{512} (ary '{1} (ary '{1} num)))))
          (t2_b1 : exp (ary '{256} num)).
  (* Transition 3 (1024 -> 512) *)
  Context (t3_g1 t3_z1 : exp (ary '{1024} num))
          (t3_w1 : exp (ary '{512} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (t3_b1 : exp (ary '{512} num)).
  (* Classifier *)
  Context (fc_w : exp (ary '{1000} (ary '{1024} num)))
          (fc_b : exp (ary '{1000} num)).
  (* ---------------- Functional DenseNet121 (opaque layer wrappers) ------
     Each layer value is a separate definition; after the body lemmas they
     are made [Opaque] so that the network-level proofs never inline a layer
     into the next one (quadratic/exponential goal blow-up otherwise). *)

  Definition dn_x1 := Conv4d_p3_k7_s2 input c1_w c1_b.
  Definition dn_x2 := BatchNorm4d dn_x1 bn1_g bn1_z eps.
  Definition dn_x3 := ReLU4d dn_x2.
  Definition dn_x4 := Maxpool4d_pad 3 2 1 dn_x3.
  Definition dn_x5 := DenseLayer dn_x4 d1_1_g1 d1_1_z1 d1_1_w1 d1_1_b1 d1_1_g2 d1_1_z2 d1_1_w2 d1_1_b2 eps.
  Definition dn_x6 := DenseLayer dn_x5 d1_2_g1 d1_2_z1 d1_2_w1 d1_2_b1 d1_2_g2 d1_2_z2 d1_2_w2 d1_2_b2 eps.
  Definition dn_x7 := DenseLayer dn_x6 d1_3_g1 d1_3_z1 d1_3_w1 d1_3_b1 d1_3_g2 d1_3_z2 d1_3_w2 d1_3_b2 eps.
  Definition dn_x8 := DenseLayer dn_x7 d1_4_g1 d1_4_z1 d1_4_w1 d1_4_b1 d1_4_g2 d1_4_z2 d1_4_w2 d1_4_b2 eps.
  Definition dn_x9 := DenseLayer dn_x8 d1_5_g1 d1_5_z1 d1_5_w1 d1_5_b1 d1_5_g2 d1_5_z2 d1_5_w2 d1_5_b2 eps.
  Definition dn_x10 := DenseLayer dn_x9 d1_6_g1 d1_6_z1 d1_6_w1 d1_6_b1 d1_6_g2 d1_6_z2 d1_6_w2 d1_6_b2 eps.
  Definition dn_x11 := Transition dn_x10 t1_g1 t1_z1 t1_w1 t1_b1 eps.
  Definition dn_x12 := DenseLayer dn_x11 d2_1_g1 d2_1_z1 d2_1_w1 d2_1_b1 d2_1_g2 d2_1_z2 d2_1_w2 d2_1_b2 eps.
  Definition dn_x13 := DenseLayer dn_x12 d2_2_g1 d2_2_z1 d2_2_w1 d2_2_b1 d2_2_g2 d2_2_z2 d2_2_w2 d2_2_b2 eps.
  Definition dn_x14 := DenseLayer dn_x13 d2_3_g1 d2_3_z1 d2_3_w1 d2_3_b1 d2_3_g2 d2_3_z2 d2_3_w2 d2_3_b2 eps.
  Definition dn_x15 := DenseLayer dn_x14 d2_4_g1 d2_4_z1 d2_4_w1 d2_4_b1 d2_4_g2 d2_4_z2 d2_4_w2 d2_4_b2 eps.
  Definition dn_x16 := DenseLayer dn_x15 d2_5_g1 d2_5_z1 d2_5_w1 d2_5_b1 d2_5_g2 d2_5_z2 d2_5_w2 d2_5_b2 eps.
  Definition dn_x17 := DenseLayer dn_x16 d2_6_g1 d2_6_z1 d2_6_w1 d2_6_b1 d2_6_g2 d2_6_z2 d2_6_w2 d2_6_b2 eps.
  Definition dn_x18 := DenseLayer dn_x17 d2_7_g1 d2_7_z1 d2_7_w1 d2_7_b1 d2_7_g2 d2_7_z2 d2_7_w2 d2_7_b2 eps.
  Definition dn_x19 := DenseLayer dn_x18 d2_8_g1 d2_8_z1 d2_8_w1 d2_8_b1 d2_8_g2 d2_8_z2 d2_8_w2 d2_8_b2 eps.
  Definition dn_x20 := DenseLayer dn_x19 d2_9_g1 d2_9_z1 d2_9_w1 d2_9_b1 d2_9_g2 d2_9_z2 d2_9_w2 d2_9_b2 eps.
  Definition dn_x21 := DenseLayer dn_x20 d2_10_g1 d2_10_z1 d2_10_w1 d2_10_b1 d2_10_g2 d2_10_z2 d2_10_w2 d2_10_b2 eps.
  Definition dn_x22 := DenseLayer dn_x21 d2_11_g1 d2_11_z1 d2_11_w1 d2_11_b1 d2_11_g2 d2_11_z2 d2_11_w2 d2_11_b2 eps.
  Definition dn_x23 := DenseLayer dn_x22 d2_12_g1 d2_12_z1 d2_12_w1 d2_12_b1 d2_12_g2 d2_12_z2 d2_12_w2 d2_12_b2 eps.
  Definition dn_x24 := Transition dn_x23 t2_g1 t2_z1 t2_w1 t2_b1 eps.
  Definition dn_x25 := DenseLayer dn_x24 d3_1_g1 d3_1_z1 d3_1_w1 d3_1_b1 d3_1_g2 d3_1_z2 d3_1_w2 d3_1_b2 eps.
  Definition dn_x26 := DenseLayer dn_x25 d3_2_g1 d3_2_z1 d3_2_w1 d3_2_b1 d3_2_g2 d3_2_z2 d3_2_w2 d3_2_b2 eps.
  Definition dn_x27 := DenseLayer dn_x26 d3_3_g1 d3_3_z1 d3_3_w1 d3_3_b1 d3_3_g2 d3_3_z2 d3_3_w2 d3_3_b2 eps.
  Definition dn_x28 := DenseLayer dn_x27 d3_4_g1 d3_4_z1 d3_4_w1 d3_4_b1 d3_4_g2 d3_4_z2 d3_4_w2 d3_4_b2 eps.
  Definition dn_x29 := DenseLayer dn_x28 d3_5_g1 d3_5_z1 d3_5_w1 d3_5_b1 d3_5_g2 d3_5_z2 d3_5_w2 d3_5_b2 eps.
  Definition dn_x30 := DenseLayer dn_x29 d3_6_g1 d3_6_z1 d3_6_w1 d3_6_b1 d3_6_g2 d3_6_z2 d3_6_w2 d3_6_b2 eps.
  Definition dn_x31 := DenseLayer dn_x30 d3_7_g1 d3_7_z1 d3_7_w1 d3_7_b1 d3_7_g2 d3_7_z2 d3_7_w2 d3_7_b2 eps.
  Definition dn_x32 := DenseLayer dn_x31 d3_8_g1 d3_8_z1 d3_8_w1 d3_8_b1 d3_8_g2 d3_8_z2 d3_8_w2 d3_8_b2 eps.
  Definition dn_x33 := DenseLayer dn_x32 d3_9_g1 d3_9_z1 d3_9_w1 d3_9_b1 d3_9_g2 d3_9_z2 d3_9_w2 d3_9_b2 eps.
  Definition dn_x34 := DenseLayer dn_x33 d3_10_g1 d3_10_z1 d3_10_w1 d3_10_b1 d3_10_g2 d3_10_z2 d3_10_w2 d3_10_b2 eps.
  Definition dn_x35 := DenseLayer dn_x34 d3_11_g1 d3_11_z1 d3_11_w1 d3_11_b1 d3_11_g2 d3_11_z2 d3_11_w2 d3_11_b2 eps.
  Definition dn_x36 := DenseLayer dn_x35 d3_12_g1 d3_12_z1 d3_12_w1 d3_12_b1 d3_12_g2 d3_12_z2 d3_12_w2 d3_12_b2 eps.
  Definition dn_x37 := DenseLayer dn_x36 d3_13_g1 d3_13_z1 d3_13_w1 d3_13_b1 d3_13_g2 d3_13_z2 d3_13_w2 d3_13_b2 eps.
  Definition dn_x38 := DenseLayer dn_x37 d3_14_g1 d3_14_z1 d3_14_w1 d3_14_b1 d3_14_g2 d3_14_z2 d3_14_w2 d3_14_b2 eps.
  Definition dn_x39 := DenseLayer dn_x38 d3_15_g1 d3_15_z1 d3_15_w1 d3_15_b1 d3_15_g2 d3_15_z2 d3_15_w2 d3_15_b2 eps.
  Definition dn_x40 := DenseLayer dn_x39 d3_16_g1 d3_16_z1 d3_16_w1 d3_16_b1 d3_16_g2 d3_16_z2 d3_16_w2 d3_16_b2 eps.
  Definition dn_x41 := DenseLayer dn_x40 d3_17_g1 d3_17_z1 d3_17_w1 d3_17_b1 d3_17_g2 d3_17_z2 d3_17_w2 d3_17_b2 eps.
  Definition dn_x42 := DenseLayer dn_x41 d3_18_g1 d3_18_z1 d3_18_w1 d3_18_b1 d3_18_g2 d3_18_z2 d3_18_w2 d3_18_b2 eps.
  Definition dn_x43 := DenseLayer dn_x42 d3_19_g1 d3_19_z1 d3_19_w1 d3_19_b1 d3_19_g2 d3_19_z2 d3_19_w2 d3_19_b2 eps.
  Definition dn_x44 := DenseLayer dn_x43 d3_20_g1 d3_20_z1 d3_20_w1 d3_20_b1 d3_20_g2 d3_20_z2 d3_20_w2 d3_20_b2 eps.
  Definition dn_x45 := DenseLayer dn_x44 d3_21_g1 d3_21_z1 d3_21_w1 d3_21_b1 d3_21_g2 d3_21_z2 d3_21_w2 d3_21_b2 eps.
  Definition dn_x46 := DenseLayer dn_x45 d3_22_g1 d3_22_z1 d3_22_w1 d3_22_b1 d3_22_g2 d3_22_z2 d3_22_w2 d3_22_b2 eps.
  Definition dn_x47 := DenseLayer dn_x46 d3_23_g1 d3_23_z1 d3_23_w1 d3_23_b1 d3_23_g2 d3_23_z2 d3_23_w2 d3_23_b2 eps.
  Definition dn_x48 := DenseLayer dn_x47 d3_24_g1 d3_24_z1 d3_24_w1 d3_24_b1 d3_24_g2 d3_24_z2 d3_24_w2 d3_24_b2 eps.
  Definition dn_x49 := Transition dn_x48 t3_g1 t3_z1 t3_w1 t3_b1 eps.
  Definition dn_x50 := DenseLayer dn_x49 d4_1_g1 d4_1_z1 d4_1_w1 d4_1_b1 d4_1_g2 d4_1_z2 d4_1_w2 d4_1_b2 eps.
  Definition dn_x51 := DenseLayer dn_x50 d4_2_g1 d4_2_z1 d4_2_w1 d4_2_b1 d4_2_g2 d4_2_z2 d4_2_w2 d4_2_b2 eps.
  Definition dn_x52 := DenseLayer dn_x51 d4_3_g1 d4_3_z1 d4_3_w1 d4_3_b1 d4_3_g2 d4_3_z2 d4_3_w2 d4_3_b2 eps.
  Definition dn_x53 := DenseLayer dn_x52 d4_4_g1 d4_4_z1 d4_4_w1 d4_4_b1 d4_4_g2 d4_4_z2 d4_4_w2 d4_4_b2 eps.
  Definition dn_x54 := DenseLayer dn_x53 d4_5_g1 d4_5_z1 d4_5_w1 d4_5_b1 d4_5_g2 d4_5_z2 d4_5_w2 d4_5_b2 eps.
  Definition dn_x55 := DenseLayer dn_x54 d4_6_g1 d4_6_z1 d4_6_w1 d4_6_b1 d4_6_g2 d4_6_z2 d4_6_w2 d4_6_b2 eps.
  Definition dn_x56 := DenseLayer dn_x55 d4_7_g1 d4_7_z1 d4_7_w1 d4_7_b1 d4_7_g2 d4_7_z2 d4_7_w2 d4_7_b2 eps.
  Definition dn_x57 := DenseLayer dn_x56 d4_8_g1 d4_8_z1 d4_8_w1 d4_8_b1 d4_8_g2 d4_8_z2 d4_8_w2 d4_8_b2 eps.
  Definition dn_x58 := DenseLayer dn_x57 d4_9_g1 d4_9_z1 d4_9_w1 d4_9_b1 d4_9_g2 d4_9_z2 d4_9_w2 d4_9_b2 eps.
  Definition dn_x59 := DenseLayer dn_x58 d4_10_g1 d4_10_z1 d4_10_w1 d4_10_b1 d4_10_g2 d4_10_z2 d4_10_w2 d4_10_b2 eps.
  Definition dn_x60 := DenseLayer dn_x59 d4_11_g1 d4_11_z1 d4_11_w1 d4_11_b1 d4_11_g2 d4_11_z2 d4_11_w2 d4_11_b2 eps.
  Definition dn_x61 := DenseLayer dn_x60 d4_12_g1 d4_12_z1 d4_12_w1 d4_12_b1 d4_12_g2 d4_12_z2 d4_12_w2 d4_12_b2 eps.
  Definition dn_x62 := DenseLayer dn_x61 d4_13_g1 d4_13_z1 d4_13_w1 d4_13_b1 d4_13_g2 d4_13_z2 d4_13_w2 d4_13_b2 eps.
  Definition dn_x63 := DenseLayer dn_x62 d4_14_g1 d4_14_z1 d4_14_w1 d4_14_b1 d4_14_g2 d4_14_z2 d4_14_w2 d4_14_b2 eps.
  Definition dn_x64 := DenseLayer dn_x63 d4_15_g1 d4_15_z1 d4_15_w1 d4_15_b1 d4_15_g2 d4_15_z2 d4_15_w2 d4_15_b2 eps.
  Definition dn_x65 := DenseLayer dn_x64 d4_16_g1 d4_16_z1 d4_16_w1 d4_16_b1 d4_16_g2 d4_16_z2 d4_16_w2 d4_16_b2 eps.
  Definition dn_x66 := GlobalAvgPool4d dn_x65.
  Definition dn_x67 := Softmax2d (Linear2d fc_w fc_b dn_x66).

  Lemma dn_x1_body : dn_x1 = Conv4d_p3_k7_s2 input c1_w c1_b.
  Proof. reflexivity. Qed.
  Lemma dn_x2_body : dn_x2 = BatchNorm4d dn_x1 bn1_g bn1_z eps.
  Proof. reflexivity. Qed.
  Lemma dn_x3_body : dn_x3 = ReLU4d dn_x2.
  Proof. reflexivity. Qed.
  Lemma dn_x4_body : dn_x4 = Maxpool4d_pad 3 2 1 dn_x3.
  Proof. reflexivity. Qed.
  Lemma dn_x5_body : dn_x5 = DenseLayer dn_x4 d1_1_g1 d1_1_z1 d1_1_w1 d1_1_b1 d1_1_g2 d1_1_z2 d1_1_w2 d1_1_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x6_body : dn_x6 = DenseLayer dn_x5 d1_2_g1 d1_2_z1 d1_2_w1 d1_2_b1 d1_2_g2 d1_2_z2 d1_2_w2 d1_2_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x7_body : dn_x7 = DenseLayer dn_x6 d1_3_g1 d1_3_z1 d1_3_w1 d1_3_b1 d1_3_g2 d1_3_z2 d1_3_w2 d1_3_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x8_body : dn_x8 = DenseLayer dn_x7 d1_4_g1 d1_4_z1 d1_4_w1 d1_4_b1 d1_4_g2 d1_4_z2 d1_4_w2 d1_4_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x9_body : dn_x9 = DenseLayer dn_x8 d1_5_g1 d1_5_z1 d1_5_w1 d1_5_b1 d1_5_g2 d1_5_z2 d1_5_w2 d1_5_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x10_body : dn_x10 = DenseLayer dn_x9 d1_6_g1 d1_6_z1 d1_6_w1 d1_6_b1 d1_6_g2 d1_6_z2 d1_6_w2 d1_6_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x11_body : dn_x11 = Transition dn_x10 t1_g1 t1_z1 t1_w1 t1_b1 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x12_body : dn_x12 = DenseLayer dn_x11 d2_1_g1 d2_1_z1 d2_1_w1 d2_1_b1 d2_1_g2 d2_1_z2 d2_1_w2 d2_1_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x13_body : dn_x13 = DenseLayer dn_x12 d2_2_g1 d2_2_z1 d2_2_w1 d2_2_b1 d2_2_g2 d2_2_z2 d2_2_w2 d2_2_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x14_body : dn_x14 = DenseLayer dn_x13 d2_3_g1 d2_3_z1 d2_3_w1 d2_3_b1 d2_3_g2 d2_3_z2 d2_3_w2 d2_3_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x15_body : dn_x15 = DenseLayer dn_x14 d2_4_g1 d2_4_z1 d2_4_w1 d2_4_b1 d2_4_g2 d2_4_z2 d2_4_w2 d2_4_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x16_body : dn_x16 = DenseLayer dn_x15 d2_5_g1 d2_5_z1 d2_5_w1 d2_5_b1 d2_5_g2 d2_5_z2 d2_5_w2 d2_5_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x17_body : dn_x17 = DenseLayer dn_x16 d2_6_g1 d2_6_z1 d2_6_w1 d2_6_b1 d2_6_g2 d2_6_z2 d2_6_w2 d2_6_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x18_body : dn_x18 = DenseLayer dn_x17 d2_7_g1 d2_7_z1 d2_7_w1 d2_7_b1 d2_7_g2 d2_7_z2 d2_7_w2 d2_7_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x19_body : dn_x19 = DenseLayer dn_x18 d2_8_g1 d2_8_z1 d2_8_w1 d2_8_b1 d2_8_g2 d2_8_z2 d2_8_w2 d2_8_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x20_body : dn_x20 = DenseLayer dn_x19 d2_9_g1 d2_9_z1 d2_9_w1 d2_9_b1 d2_9_g2 d2_9_z2 d2_9_w2 d2_9_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x21_body : dn_x21 = DenseLayer dn_x20 d2_10_g1 d2_10_z1 d2_10_w1 d2_10_b1 d2_10_g2 d2_10_z2 d2_10_w2 d2_10_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x22_body : dn_x22 = DenseLayer dn_x21 d2_11_g1 d2_11_z1 d2_11_w1 d2_11_b1 d2_11_g2 d2_11_z2 d2_11_w2 d2_11_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x23_body : dn_x23 = DenseLayer dn_x22 d2_12_g1 d2_12_z1 d2_12_w1 d2_12_b1 d2_12_g2 d2_12_z2 d2_12_w2 d2_12_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x24_body : dn_x24 = Transition dn_x23 t2_g1 t2_z1 t2_w1 t2_b1 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x25_body : dn_x25 = DenseLayer dn_x24 d3_1_g1 d3_1_z1 d3_1_w1 d3_1_b1 d3_1_g2 d3_1_z2 d3_1_w2 d3_1_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x26_body : dn_x26 = DenseLayer dn_x25 d3_2_g1 d3_2_z1 d3_2_w1 d3_2_b1 d3_2_g2 d3_2_z2 d3_2_w2 d3_2_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x27_body : dn_x27 = DenseLayer dn_x26 d3_3_g1 d3_3_z1 d3_3_w1 d3_3_b1 d3_3_g2 d3_3_z2 d3_3_w2 d3_3_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x28_body : dn_x28 = DenseLayer dn_x27 d3_4_g1 d3_4_z1 d3_4_w1 d3_4_b1 d3_4_g2 d3_4_z2 d3_4_w2 d3_4_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x29_body : dn_x29 = DenseLayer dn_x28 d3_5_g1 d3_5_z1 d3_5_w1 d3_5_b1 d3_5_g2 d3_5_z2 d3_5_w2 d3_5_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x30_body : dn_x30 = DenseLayer dn_x29 d3_6_g1 d3_6_z1 d3_6_w1 d3_6_b1 d3_6_g2 d3_6_z2 d3_6_w2 d3_6_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x31_body : dn_x31 = DenseLayer dn_x30 d3_7_g1 d3_7_z1 d3_7_w1 d3_7_b1 d3_7_g2 d3_7_z2 d3_7_w2 d3_7_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x32_body : dn_x32 = DenseLayer dn_x31 d3_8_g1 d3_8_z1 d3_8_w1 d3_8_b1 d3_8_g2 d3_8_z2 d3_8_w2 d3_8_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x33_body : dn_x33 = DenseLayer dn_x32 d3_9_g1 d3_9_z1 d3_9_w1 d3_9_b1 d3_9_g2 d3_9_z2 d3_9_w2 d3_9_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x34_body : dn_x34 = DenseLayer dn_x33 d3_10_g1 d3_10_z1 d3_10_w1 d3_10_b1 d3_10_g2 d3_10_z2 d3_10_w2 d3_10_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x35_body : dn_x35 = DenseLayer dn_x34 d3_11_g1 d3_11_z1 d3_11_w1 d3_11_b1 d3_11_g2 d3_11_z2 d3_11_w2 d3_11_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x36_body : dn_x36 = DenseLayer dn_x35 d3_12_g1 d3_12_z1 d3_12_w1 d3_12_b1 d3_12_g2 d3_12_z2 d3_12_w2 d3_12_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x37_body : dn_x37 = DenseLayer dn_x36 d3_13_g1 d3_13_z1 d3_13_w1 d3_13_b1 d3_13_g2 d3_13_z2 d3_13_w2 d3_13_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x38_body : dn_x38 = DenseLayer dn_x37 d3_14_g1 d3_14_z1 d3_14_w1 d3_14_b1 d3_14_g2 d3_14_z2 d3_14_w2 d3_14_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x39_body : dn_x39 = DenseLayer dn_x38 d3_15_g1 d3_15_z1 d3_15_w1 d3_15_b1 d3_15_g2 d3_15_z2 d3_15_w2 d3_15_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x40_body : dn_x40 = DenseLayer dn_x39 d3_16_g1 d3_16_z1 d3_16_w1 d3_16_b1 d3_16_g2 d3_16_z2 d3_16_w2 d3_16_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x41_body : dn_x41 = DenseLayer dn_x40 d3_17_g1 d3_17_z1 d3_17_w1 d3_17_b1 d3_17_g2 d3_17_z2 d3_17_w2 d3_17_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x42_body : dn_x42 = DenseLayer dn_x41 d3_18_g1 d3_18_z1 d3_18_w1 d3_18_b1 d3_18_g2 d3_18_z2 d3_18_w2 d3_18_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x43_body : dn_x43 = DenseLayer dn_x42 d3_19_g1 d3_19_z1 d3_19_w1 d3_19_b1 d3_19_g2 d3_19_z2 d3_19_w2 d3_19_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x44_body : dn_x44 = DenseLayer dn_x43 d3_20_g1 d3_20_z1 d3_20_w1 d3_20_b1 d3_20_g2 d3_20_z2 d3_20_w2 d3_20_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x45_body : dn_x45 = DenseLayer dn_x44 d3_21_g1 d3_21_z1 d3_21_w1 d3_21_b1 d3_21_g2 d3_21_z2 d3_21_w2 d3_21_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x46_body : dn_x46 = DenseLayer dn_x45 d3_22_g1 d3_22_z1 d3_22_w1 d3_22_b1 d3_22_g2 d3_22_z2 d3_22_w2 d3_22_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x47_body : dn_x47 = DenseLayer dn_x46 d3_23_g1 d3_23_z1 d3_23_w1 d3_23_b1 d3_23_g2 d3_23_z2 d3_23_w2 d3_23_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x48_body : dn_x48 = DenseLayer dn_x47 d3_24_g1 d3_24_z1 d3_24_w1 d3_24_b1 d3_24_g2 d3_24_z2 d3_24_w2 d3_24_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x49_body : dn_x49 = Transition dn_x48 t3_g1 t3_z1 t3_w1 t3_b1 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x50_body : dn_x50 = DenseLayer dn_x49 d4_1_g1 d4_1_z1 d4_1_w1 d4_1_b1 d4_1_g2 d4_1_z2 d4_1_w2 d4_1_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x51_body : dn_x51 = DenseLayer dn_x50 d4_2_g1 d4_2_z1 d4_2_w1 d4_2_b1 d4_2_g2 d4_2_z2 d4_2_w2 d4_2_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x52_body : dn_x52 = DenseLayer dn_x51 d4_3_g1 d4_3_z1 d4_3_w1 d4_3_b1 d4_3_g2 d4_3_z2 d4_3_w2 d4_3_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x53_body : dn_x53 = DenseLayer dn_x52 d4_4_g1 d4_4_z1 d4_4_w1 d4_4_b1 d4_4_g2 d4_4_z2 d4_4_w2 d4_4_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x54_body : dn_x54 = DenseLayer dn_x53 d4_5_g1 d4_5_z1 d4_5_w1 d4_5_b1 d4_5_g2 d4_5_z2 d4_5_w2 d4_5_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x55_body : dn_x55 = DenseLayer dn_x54 d4_6_g1 d4_6_z1 d4_6_w1 d4_6_b1 d4_6_g2 d4_6_z2 d4_6_w2 d4_6_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x56_body : dn_x56 = DenseLayer dn_x55 d4_7_g1 d4_7_z1 d4_7_w1 d4_7_b1 d4_7_g2 d4_7_z2 d4_7_w2 d4_7_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x57_body : dn_x57 = DenseLayer dn_x56 d4_8_g1 d4_8_z1 d4_8_w1 d4_8_b1 d4_8_g2 d4_8_z2 d4_8_w2 d4_8_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x58_body : dn_x58 = DenseLayer dn_x57 d4_9_g1 d4_9_z1 d4_9_w1 d4_9_b1 d4_9_g2 d4_9_z2 d4_9_w2 d4_9_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x59_body : dn_x59 = DenseLayer dn_x58 d4_10_g1 d4_10_z1 d4_10_w1 d4_10_b1 d4_10_g2 d4_10_z2 d4_10_w2 d4_10_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x60_body : dn_x60 = DenseLayer dn_x59 d4_11_g1 d4_11_z1 d4_11_w1 d4_11_b1 d4_11_g2 d4_11_z2 d4_11_w2 d4_11_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x61_body : dn_x61 = DenseLayer dn_x60 d4_12_g1 d4_12_z1 d4_12_w1 d4_12_b1 d4_12_g2 d4_12_z2 d4_12_w2 d4_12_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x62_body : dn_x62 = DenseLayer dn_x61 d4_13_g1 d4_13_z1 d4_13_w1 d4_13_b1 d4_13_g2 d4_13_z2 d4_13_w2 d4_13_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x63_body : dn_x63 = DenseLayer dn_x62 d4_14_g1 d4_14_z1 d4_14_w1 d4_14_b1 d4_14_g2 d4_14_z2 d4_14_w2 d4_14_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x64_body : dn_x64 = DenseLayer dn_x63 d4_15_g1 d4_15_z1 d4_15_w1 d4_15_b1 d4_15_g2 d4_15_z2 d4_15_w2 d4_15_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x65_body : dn_x65 = DenseLayer dn_x64 d4_16_g1 d4_16_z1 d4_16_w1 d4_16_b1 d4_16_g2 d4_16_z2 d4_16_w2 d4_16_b2 eps.
  Proof. reflexivity. Qed.
  Lemma dn_x66_body : dn_x66 = GlobalAvgPool4d dn_x65.
  Proof. reflexivity. Qed.
  Lemma dn_x67_body : dn_x67 = Softmax2d (Linear2d fc_w fc_b dn_x66).
  Proof. reflexivity. Qed.

  Opaque dn_x1 dn_x2 dn_x3 dn_x4 dn_x5 dn_x6 dn_x7 dn_x8 dn_x9 dn_x10 dn_x11 dn_x12 dn_x13 dn_x14 dn_x15 dn_x16 dn_x17 dn_x18 dn_x19 dn_x20 dn_x21 dn_x22 dn_x23 dn_x24 dn_x25 dn_x26 dn_x27 dn_x28 dn_x29 dn_x30 dn_x31 dn_x32 dn_x33 dn_x34 dn_x35 dn_x36 dn_x37 dn_x38 dn_x39 dn_x40 dn_x41 dn_x42 dn_x43 dn_x44 dn_x45 dn_x46 dn_x47 dn_x48 dn_x49 dn_x50 dn_x51 dn_x52 dn_x53 dn_x54 dn_x55 dn_x56 dn_x57 dn_x58 dn_x59 dn_x60 dn_x61 dn_x62 dn_x63 dn_x64 dn_x65 dn_x66 dn_x67.

  Definition DenseNet121 : exp (ary '{batch} (ary '{1000} num)) := dn_x67.

  (* ---------------- Imperative DenseNet121 (buffer-layered) ---------------
     Every dense layer appends its 32 new feature channels to a fresh buffer
     (l1..l66); block temporaries dt1..dt6 are shared between blocks. *)

  Definition densenet121_comm (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
new (fun t1 => seq (Conv4d_p3_k7_s2_comm input c1_w c1_b t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 bn1_g bn1_z eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Maxpool4d_pad_comm 3 2 1 e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 =>
        dense_layer_comm e4 d1_1_g1 d1_1_z1 d1_1_w1 d1_1_b1 d1_1_g2 d1_1_z2 d1_1_w2 d1_1_b2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 =>
        dense_layer_comm e5 d1_2_g1 d1_2_z1 d1_2_w1 d1_2_b1 d1_2_g2 d1_2_z2 d1_2_w2 d1_2_b2 eps t6))
(new (fun t7 => seq (bind_read t6 (fun e6 =>
        dense_layer_comm e6 d1_3_g1 d1_3_z1 d1_3_w1 d1_3_b1 d1_3_g2 d1_3_z2 d1_3_w2 d1_3_b2 eps t7))
(new (fun t8 => seq (bind_read t7 (fun e7 =>
        dense_layer_comm e7 d1_4_g1 d1_4_z1 d1_4_w1 d1_4_b1 d1_4_g2 d1_4_z2 d1_4_w2 d1_4_b2 eps t8))
(new (fun t9 => seq (bind_read t8 (fun e8 =>
        dense_layer_comm e8 d1_5_g1 d1_5_z1 d1_5_w1 d1_5_b1 d1_5_g2 d1_5_z2 d1_5_w2 d1_5_b2 eps t9))
(new (fun t10 => seq (bind_read t9 (fun e9 =>
        dense_layer_comm e9 d1_6_g1 d1_6_z1 d1_6_w1 d1_6_b1 d1_6_g2 d1_6_z2 d1_6_w2 d1_6_b2 eps t10))
(new (fun t11 => seq (bind_read t10 (fun e10 =>
        transition_comm e10 t1_g1 t1_z1 t1_w1 t1_b1 eps t11))
(new (fun t12 => seq (bind_read t11 (fun e11 =>
        dense_layer_comm e11 d2_1_g1 d2_1_z1 d2_1_w1 d2_1_b1 d2_1_g2 d2_1_z2 d2_1_w2 d2_1_b2 eps t12))
(new (fun t13 => seq (bind_read t12 (fun e12 =>
        dense_layer_comm e12 d2_2_g1 d2_2_z1 d2_2_w1 d2_2_b1 d2_2_g2 d2_2_z2 d2_2_w2 d2_2_b2 eps t13))
(new (fun t14 => seq (bind_read t13 (fun e13 =>
        dense_layer_comm e13 d2_3_g1 d2_3_z1 d2_3_w1 d2_3_b1 d2_3_g2 d2_3_z2 d2_3_w2 d2_3_b2 eps t14))
(new (fun t15 => seq (bind_read t14 (fun e14 =>
        dense_layer_comm e14 d2_4_g1 d2_4_z1 d2_4_w1 d2_4_b1 d2_4_g2 d2_4_z2 d2_4_w2 d2_4_b2 eps t15))
(new (fun t16 => seq (bind_read t15 (fun e15 =>
        dense_layer_comm e15 d2_5_g1 d2_5_z1 d2_5_w1 d2_5_b1 d2_5_g2 d2_5_z2 d2_5_w2 d2_5_b2 eps t16))
(new (fun t17 => seq (bind_read t16 (fun e16 =>
        dense_layer_comm e16 d2_6_g1 d2_6_z1 d2_6_w1 d2_6_b1 d2_6_g2 d2_6_z2 d2_6_w2 d2_6_b2 eps t17))
(new (fun t18 => seq (bind_read t17 (fun e17 =>
        dense_layer_comm e17 d2_7_g1 d2_7_z1 d2_7_w1 d2_7_b1 d2_7_g2 d2_7_z2 d2_7_w2 d2_7_b2 eps t18))
(new (fun t19 => seq (bind_read t18 (fun e18 =>
        dense_layer_comm e18 d2_8_g1 d2_8_z1 d2_8_w1 d2_8_b1 d2_8_g2 d2_8_z2 d2_8_w2 d2_8_b2 eps t19))
(new (fun t20 => seq (bind_read t19 (fun e19 =>
        dense_layer_comm e19 d2_9_g1 d2_9_z1 d2_9_w1 d2_9_b1 d2_9_g2 d2_9_z2 d2_9_w2 d2_9_b2 eps t20))
(new (fun t21 => seq (bind_read t20 (fun e20 =>
        dense_layer_comm e20 d2_10_g1 d2_10_z1 d2_10_w1 d2_10_b1 d2_10_g2 d2_10_z2 d2_10_w2 d2_10_b2 eps t21))
(new (fun t22 => seq (bind_read t21 (fun e21 =>
        dense_layer_comm e21 d2_11_g1 d2_11_z1 d2_11_w1 d2_11_b1 d2_11_g2 d2_11_z2 d2_11_w2 d2_11_b2 eps t22))
(new (fun t23 => seq (bind_read t22 (fun e22 =>
        dense_layer_comm e22 d2_12_g1 d2_12_z1 d2_12_w1 d2_12_b1 d2_12_g2 d2_12_z2 d2_12_w2 d2_12_b2 eps t23))
(new (fun t24 => seq (bind_read t23 (fun e23 =>
        transition_comm e23 t2_g1 t2_z1 t2_w1 t2_b1 eps t24))
(new (fun t25 => seq (bind_read t24 (fun e24 =>
        dense_layer_comm e24 d3_1_g1 d3_1_z1 d3_1_w1 d3_1_b1 d3_1_g2 d3_1_z2 d3_1_w2 d3_1_b2 eps t25))
(new (fun t26 => seq (bind_read t25 (fun e25 =>
        dense_layer_comm e25 d3_2_g1 d3_2_z1 d3_2_w1 d3_2_b1 d3_2_g2 d3_2_z2 d3_2_w2 d3_2_b2 eps t26))
(new (fun t27 => seq (bind_read t26 (fun e26 =>
        dense_layer_comm e26 d3_3_g1 d3_3_z1 d3_3_w1 d3_3_b1 d3_3_g2 d3_3_z2 d3_3_w2 d3_3_b2 eps t27))
(new (fun t28 => seq (bind_read t27 (fun e27 =>
        dense_layer_comm e27 d3_4_g1 d3_4_z1 d3_4_w1 d3_4_b1 d3_4_g2 d3_4_z2 d3_4_w2 d3_4_b2 eps t28))
(new (fun t29 => seq (bind_read t28 (fun e28 =>
        dense_layer_comm e28 d3_5_g1 d3_5_z1 d3_5_w1 d3_5_b1 d3_5_g2 d3_5_z2 d3_5_w2 d3_5_b2 eps t29))
(new (fun t30 => seq (bind_read t29 (fun e29 =>
        dense_layer_comm e29 d3_6_g1 d3_6_z1 d3_6_w1 d3_6_b1 d3_6_g2 d3_6_z2 d3_6_w2 d3_6_b2 eps t30))
(new (fun t31 => seq (bind_read t30 (fun e30 =>
        dense_layer_comm e30 d3_7_g1 d3_7_z1 d3_7_w1 d3_7_b1 d3_7_g2 d3_7_z2 d3_7_w2 d3_7_b2 eps t31))
(new (fun t32 => seq (bind_read t31 (fun e31 =>
        dense_layer_comm e31 d3_8_g1 d3_8_z1 d3_8_w1 d3_8_b1 d3_8_g2 d3_8_z2 d3_8_w2 d3_8_b2 eps t32))
(new (fun t33 => seq (bind_read t32 (fun e32 =>
        dense_layer_comm e32 d3_9_g1 d3_9_z1 d3_9_w1 d3_9_b1 d3_9_g2 d3_9_z2 d3_9_w2 d3_9_b2 eps t33))
(new (fun t34 => seq (bind_read t33 (fun e33 =>
        dense_layer_comm e33 d3_10_g1 d3_10_z1 d3_10_w1 d3_10_b1 d3_10_g2 d3_10_z2 d3_10_w2 d3_10_b2 eps t34))
(new (fun t35 => seq (bind_read t34 (fun e34 =>
        dense_layer_comm e34 d3_11_g1 d3_11_z1 d3_11_w1 d3_11_b1 d3_11_g2 d3_11_z2 d3_11_w2 d3_11_b2 eps t35))
(new (fun t36 => seq (bind_read t35 (fun e35 =>
        dense_layer_comm e35 d3_12_g1 d3_12_z1 d3_12_w1 d3_12_b1 d3_12_g2 d3_12_z2 d3_12_w2 d3_12_b2 eps t36))
(new (fun t37 => seq (bind_read t36 (fun e36 =>
        dense_layer_comm e36 d3_13_g1 d3_13_z1 d3_13_w1 d3_13_b1 d3_13_g2 d3_13_z2 d3_13_w2 d3_13_b2 eps t37))
(new (fun t38 => seq (bind_read t37 (fun e37 =>
        dense_layer_comm e37 d3_14_g1 d3_14_z1 d3_14_w1 d3_14_b1 d3_14_g2 d3_14_z2 d3_14_w2 d3_14_b2 eps t38))
(new (fun t39 => seq (bind_read t38 (fun e38 =>
        dense_layer_comm e38 d3_15_g1 d3_15_z1 d3_15_w1 d3_15_b1 d3_15_g2 d3_15_z2 d3_15_w2 d3_15_b2 eps t39))
(new (fun t40 => seq (bind_read t39 (fun e39 =>
        dense_layer_comm e39 d3_16_g1 d3_16_z1 d3_16_w1 d3_16_b1 d3_16_g2 d3_16_z2 d3_16_w2 d3_16_b2 eps t40))
(new (fun t41 => seq (bind_read t40 (fun e40 =>
        dense_layer_comm e40 d3_17_g1 d3_17_z1 d3_17_w1 d3_17_b1 d3_17_g2 d3_17_z2 d3_17_w2 d3_17_b2 eps t41))
(new (fun t42 => seq (bind_read t41 (fun e41 =>
        dense_layer_comm e41 d3_18_g1 d3_18_z1 d3_18_w1 d3_18_b1 d3_18_g2 d3_18_z2 d3_18_w2 d3_18_b2 eps t42))
(new (fun t43 => seq (bind_read t42 (fun e42 =>
        dense_layer_comm e42 d3_19_g1 d3_19_z1 d3_19_w1 d3_19_b1 d3_19_g2 d3_19_z2 d3_19_w2 d3_19_b2 eps t43))
(new (fun t44 => seq (bind_read t43 (fun e43 =>
        dense_layer_comm e43 d3_20_g1 d3_20_z1 d3_20_w1 d3_20_b1 d3_20_g2 d3_20_z2 d3_20_w2 d3_20_b2 eps t44))
(new (fun t45 => seq (bind_read t44 (fun e44 =>
        dense_layer_comm e44 d3_21_g1 d3_21_z1 d3_21_w1 d3_21_b1 d3_21_g2 d3_21_z2 d3_21_w2 d3_21_b2 eps t45))
(new (fun t46 => seq (bind_read t45 (fun e45 =>
        dense_layer_comm e45 d3_22_g1 d3_22_z1 d3_22_w1 d3_22_b1 d3_22_g2 d3_22_z2 d3_22_w2 d3_22_b2 eps t46))
(new (fun t47 => seq (bind_read t46 (fun e46 =>
        dense_layer_comm e46 d3_23_g1 d3_23_z1 d3_23_w1 d3_23_b1 d3_23_g2 d3_23_z2 d3_23_w2 d3_23_b2 eps t47))
(new (fun t48 => seq (bind_read t47 (fun e47 =>
        dense_layer_comm e47 d3_24_g1 d3_24_z1 d3_24_w1 d3_24_b1 d3_24_g2 d3_24_z2 d3_24_w2 d3_24_b2 eps t48))
(new (fun t49 => seq (bind_read t48 (fun e48 =>
        transition_comm e48 t3_g1 t3_z1 t3_w1 t3_b1 eps t49))
(new (fun t50 => seq (bind_read t49 (fun e49 =>
        dense_layer_comm e49 d4_1_g1 d4_1_z1 d4_1_w1 d4_1_b1 d4_1_g2 d4_1_z2 d4_1_w2 d4_1_b2 eps t50))
(new (fun t51 => seq (bind_read t50 (fun e50 =>
        dense_layer_comm e50 d4_2_g1 d4_2_z1 d4_2_w1 d4_2_b1 d4_2_g2 d4_2_z2 d4_2_w2 d4_2_b2 eps t51))
(new (fun t52 => seq (bind_read t51 (fun e51 =>
        dense_layer_comm e51 d4_3_g1 d4_3_z1 d4_3_w1 d4_3_b1 d4_3_g2 d4_3_z2 d4_3_w2 d4_3_b2 eps t52))
(new (fun t53 => seq (bind_read t52 (fun e52 =>
        dense_layer_comm e52 d4_4_g1 d4_4_z1 d4_4_w1 d4_4_b1 d4_4_g2 d4_4_z2 d4_4_w2 d4_4_b2 eps t53))
(new (fun t54 => seq (bind_read t53 (fun e53 =>
        dense_layer_comm e53 d4_5_g1 d4_5_z1 d4_5_w1 d4_5_b1 d4_5_g2 d4_5_z2 d4_5_w2 d4_5_b2 eps t54))
(new (fun t55 => seq (bind_read t54 (fun e54 =>
        dense_layer_comm e54 d4_6_g1 d4_6_z1 d4_6_w1 d4_6_b1 d4_6_g2 d4_6_z2 d4_6_w2 d4_6_b2 eps t55))
(new (fun t56 => seq (bind_read t55 (fun e55 =>
        dense_layer_comm e55 d4_7_g1 d4_7_z1 d4_7_w1 d4_7_b1 d4_7_g2 d4_7_z2 d4_7_w2 d4_7_b2 eps t56))
(new (fun t57 => seq (bind_read t56 (fun e56 =>
        dense_layer_comm e56 d4_8_g1 d4_8_z1 d4_8_w1 d4_8_b1 d4_8_g2 d4_8_z2 d4_8_w2 d4_8_b2 eps t57))
(new (fun t58 => seq (bind_read t57 (fun e57 =>
        dense_layer_comm e57 d4_9_g1 d4_9_z1 d4_9_w1 d4_9_b1 d4_9_g2 d4_9_z2 d4_9_w2 d4_9_b2 eps t58))
(new (fun t59 => seq (bind_read t58 (fun e58 =>
        dense_layer_comm e58 d4_10_g1 d4_10_z1 d4_10_w1 d4_10_b1 d4_10_g2 d4_10_z2 d4_10_w2 d4_10_b2 eps t59))
(new (fun t60 => seq (bind_read t59 (fun e59 =>
        dense_layer_comm e59 d4_11_g1 d4_11_z1 d4_11_w1 d4_11_b1 d4_11_g2 d4_11_z2 d4_11_w2 d4_11_b2 eps t60))
(new (fun t61 => seq (bind_read t60 (fun e60 =>
        dense_layer_comm e60 d4_12_g1 d4_12_z1 d4_12_w1 d4_12_b1 d4_12_g2 d4_12_z2 d4_12_w2 d4_12_b2 eps t61))
(new (fun t62 => seq (bind_read t61 (fun e61 =>
        dense_layer_comm e61 d4_13_g1 d4_13_z1 d4_13_w1 d4_13_b1 d4_13_g2 d4_13_z2 d4_13_w2 d4_13_b2 eps t62))
(new (fun t63 => seq (bind_read t62 (fun e62 =>
        dense_layer_comm e62 d4_14_g1 d4_14_z1 d4_14_w1 d4_14_b1 d4_14_g2 d4_14_z2 d4_14_w2 d4_14_b2 eps t63))
(new (fun t64 => seq (bind_read t63 (fun e63 =>
        dense_layer_comm e63 d4_15_g1 d4_15_z1 d4_15_w1 d4_15_b1 d4_15_g2 d4_15_z2 d4_15_w2 d4_15_b2 eps t64))
(new (fun t65 => seq (bind_read t64 (fun e64 =>
        dense_layer_comm e64 d4_16_g1 d4_16_z1 d4_16_w1 d4_16_b1 d4_16_g2 d4_16_z2 d4_16_w2 d4_16_b2 eps t65))
(new (fun t66 => seq (bind_read t65 (fun e65 => GlobalAvgPool4d_comm e65 t66))
     (bind_read t66 (fun e66 => Softmax2d_comm (Linear2d fc_w fc_b e66) output))
) (acc' (Var "l66")))
) (acc' (Var "l65")))
) (acc' (Var "l64")))
) (acc' (Var "l63")))
) (acc' (Var "l62")))
) (acc' (Var "l61")))
) (acc' (Var "l60")))
) (acc' (Var "l59")))
) (acc' (Var "l58")))
) (acc' (Var "l57")))
) (acc' (Var "l56")))
) (acc' (Var "l55")))
) (acc' (Var "l54")))
) (acc' (Var "l53")))
) (acc' (Var "l52")))
) (acc' (Var "l51")))
) (acc' (Var "l50")))
) (acc' (Var "l49")))
) (acc' (Var "l48")))
) (acc' (Var "l47")))
) (acc' (Var "l46")))
) (acc' (Var "l45")))
) (acc' (Var "l44")))
) (acc' (Var "l43")))
) (acc' (Var "l42")))
) (acc' (Var "l41")))
) (acc' (Var "l40")))
) (acc' (Var "l39")))
) (acc' (Var "l38")))
) (acc' (Var "l37")))
) (acc' (Var "l36")))
) (acc' (Var "l35")))
) (acc' (Var "l34")))
) (acc' (Var "l33")))
) (acc' (Var "l32")))
) (acc' (Var "l31")))
) (acc' (Var "l30")))
) (acc' (Var "l29")))
) (acc' (Var "l28")))
) (acc' (Var "l27")))
) (acc' (Var "l26")))
) (acc' (Var "l25")))
) (acc' (Var "l24")))
) (acc' (Var "l23")))
) (acc' (Var "l22")))
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
) (acc' (Var "l1"))
.

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition densenet121_comm_direct (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
    seq (A(acc' (Var "l1"), dn_x1))
    (seq (A(acc' (Var "l2"), dn_x2))
    (seq (A(acc' (Var "l3"), dn_x3))
    (seq (A(acc' (Var "l4"), dn_x4))
    (seq (dense_layer_direct dn_x4 d1_1_g1 d1_1_z1 d1_1_w1 d1_1_b1 d1_1_g2 d1_1_z2 d1_1_w2 d1_1_b2 eps (acc' (Var "l5")))
    (seq (dense_layer_direct dn_x5 d1_2_g1 d1_2_z1 d1_2_w1 d1_2_b1 d1_2_g2 d1_2_z2 d1_2_w2 d1_2_b2 eps (acc' (Var "l6")))
    (seq (dense_layer_direct dn_x6 d1_3_g1 d1_3_z1 d1_3_w1 d1_3_b1 d1_3_g2 d1_3_z2 d1_3_w2 d1_3_b2 eps (acc' (Var "l7")))
    (seq (dense_layer_direct dn_x7 d1_4_g1 d1_4_z1 d1_4_w1 d1_4_b1 d1_4_g2 d1_4_z2 d1_4_w2 d1_4_b2 eps (acc' (Var "l8")))
    (seq (dense_layer_direct dn_x8 d1_5_g1 d1_5_z1 d1_5_w1 d1_5_b1 d1_5_g2 d1_5_z2 d1_5_w2 d1_5_b2 eps (acc' (Var "l9")))
    (seq (dense_layer_direct dn_x9 d1_6_g1 d1_6_z1 d1_6_w1 d1_6_b1 d1_6_g2 d1_6_z2 d1_6_w2 d1_6_b2 eps (acc' (Var "l10")))
    (seq (transition_direct dn_x10 t1_g1 t1_z1 t1_w1 t1_b1 eps (acc' (Var "l11")))
    (seq (dense_layer_direct dn_x11 d2_1_g1 d2_1_z1 d2_1_w1 d2_1_b1 d2_1_g2 d2_1_z2 d2_1_w2 d2_1_b2 eps (acc' (Var "l12")))
    (seq (dense_layer_direct dn_x12 d2_2_g1 d2_2_z1 d2_2_w1 d2_2_b1 d2_2_g2 d2_2_z2 d2_2_w2 d2_2_b2 eps (acc' (Var "l13")))
    (seq (dense_layer_direct dn_x13 d2_3_g1 d2_3_z1 d2_3_w1 d2_3_b1 d2_3_g2 d2_3_z2 d2_3_w2 d2_3_b2 eps (acc' (Var "l14")))
    (seq (dense_layer_direct dn_x14 d2_4_g1 d2_4_z1 d2_4_w1 d2_4_b1 d2_4_g2 d2_4_z2 d2_4_w2 d2_4_b2 eps (acc' (Var "l15")))
    (seq (dense_layer_direct dn_x15 d2_5_g1 d2_5_z1 d2_5_w1 d2_5_b1 d2_5_g2 d2_5_z2 d2_5_w2 d2_5_b2 eps (acc' (Var "l16")))
    (seq (dense_layer_direct dn_x16 d2_6_g1 d2_6_z1 d2_6_w1 d2_6_b1 d2_6_g2 d2_6_z2 d2_6_w2 d2_6_b2 eps (acc' (Var "l17")))
    (seq (dense_layer_direct dn_x17 d2_7_g1 d2_7_z1 d2_7_w1 d2_7_b1 d2_7_g2 d2_7_z2 d2_7_w2 d2_7_b2 eps (acc' (Var "l18")))
    (seq (dense_layer_direct dn_x18 d2_8_g1 d2_8_z1 d2_8_w1 d2_8_b1 d2_8_g2 d2_8_z2 d2_8_w2 d2_8_b2 eps (acc' (Var "l19")))
    (seq (dense_layer_direct dn_x19 d2_9_g1 d2_9_z1 d2_9_w1 d2_9_b1 d2_9_g2 d2_9_z2 d2_9_w2 d2_9_b2 eps (acc' (Var "l20")))
    (seq (dense_layer_direct dn_x20 d2_10_g1 d2_10_z1 d2_10_w1 d2_10_b1 d2_10_g2 d2_10_z2 d2_10_w2 d2_10_b2 eps (acc' (Var "l21")))
    (seq (dense_layer_direct dn_x21 d2_11_g1 d2_11_z1 d2_11_w1 d2_11_b1 d2_11_g2 d2_11_z2 d2_11_w2 d2_11_b2 eps (acc' (Var "l22")))
    (seq (dense_layer_direct dn_x22 d2_12_g1 d2_12_z1 d2_12_w1 d2_12_b1 d2_12_g2 d2_12_z2 d2_12_w2 d2_12_b2 eps (acc' (Var "l23")))
    (seq (transition_direct dn_x23 t2_g1 t2_z1 t2_w1 t2_b1 eps (acc' (Var "l24")))
    (seq (dense_layer_direct dn_x24 d3_1_g1 d3_1_z1 d3_1_w1 d3_1_b1 d3_1_g2 d3_1_z2 d3_1_w2 d3_1_b2 eps (acc' (Var "l25")))
    (seq (dense_layer_direct dn_x25 d3_2_g1 d3_2_z1 d3_2_w1 d3_2_b1 d3_2_g2 d3_2_z2 d3_2_w2 d3_2_b2 eps (acc' (Var "l26")))
    (seq (dense_layer_direct dn_x26 d3_3_g1 d3_3_z1 d3_3_w1 d3_3_b1 d3_3_g2 d3_3_z2 d3_3_w2 d3_3_b2 eps (acc' (Var "l27")))
    (seq (dense_layer_direct dn_x27 d3_4_g1 d3_4_z1 d3_4_w1 d3_4_b1 d3_4_g2 d3_4_z2 d3_4_w2 d3_4_b2 eps (acc' (Var "l28")))
    (seq (dense_layer_direct dn_x28 d3_5_g1 d3_5_z1 d3_5_w1 d3_5_b1 d3_5_g2 d3_5_z2 d3_5_w2 d3_5_b2 eps (acc' (Var "l29")))
    (seq (dense_layer_direct dn_x29 d3_6_g1 d3_6_z1 d3_6_w1 d3_6_b1 d3_6_g2 d3_6_z2 d3_6_w2 d3_6_b2 eps (acc' (Var "l30")))
    (seq (dense_layer_direct dn_x30 d3_7_g1 d3_7_z1 d3_7_w1 d3_7_b1 d3_7_g2 d3_7_z2 d3_7_w2 d3_7_b2 eps (acc' (Var "l31")))
    (seq (dense_layer_direct dn_x31 d3_8_g1 d3_8_z1 d3_8_w1 d3_8_b1 d3_8_g2 d3_8_z2 d3_8_w2 d3_8_b2 eps (acc' (Var "l32")))
    (seq (dense_layer_direct dn_x32 d3_9_g1 d3_9_z1 d3_9_w1 d3_9_b1 d3_9_g2 d3_9_z2 d3_9_w2 d3_9_b2 eps (acc' (Var "l33")))
    (seq (dense_layer_direct dn_x33 d3_10_g1 d3_10_z1 d3_10_w1 d3_10_b1 d3_10_g2 d3_10_z2 d3_10_w2 d3_10_b2 eps (acc' (Var "l34")))
    (seq (dense_layer_direct dn_x34 d3_11_g1 d3_11_z1 d3_11_w1 d3_11_b1 d3_11_g2 d3_11_z2 d3_11_w2 d3_11_b2 eps (acc' (Var "l35")))
    (seq (dense_layer_direct dn_x35 d3_12_g1 d3_12_z1 d3_12_w1 d3_12_b1 d3_12_g2 d3_12_z2 d3_12_w2 d3_12_b2 eps (acc' (Var "l36")))
    (seq (dense_layer_direct dn_x36 d3_13_g1 d3_13_z1 d3_13_w1 d3_13_b1 d3_13_g2 d3_13_z2 d3_13_w2 d3_13_b2 eps (acc' (Var "l37")))
    (seq (dense_layer_direct dn_x37 d3_14_g1 d3_14_z1 d3_14_w1 d3_14_b1 d3_14_g2 d3_14_z2 d3_14_w2 d3_14_b2 eps (acc' (Var "l38")))
    (seq (dense_layer_direct dn_x38 d3_15_g1 d3_15_z1 d3_15_w1 d3_15_b1 d3_15_g2 d3_15_z2 d3_15_w2 d3_15_b2 eps (acc' (Var "l39")))
    (seq (dense_layer_direct dn_x39 d3_16_g1 d3_16_z1 d3_16_w1 d3_16_b1 d3_16_g2 d3_16_z2 d3_16_w2 d3_16_b2 eps (acc' (Var "l40")))
    (seq (dense_layer_direct dn_x40 d3_17_g1 d3_17_z1 d3_17_w1 d3_17_b1 d3_17_g2 d3_17_z2 d3_17_w2 d3_17_b2 eps (acc' (Var "l41")))
    (seq (dense_layer_direct dn_x41 d3_18_g1 d3_18_z1 d3_18_w1 d3_18_b1 d3_18_g2 d3_18_z2 d3_18_w2 d3_18_b2 eps (acc' (Var "l42")))
    (seq (dense_layer_direct dn_x42 d3_19_g1 d3_19_z1 d3_19_w1 d3_19_b1 d3_19_g2 d3_19_z2 d3_19_w2 d3_19_b2 eps (acc' (Var "l43")))
    (seq (dense_layer_direct dn_x43 d3_20_g1 d3_20_z1 d3_20_w1 d3_20_b1 d3_20_g2 d3_20_z2 d3_20_w2 d3_20_b2 eps (acc' (Var "l44")))
    (seq (dense_layer_direct dn_x44 d3_21_g1 d3_21_z1 d3_21_w1 d3_21_b1 d3_21_g2 d3_21_z2 d3_21_w2 d3_21_b2 eps (acc' (Var "l45")))
    (seq (dense_layer_direct dn_x45 d3_22_g1 d3_22_z1 d3_22_w1 d3_22_b1 d3_22_g2 d3_22_z2 d3_22_w2 d3_22_b2 eps (acc' (Var "l46")))
    (seq (dense_layer_direct dn_x46 d3_23_g1 d3_23_z1 d3_23_w1 d3_23_b1 d3_23_g2 d3_23_z2 d3_23_w2 d3_23_b2 eps (acc' (Var "l47")))
    (seq (dense_layer_direct dn_x47 d3_24_g1 d3_24_z1 d3_24_w1 d3_24_b1 d3_24_g2 d3_24_z2 d3_24_w2 d3_24_b2 eps (acc' (Var "l48")))
    (seq (transition_direct dn_x48 t3_g1 t3_z1 t3_w1 t3_b1 eps (acc' (Var "l49")))
    (seq (dense_layer_direct dn_x49 d4_1_g1 d4_1_z1 d4_1_w1 d4_1_b1 d4_1_g2 d4_1_z2 d4_1_w2 d4_1_b2 eps (acc' (Var "l50")))
    (seq (dense_layer_direct dn_x50 d4_2_g1 d4_2_z1 d4_2_w1 d4_2_b1 d4_2_g2 d4_2_z2 d4_2_w2 d4_2_b2 eps (acc' (Var "l51")))
    (seq (dense_layer_direct dn_x51 d4_3_g1 d4_3_z1 d4_3_w1 d4_3_b1 d4_3_g2 d4_3_z2 d4_3_w2 d4_3_b2 eps (acc' (Var "l52")))
    (seq (dense_layer_direct dn_x52 d4_4_g1 d4_4_z1 d4_4_w1 d4_4_b1 d4_4_g2 d4_4_z2 d4_4_w2 d4_4_b2 eps (acc' (Var "l53")))
    (seq (dense_layer_direct dn_x53 d4_5_g1 d4_5_z1 d4_5_w1 d4_5_b1 d4_5_g2 d4_5_z2 d4_5_w2 d4_5_b2 eps (acc' (Var "l54")))
    (seq (dense_layer_direct dn_x54 d4_6_g1 d4_6_z1 d4_6_w1 d4_6_b1 d4_6_g2 d4_6_z2 d4_6_w2 d4_6_b2 eps (acc' (Var "l55")))
    (seq (dense_layer_direct dn_x55 d4_7_g1 d4_7_z1 d4_7_w1 d4_7_b1 d4_7_g2 d4_7_z2 d4_7_w2 d4_7_b2 eps (acc' (Var "l56")))
    (seq (dense_layer_direct dn_x56 d4_8_g1 d4_8_z1 d4_8_w1 d4_8_b1 d4_8_g2 d4_8_z2 d4_8_w2 d4_8_b2 eps (acc' (Var "l57")))
    (seq (dense_layer_direct dn_x57 d4_9_g1 d4_9_z1 d4_9_w1 d4_9_b1 d4_9_g2 d4_9_z2 d4_9_w2 d4_9_b2 eps (acc' (Var "l58")))
    (seq (dense_layer_direct dn_x58 d4_10_g1 d4_10_z1 d4_10_w1 d4_10_b1 d4_10_g2 d4_10_z2 d4_10_w2 d4_10_b2 eps (acc' (Var "l59")))
    (seq (dense_layer_direct dn_x59 d4_11_g1 d4_11_z1 d4_11_w1 d4_11_b1 d4_11_g2 d4_11_z2 d4_11_w2 d4_11_b2 eps (acc' (Var "l60")))
    (seq (dense_layer_direct dn_x60 d4_12_g1 d4_12_z1 d4_12_w1 d4_12_b1 d4_12_g2 d4_12_z2 d4_12_w2 d4_12_b2 eps (acc' (Var "l61")))
    (seq (dense_layer_direct dn_x61 d4_13_g1 d4_13_z1 d4_13_w1 d4_13_b1 d4_13_g2 d4_13_z2 d4_13_w2 d4_13_b2 eps (acc' (Var "l62")))
    (seq (dense_layer_direct dn_x62 d4_14_g1 d4_14_z1 d4_14_w1 d4_14_b1 d4_14_g2 d4_14_z2 d4_14_w2 d4_14_b2 eps (acc' (Var "l63")))
    (seq (dense_layer_direct dn_x63 d4_15_g1 d4_15_z1 d4_15_w1 d4_15_b1 d4_15_g2 d4_15_z2 d4_15_w2 d4_15_b2 eps (acc' (Var "l64")))
    (seq (dense_layer_direct dn_x64 d4_16_g1 d4_16_z1 d4_16_w1 d4_16_b1 d4_16_g2 d4_16_z2 d4_16_w2 d4_16_b2 eps (acc' (Var "l65")))
    (seq (A(acc' (Var "l66"), dn_x66))
    ((A(output, dn_x67)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition r1_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{batch} (ary '{64} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{batch} (ary '{96} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{batch} (ary '{128} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{batch} (ary '{160} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l7").
  Definition r8_acc : acc (ary '{batch} (ary '{192} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l8").
  Definition r9_acc : acc (ary '{batch} (ary '{224} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l9").
  Definition r10_acc : acc (ary '{batch} (ary '{256} (ary '{sp0} (ary '{sp0} num))))
    := acc' (Var "l10").
  Definition r11_acc : acc (ary '{batch} (ary '{128} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{batch} (ary '{160} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{batch} (ary '{192} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l13").
  Definition r14_acc : acc (ary '{batch} (ary '{224} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l14").
  Definition r15_acc : acc (ary '{batch} (ary '{256} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l15").
  Definition r16_acc : acc (ary '{batch} (ary '{288} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l16").
  Definition r17_acc : acc (ary '{batch} (ary '{320} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l17").
  Definition r18_acc : acc (ary '{batch} (ary '{352} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l18").
  Definition r19_acc : acc (ary '{batch} (ary '{384} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l19").
  Definition r20_acc : acc (ary '{batch} (ary '{416} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l20").
  Definition r21_acc : acc (ary '{batch} (ary '{448} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l21").
  Definition r22_acc : acc (ary '{batch} (ary '{480} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l22").
  Definition r23_acc : acc (ary '{batch} (ary '{512} (ary '{sp1} (ary '{sp1} num))))
    := acc' (Var "l23").
  Definition r24_acc : acc (ary '{batch} (ary '{256} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l24").
  Definition r25_acc : acc (ary '{batch} (ary '{288} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l25").
  Definition r26_acc : acc (ary '{batch} (ary '{320} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l26").
  Definition r27_acc : acc (ary '{batch} (ary '{352} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l27").
  Definition r28_acc : acc (ary '{batch} (ary '{384} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l28").
  Definition r29_acc : acc (ary '{batch} (ary '{416} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l29").
  Definition r30_acc : acc (ary '{batch} (ary '{448} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l30").
  Definition r31_acc : acc (ary '{batch} (ary '{480} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l31").
  Definition r32_acc : acc (ary '{batch} (ary '{512} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l32").
  Definition r33_acc : acc (ary '{batch} (ary '{544} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l33").
  Definition r34_acc : acc (ary '{batch} (ary '{576} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l34").
  Definition r35_acc : acc (ary '{batch} (ary '{608} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l35").
  Definition r36_acc : acc (ary '{batch} (ary '{640} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l36").
  Definition r37_acc : acc (ary '{batch} (ary '{672} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l37").
  Definition r38_acc : acc (ary '{batch} (ary '{704} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l38").
  Definition r39_acc : acc (ary '{batch} (ary '{736} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l39").
  Definition r40_acc : acc (ary '{batch} (ary '{768} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l40").
  Definition r41_acc : acc (ary '{batch} (ary '{800} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l41").
  Definition r42_acc : acc (ary '{batch} (ary '{832} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l42").
  Definition r43_acc : acc (ary '{batch} (ary '{864} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l43").
  Definition r44_acc : acc (ary '{batch} (ary '{896} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l44").
  Definition r45_acc : acc (ary '{batch} (ary '{928} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l45").
  Definition r46_acc : acc (ary '{batch} (ary '{960} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l46").
  Definition r47_acc : acc (ary '{batch} (ary '{992} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l47").
  Definition r48_acc : acc (ary '{batch} (ary '{1024} (ary '{sp2} (ary '{sp2} num))))
    := acc' (Var "l48").
  Definition r49_acc : acc (ary '{batch} (ary '{512} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l49").
  Definition r50_acc : acc (ary '{batch} (ary '{544} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l50").
  Definition r51_acc : acc (ary '{batch} (ary '{576} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l51").
  Definition r52_acc : acc (ary '{batch} (ary '{608} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l52").
  Definition r53_acc : acc (ary '{batch} (ary '{640} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l53").
  Definition r54_acc : acc (ary '{batch} (ary '{672} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l54").
  Definition r55_acc : acc (ary '{batch} (ary '{704} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l55").
  Definition r56_acc : acc (ary '{batch} (ary '{736} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l56").
  Definition r57_acc : acc (ary '{batch} (ary '{768} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l57").
  Definition r58_acc : acc (ary '{batch} (ary '{800} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l58").
  Definition r59_acc : acc (ary '{batch} (ary '{832} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l59").
  Definition r60_acc : acc (ary '{batch} (ary '{864} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l60").
  Definition r61_acc : acc (ary '{batch} (ary '{896} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l61").
  Definition r62_acc : acc (ary '{batch} (ary '{928} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l62").
  Definition r63_acc : acc (ary '{batch} (ary '{960} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l63").
  Definition r64_acc : acc (ary '{batch} (ary '{992} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l64").
  Definition r65_acc : acc (ary '{batch} (ary '{1024} (ary '{sp3} (ary '{sp3} num))))
    := acc' (Var "l65").
  Definition r66_acc : acc (ary '{batch} (ary '{1024} num))
    := acc' (Var "l66").

  (* Freshness: all layer buffers are undefined in the incoming environment
     and their paths do not overlap the final output.  The block temporaries
     dt1..dt6 are shared between blocks and are required to be fresh at every
     type. *)
  Definition densenet121_fresh
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
    StructUndefined r22_acc rho /\
    StructUndefined r23_acc rho /\
    StructUndefined r24_acc rho /\
    StructUndefined r25_acc rho /\
    StructUndefined r26_acc rho /\
    StructUndefined r27_acc rho /\
    StructUndefined r28_acc rho /\
    StructUndefined r29_acc rho /\
    StructUndefined r30_acc rho /\
    StructUndefined r31_acc rho /\
    StructUndefined r32_acc rho /\
    StructUndefined r33_acc rho /\
    StructUndefined r34_acc rho /\
    StructUndefined r35_acc rho /\
    StructUndefined r36_acc rho /\
    StructUndefined r37_acc rho /\
    StructUndefined r38_acc rho /\
    StructUndefined r39_acc rho /\
    StructUndefined r40_acc rho /\
    StructUndefined r41_acc rho /\
    StructUndefined r42_acc rho /\
    StructUndefined r43_acc rho /\
    StructUndefined r44_acc rho /\
    StructUndefined r45_acc rho /\
    StructUndefined r46_acc rho /\
    StructUndefined r47_acc rho /\
    StructUndefined r48_acc rho /\
    StructUndefined r49_acc rho /\
    StructUndefined r50_acc rho /\
    StructUndefined r51_acc rho /\
    StructUndefined r52_acc rho /\
    StructUndefined r53_acc rho /\
    StructUndefined r54_acc rho /\
    StructUndefined r55_acc rho /\
    StructUndefined r56_acc rho /\
    StructUndefined r57_acc rho /\
    StructUndefined r58_acc rho /\
    StructUndefined r59_acc rho /\
    StructUndefined r60_acc rho /\
    StructUndefined r61_acc rho /\
    StructUndefined r62_acc rho /\
    StructUndefined r63_acc rho /\
    StructUndefined r64_acc rho /\
    StructUndefined r65_acc rho /\
    StructUndefined r66_acc rho /\
    (forall d : data, StructUndefined (acc' (Var "dt1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "dt2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "dt3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "dt4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "dt5") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "dt6") : acc d) rho) /\
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
    (forall p, in_acc p output -> ~ in_acc p r22_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r23_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r24_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r25_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r26_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r27_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r28_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r29_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r30_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r31_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r32_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r33_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r34_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r35_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r36_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r37_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r38_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r39_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r40_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r41_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r42_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r43_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r44_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r45_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r46_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r47_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r48_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r49_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r50_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r51_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r52_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r53_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r54_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r55_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r56_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r57_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r58_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r59_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r60_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r61_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r62_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r63_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r64_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r65_acc) /\
    (forall p, in_acc p output -> ~ in_acc p r66_acc) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dt1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dt2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dt3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dt4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dt5") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "dt6") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  (* The proof keeps the goal small throughout: layer values are folded to
     their opaque [dn_xK] constants as soon as they are assigned, and block
     direct forms are never unfolded at the network level
     ([dense_layer_direct_read] / [transition_direct_read] advance past
     them). *)
  Lemma densenet121_comm_eq_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num))),
    densenet121_comm output = densenet121_comm_direct output.
  Proof.
    intros.
    unfold densenet121_comm, densenet121_comm_direct, new.
    cbv beta.
    rewrite <- A_Conv4d_p3_k7_s2.
    rewrite <- dn_x1_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_BatchNorm4d.
    rewrite bind_read_replace_seq.
    rewrite <- dn_x2_body.
    rewrite <- A_ReLU4d.
    rewrite bind_read_replace_seq.
    rewrite <- dn_x3_body.
    rewrite <- A_Maxpool4d_pad.
    rewrite bind_read_replace_seq.
    rewrite <- dn_x4_body.
    rewrite dense_layer_comm_eq_direct.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x5_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x6_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x7_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x8_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x9_body.
    rewrite dense_layer_direct_read.
    rewrite transition_comm_eq_direct.
    rewrite <- dn_x10_body.
    rewrite transition_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x11_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x12_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x13_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x14_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x15_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x16_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x17_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x18_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x19_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x20_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x21_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x22_body.
    rewrite dense_layer_direct_read.
    rewrite transition_comm_eq_direct.
    rewrite <- dn_x23_body.
    rewrite transition_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x24_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x25_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x26_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x27_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x28_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x29_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x30_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x31_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x32_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x33_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x34_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x35_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x36_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x37_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x38_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x39_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x40_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x41_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x42_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x43_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x44_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x45_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x46_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x47_body.
    rewrite dense_layer_direct_read.
    rewrite transition_comm_eq_direct.
    rewrite <- dn_x48_body.
    rewrite transition_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x49_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x50_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x51_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x52_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x53_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x54_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x55_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x56_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x57_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x58_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x59_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x60_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x61_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x62_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x63_body.
    rewrite dense_layer_direct_read.
    rewrite dense_layer_comm_eq_direct.
    rewrite <- dn_x64_body.
    rewrite dense_layer_direct_read.
    rewrite <- dn_x65_body.
    rewrite <- A_GlobalAvgPool4d.
    rewrite <- dn_x66_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    rewrite <- dn_x67_body.
    reflexivity.
  Qed.

  Lemma A_DenseNet121_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    densenet121_fresh output rho ->
    densenet121_comm_direct output rho p = A(output, DenseNet121) rho p.
  Proof.
    intros.
    unfold densenet121_comm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold DenseNet121. reflexivity.
  Qed.

  Theorem A_DenseNet121 :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    densenet121_fresh output rho ->
    densenet121_comm output rho p = A(output, DenseNet121) rho p.
  Proof.
    intros. rewrite densenet121_comm_eq_direct.
    apply A_DenseNet121_direct; assumption.
  Qed.

End DenseNet121.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_DenseLayer.
Print Assumptions A_Transition.
Print Assumptions A_DenseNet121.
