(* DPIA-style end-to-end Leibniz correctness proof for SqueezeNet (route A).

   Structure: SqueezeNet v1.1-style in 4d batched form, spatial size
   symbolic (m), no batchnorm (SqueezeNet has none):
     conv1(7x7,p3,s2; 96) - relu - maxpool(3x3,s2,p1)
     fire2(s16,e64,e64) - fire3(s32,e128,e128) - maxpool(3x3,s2,p1)
     fire4(s32,e128,e128) - fire5(s48,e192,e192) - maxpool(3x3,s2,p1)
     fire6(s64,e256,e256) - fire7(s64,e256,e256) - fire8(s80,e320,e320)
     conv10(1x1; 1000) - relu - GlobalAvgPool - softmax

   Version note: this file follows the 7-Fire variant specified in the task
   brief (Fire2..Fire8, maxpool after fire3 and fire5, expand widths = 4x
   the squeeze width, conv1 with 96 output channels as in the original
   paper).  For the record, torchvision's [squeezenet1_1] reference has 8
   Fire modules (squeeze widths 16,16,32,32,48,48,64,64, pools after the
   2nd and 4th Fire) and 64 conv1 channels; the paper (Iandola et al.,
   arXiv:1602.07360) v1.1 pools after conv1, fire4 and fire8.  v1.1 has no
   final fc layer: the classifier is conv10(1x1,1000) - relu -
   GlobalAvgPool - softmax.  The training-time dropout before conv10 is not
   part of the inference forward pass and is omitted.

   Each Fire module is
     squeeze: conv1x1 - relu
     expand1: conv1x1 - relu     expand3: conv3x3(p1) - relu
     Concat4d (channel concatenation of the two expand branches).

   The 1x1 / 3x3 stride-1 same-size convolutions reuse [Conv4d_1x1_s1]
   (ResNet50_DPIA) and [Conv4d_3x3_s1] (ResNet18_DPIA); the stem reuses
   [Conv4d_p3_k7_s2] and [Maxpool4d_pad]; the concatenation reuses
   [Concat4d] (Ops_Concat).

   As in GoogLeNet_DPIA.v, the block combinator [fire_comm] is proved equal
   to a buffer-free "direct" form ([fire_comm_eq_direct]); the
   network-level proof rewrites the comm form to the direct form, and the
   direct form observed at an output path equals the functional network.
   The two Concat4d inputs are bound right after each branch completes
   (bind_read adjacent to the branch's last assign), the same device as the
   four branches in GoogLeNet_DPIA.v. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
Require Import Ionia.AlexNet_DPIA.
Require Import Ionia.Ops_Conv.
Require Import Ionia.Ops_Elementwise.
Require Import Ionia.Ops_PoolPad.
Require Import Ionia.Ops_Reduce.
Require Import Ionia.Ops_Concat.
Require Import Ionia.ResNet18_DPIA.
Require Import Ionia.ResNet50_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* Pool output sizes along the network (each is [Maxpool4d_pad 3 2 1]
   applied to the previous size). *)
Definition s_pool2 (m : nat) : nat := (s_pool m - 3 + 2 * 1) / 2 + 1.
Definition s_pool3 (m : nat) : nat := (s_pool2 m - 3 + 2 * 1) / 2 + 1.

(* -------------------------------------------------------------------------- *)
(* Fire : squeeze 1x1 + expand (1x1 | 3x3) + channel concatenation            *)
(* -------------------------------------------------------------------------- *)

Definition Fire {batch inch s e1 e3 m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (ws : exp (ary '{s} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{s} num))
  (w1 : exp (ary '{e1} (ary '{s} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{e1} num))
  (w3 : exp (ary '{e3} (ary '{s} (ary '{3} (ary '{3} num)))))
  (b3 : exp (ary '{e3} num))
  : exp (ary '{batch} (ary '{(e1 + e3)} (ary '{m1} (ary '{m2} num)))) :=
  let v0 := Conv4d_1x1_s1 bs ws input in
  let sq := ReLU4d v0 in
  let v1 := Conv4d_1x1_s1 b1 w1 sq in
  let o1 := ReLU4d v1 in
  let v3 := Conv4d_3x3_s1 b3 w3 sq in
  let o3 := ReLU4d v3 in
  Concat4d o1 o3.

(* Imperative block: temporaries it1..it6, output written in place.  Each
   branch's result is bound (bind_read) immediately after its last assign so
   that the replacement lemmas apply to adjacent pairs. *)
Definition fire_comm {batch inch s e1 e3 m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (ws : exp (ary '{s} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{s} num))
  (w1 : exp (ary '{e1} (ary '{s} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{e1} num))
  (w3 : exp (ary '{e3} (ary '{s} (ary '{3} (ary '{3} num)))))
  (b3 : exp (ary '{e3} num))
  (output : acc (ary '{batch} (ary '{(e1 + e3)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bs ws input t1)
(new (fun t2 => seq (bind_read t1 (fun e0 => ReLU4d_comm e0 t2))
(bind_read t2 (fun sq =>
new (fun t3 => seq (Conv4d_1x1_s1_comm b1 w1 sq t3)
(new (fun t4 => seq (bind_read t3 (fun e1 => ReLU4d_comm e1 t4))
(bind_read t4 (fun o1 =>
new (fun t5 => seq (Conv4d_3x3_s1_comm b3 w3 sq t5)
(new (fun t6 => seq (bind_read t5 (fun e5 => ReLU4d_comm e5 t6))
(bind_read t6 (fun o2 => Concat4d_comm o1 o2 output))
) (acc' (Var "it6")))
) (acc' (Var "it5"))))
) (acc' (Var "it4")))
) (acc' (Var "it3"))))
) (acc' (Var "it2")))
) (acc' (Var "it1")).

(* Direct (DPIA-normal) form of the block. *)
Definition fire_direct {batch inch s e1 e3 m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (ws : exp (ary '{s} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{s} num))
  (w1 : exp (ary '{e1} (ary '{s} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{e1} num))
  (w3 : exp (ary '{e3} (ary '{s} (ary '{3} (ary '{3} num)))))
  (b3 : exp (ary '{e3} num))
  (output : acc (ary '{batch} (ary '{(e1 + e3)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let v0 := Conv4d_1x1_s1 bs ws input in
  let sq := ReLU4d v0 in
  let v1 := Conv4d_1x1_s1 b1 w1 sq in
  let o1 := ReLU4d v1 in
  let v3 := Conv4d_3x3_s1 b3 w3 sq in
  let o3 := ReLU4d v3 in
seq (seq (seq (seq (seq (seq (A(acc' (Var "it1"), v0))
                                (A(acc' (Var "it2"), sq)))
                                (A(acc' (Var "it3"), v1)))
                                (A(acc' (Var "it4"), o1)))
                                (A(acc' (Var "it5"), v3)))
                                (A(acc' (Var "it6"), o3)))
                                (A(output, Fire input ws bs w1 b1 w3 b3)).

Lemma fire_comm_eq_direct : forall (batch inch s e1 e3 m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (ws : exp (ary '{s} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{s} num))
  (w1 : exp (ary '{e1} (ary '{s} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{e1} num))
  (w3 : exp (ary '{e3} (ary '{s} (ary '{3} (ary '{3} num)))))
  (b3 : exp (ary '{e3} num))
  (output : acc (ary '{batch} (ary '{(e1 + e3)} (ary '{m1} (ary '{m2} num))))),
  fire_comm input ws bs w1 b1 w3 b3 output =
  fire_direct input ws bs w1 b1 w3 b3 output.
Proof.
  intros.
  unfold fire_comm, fire_direct, new.
  cbv beta zeta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Concat4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [Fire]. *)
Lemma A_Fire : forall (batch inch s e1 e3 m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (ws : exp (ary '{s} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{s} num))
  (w1 : exp (ary '{e1} (ary '{s} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{e1} num))
  (w3 : exp (ary '{e3} (ary '{s} (ary '{3} (ary '{3} num)))))
  (b3 : exp (ary '{e3} num))
  (output : acc (ary '{batch} (ary '{(e1 + e3)} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  fire_comm input ws bs w1 b1 w3 b3 output rho p =
  A(output, Fire input ws bs w1 b1 w3 b3) rho p.
Proof.
  intros. rewrite fire_comm_eq_direct.
  unfold fire_direct, Fire, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value.  This lets the network-level proof advance
   past a block without ever unfolding its direct form. *)
Lemma fire_direct_read : forall (batch inch s e1 e3 m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (ws : exp (ary '{s} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bs : exp (ary '{s} num))
  (w1 : exp (ary '{e1} (ary '{s} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{e1} num))
  (w3 : exp (ary '{e3} (ary '{s} (ary '{3} (ary '{3} num)))))
  (b3 : exp (ary '{e3} num))
  (q : path)
  (k : exp (ary '{batch} (ary '{(e1 + e3)} (ary '{m1} (ary '{m2} num)))) -> comm)
  (c0 : comm),
  seq (fire_direct input ws bs w1 b1 w3 b3 (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (fire_direct input ws bs w1 b1 w3 b3 (acc' q))
      (seq (k (Fire input ws bs w1 b1 w3 b3)) c0).
Proof.
  intros. unfold fire_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* SqueezeNet (symbolic spatial size m, symbolic batch and input channels)   *)
(* -------------------------------------------------------------------------- *)

Section SqueezeNet.
  Context {batch channel m : nat}.
  Context (input : exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num))))).

  (* Stem *)
  Context (c1_w : exp (ary '{96} (ary '{channel} (ary '{7} (ary '{7} num)))))
          (c1_b : exp (ary '{96} num)).
  (* Fire2: 96 -> 64+64 (squeeze 16) *)
  Context (f2_ws : exp (ary '{16} (ary '{96} (ary '{1} (ary '{1} num)))))
          (f2_bs : exp (ary '{16} num))
          (f2_w1 : exp (ary '{64} (ary '{16} (ary '{1} (ary '{1} num)))))
          (f2_b1 : exp (ary '{64} num))
          (f2_w3 : exp (ary '{64} (ary '{16} (ary '{3} (ary '{3} num)))))
          (f2_b3 : exp (ary '{64} num)).
  (* Fire3: 64+64 -> 128+128 (squeeze 32) *)
  Context (f3_ws : exp (ary '{32} (ary '{64+64} (ary '{1} (ary '{1} num)))))
          (f3_bs : exp (ary '{32} num))
          (f3_w1 : exp (ary '{128} (ary '{32} (ary '{1} (ary '{1} num)))))
          (f3_b1 : exp (ary '{128} num))
          (f3_w3 : exp (ary '{128} (ary '{32} (ary '{3} (ary '{3} num)))))
          (f3_b3 : exp (ary '{128} num)).
  (* Fire4: 128+128 -> 128+128 (squeeze 32) *)
  Context (f4_ws : exp (ary '{32} (ary '{128+128} (ary '{1} (ary '{1} num)))))
          (f4_bs : exp (ary '{32} num))
          (f4_w1 : exp (ary '{128} (ary '{32} (ary '{1} (ary '{1} num)))))
          (f4_b1 : exp (ary '{128} num))
          (f4_w3 : exp (ary '{128} (ary '{32} (ary '{3} (ary '{3} num)))))
          (f4_b3 : exp (ary '{128} num)).
  (* Fire5: 128+128 -> 192+192 (squeeze 48) *)
  Context (f5_ws : exp (ary '{48} (ary '{128+128} (ary '{1} (ary '{1} num)))))
          (f5_bs : exp (ary '{48} num))
          (f5_w1 : exp (ary '{192} (ary '{48} (ary '{1} (ary '{1} num)))))
          (f5_b1 : exp (ary '{192} num))
          (f5_w3 : exp (ary '{192} (ary '{48} (ary '{3} (ary '{3} num)))))
          (f5_b3 : exp (ary '{192} num)).
  (* Fire6: 192+192 -> 256+256 (squeeze 64) *)
  Context (f6_ws : exp (ary '{64} (ary '{192+192} (ary '{1} (ary '{1} num)))))
          (f6_bs : exp (ary '{64} num))
          (f6_w1 : exp (ary '{256} (ary '{64} (ary '{1} (ary '{1} num)))))
          (f6_b1 : exp (ary '{256} num))
          (f6_w3 : exp (ary '{256} (ary '{64} (ary '{3} (ary '{3} num)))))
          (f6_b3 : exp (ary '{256} num)).
  (* Fire7: 256+256 -> 256+256 (squeeze 64) *)
  Context (f7_ws : exp (ary '{64} (ary '{256+256} (ary '{1} (ary '{1} num)))))
          (f7_bs : exp (ary '{64} num))
          (f7_w1 : exp (ary '{256} (ary '{64} (ary '{1} (ary '{1} num)))))
          (f7_b1 : exp (ary '{256} num))
          (f7_w3 : exp (ary '{256} (ary '{64} (ary '{3} (ary '{3} num)))))
          (f7_b3 : exp (ary '{256} num)).
  (* Fire8: 256+256 -> 320+320 (squeeze 80) *)
  Context (f8_ws : exp (ary '{80} (ary '{256+256} (ary '{1} (ary '{1} num)))))
          (f8_bs : exp (ary '{80} num))
          (f8_w1 : exp (ary '{320} (ary '{80} (ary '{1} (ary '{1} num)))))
          (f8_b1 : exp (ary '{320} num))
          (f8_w3 : exp (ary '{320} (ary '{80} (ary '{3} (ary '{3} num)))))
          (f8_b3 : exp (ary '{320} num)).
  (* Classifier: conv10 1x1 to 1000 classes *)
  Context (c10_w : exp (ary '{1000} (ary '{320+320} (ary '{1} (ary '{1} num)))))
          (c10_b : exp (ary '{1000} num)).

  (* ---------------- Functional SqueezeNet (opaque layer wrappers) --------
     Each layer value is a separate definition; after the body lemmas they
     are made [Opaque] so that the network-level proofs never inline a layer
     into the next one (quadratic/exponential goal blow-up otherwise). *)
  Definition sn_x1 := Conv4d_p3_k7_s2 input c1_w c1_b.
  Definition sn_x2 := ReLU4d sn_x1.
  Definition sn_x3 := Maxpool4d_pad 3 2 1 sn_x2.
  Definition sn_x4 := Fire sn_x3 f2_ws f2_bs f2_w1 f2_b1 f2_w3 f2_b3.
  Definition sn_x5 := Fire sn_x4 f3_ws f3_bs f3_w1 f3_b1 f3_w3 f3_b3.
  Definition sn_x6 := Maxpool4d_pad 3 2 1 sn_x5.
  Definition sn_x7 := Fire sn_x6 f4_ws f4_bs f4_w1 f4_b1 f4_w3 f4_b3.
  Definition sn_x8 := Fire sn_x7 f5_ws f5_bs f5_w1 f5_b1 f5_w3 f5_b3.
  Definition sn_x9 := Maxpool4d_pad 3 2 1 sn_x8.
  Definition sn_x10 := Fire sn_x9 f6_ws f6_bs f6_w1 f6_b1 f6_w3 f6_b3.
  Definition sn_x11 := Fire sn_x10 f7_ws f7_bs f7_w1 f7_b1 f7_w3 f7_b3.
  Definition sn_x12 := Fire sn_x11 f8_ws f8_bs f8_w1 f8_b1 f8_w3 f8_b3.
  Definition sn_x13 := Conv4d_1x1_s1 c10_b c10_w sn_x12.
  Definition sn_x14 := ReLU4d sn_x13.
  Definition sn_x15 := GlobalAvgPool4d sn_x14.
  Definition sn_x16 := Softmax2d sn_x15.

  Lemma sn_x1_body : sn_x1 = Conv4d_p3_k7_s2 input c1_w c1_b.
  Proof. reflexivity. Qed.
  Lemma sn_x2_body : sn_x2 = ReLU4d sn_x1.
  Proof. reflexivity. Qed.
  Lemma sn_x3_body : sn_x3 = Maxpool4d_pad 3 2 1 sn_x2.
  Proof. reflexivity. Qed.
  Lemma sn_x4_body : sn_x4 = Fire sn_x3 f2_ws f2_bs f2_w1 f2_b1 f2_w3 f2_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x5_body : sn_x5 = Fire sn_x4 f3_ws f3_bs f3_w1 f3_b1 f3_w3 f3_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x6_body : sn_x6 = Maxpool4d_pad 3 2 1 sn_x5.
  Proof. reflexivity. Qed.
  Lemma sn_x7_body : sn_x7 = Fire sn_x6 f4_ws f4_bs f4_w1 f4_b1 f4_w3 f4_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x8_body : sn_x8 = Fire sn_x7 f5_ws f5_bs f5_w1 f5_b1 f5_w3 f5_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x9_body : sn_x9 = Maxpool4d_pad 3 2 1 sn_x8.
  Proof. reflexivity. Qed.
  Lemma sn_x10_body : sn_x10 = Fire sn_x9 f6_ws f6_bs f6_w1 f6_b1 f6_w3 f6_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x11_body : sn_x11 = Fire sn_x10 f7_ws f7_bs f7_w1 f7_b1 f7_w3 f7_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x12_body : sn_x12 = Fire sn_x11 f8_ws f8_bs f8_w1 f8_b1 f8_w3 f8_b3.
  Proof. reflexivity. Qed.
  Lemma sn_x13_body : sn_x13 = Conv4d_1x1_s1 c10_b c10_w sn_x12.
  Proof. reflexivity. Qed.
  Lemma sn_x14_body : sn_x14 = ReLU4d sn_x13.
  Proof. reflexivity. Qed.
  Lemma sn_x15_body : sn_x15 = GlobalAvgPool4d sn_x14.
  Proof. reflexivity. Qed.
  Lemma sn_x16_body : sn_x16 = Softmax2d sn_x15.
  Proof. reflexivity. Qed.

  Opaque sn_x1 sn_x2 sn_x3 sn_x4 sn_x5 sn_x6 sn_x7 sn_x8 sn_x9 sn_x10 sn_x11 sn_x12 sn_x13 sn_x14 sn_x15 sn_x16.

  Definition SqueezeNet : exp (ary '{batch} (ary '{1000} num)) := sn_x16.

  (* ---------------- Imperative SqueezeNet (buffer-layered) -------------- *)

  Definition squeezenet_comm (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
new (fun t1 => seq (Conv4d_p3_k7_s2_comm input c1_w c1_b t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => ReLU4d_comm e1 t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Maxpool4d_pad_comm 3 2 1 e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => fire_comm e3 f2_ws f2_bs f2_w1 f2_b1 f2_w3 f2_b3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => fire_comm e4 f3_ws f3_bs f3_w1 f3_b1 f3_w3 f3_b3 t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Maxpool4d_pad_comm 3 2 1 e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => fire_comm e6 f4_ws f4_bs f4_w1 f4_b1 f4_w3 f4_b3 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => fire_comm e7 f5_ws f5_bs f5_w1 f5_b1 f5_w3 f5_b3 t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => Maxpool4d_pad_comm 3 2 1 e8 t9))
(new (fun t10 => seq (bind_read t9 (fun e9 => fire_comm e9 f6_ws f6_bs f6_w1 f6_b1 f6_w3 f6_b3 t10))
(new (fun t11 => seq (bind_read t10 (fun e10 => fire_comm e10 f7_ws f7_bs f7_w1 f7_b1 f7_w3 f7_b3 t11))
(new (fun t12 => seq (bind_read t11 (fun e11 => fire_comm e11 f8_ws f8_bs f8_w1 f8_b1 f8_w3 f8_b3 t12))
(new (fun t13 => seq (bind_read t12 (fun e12 => Conv4d_1x1_s1_comm c10_b c10_w e12 t13))
(new (fun t14 => seq (bind_read t13 (fun e13 => ReLU4d_comm e13 t14))
(new (fun t15 => seq (bind_read t14 (fun e14 => GlobalAvgPool4d_comm e14 t15))
     (bind_read t15 (fun e15 => Softmax2d_comm e15 output))
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

  Definition squeezenet_comm_direct (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
    seq (A(acc' (Var "l1"), sn_x1))
    (seq (A(acc' (Var "l2"), sn_x2))
    (seq (A(acc' (Var "l3"), sn_x3))
    (seq (fire_direct sn_x3 f2_ws f2_bs f2_w1 f2_b1 f2_w3 f2_b3 (acc' (Var "l4")))
    (seq (fire_direct sn_x4 f3_ws f3_bs f3_w1 f3_b1 f3_w3 f3_b3 (acc' (Var "l5")))
    (seq (A(acc' (Var "l6"), sn_x6))
    (seq (fire_direct sn_x6 f4_ws f4_bs f4_w1 f4_b1 f4_w3 f4_b3 (acc' (Var "l7")))
    (seq (fire_direct sn_x7 f5_ws f5_bs f5_w1 f5_b1 f5_w3 f5_b3 (acc' (Var "l8")))
    (seq (A(acc' (Var "l9"), sn_x9))
    (seq (fire_direct sn_x9 f6_ws f6_bs f6_w1 f6_b1 f6_w3 f6_b3 (acc' (Var "l10")))
    (seq (fire_direct sn_x10 f7_ws f7_bs f7_w1 f7_b1 f7_w3 f7_b3 (acc' (Var "l11")))
    (seq (fire_direct sn_x11 f8_ws f8_bs f8_w1 f8_b1 f8_w3 f8_b3 (acc' (Var "l12")))
    (seq (A(acc' (Var "l13"), sn_x13))
    (seq (A(acc' (Var "l14"), sn_x14))
    (seq (A(acc' (Var "l15"), sn_x15))
    ((A(output, sn_x16))))))))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition r1_acc : acc (ary '{batch} (ary '{96} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{batch} (ary '{96} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{batch} (ary '{96} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{batch} (ary '{64+64} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{batch} (ary '{128+128} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{batch} (ary '{128+128} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{batch} (ary '{128+128} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l7").
  Definition r8_acc : acc (ary '{batch} (ary '{192+192} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l8").
  Definition r9_acc : acc (ary '{batch} (ary '{192+192} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l9").
  Definition r10_acc : acc (ary '{batch} (ary '{256+256} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l10").
  Definition r11_acc : acc (ary '{batch} (ary '{256+256} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{batch} (ary '{320+320} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{batch} (ary '{1000} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l13").
  Definition r14_acc : acc (ary '{batch} (ary '{1000} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l14").
  Definition r15_acc : acc (ary '{batch} (ary '{1000} num))
    := acc' (Var "l15").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries it1..it6 are shared between blocks and are required to be
     fresh at every type. *)
  Definition squeezenet_fresh
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
    (forall d : data, StructUndefined (acc' (Var "it1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it5") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it6") : acc d) rho) /\
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
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it5") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it6") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  (* The proof keeps the goal small throughout: layer values are folded to
     their opaque [sn_xK] constants as soon as they are assigned, and block
     direct forms are never unfolded at the network level
     ([fire_direct_read] advances past them). *)
  Lemma squeezenet_comm_eq_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num))),
    squeezenet_comm output = squeezenet_comm_direct output.
  Proof.
    intros.
    unfold squeezenet_comm, squeezenet_comm_direct, new.
    cbv beta.
    rewrite <- A_Conv4d_p3_k7_s2.
    rewrite <- sn_x1_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_ReLU4d.
    rewrite <- sn_x2_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- sn_x3_body.
    rewrite bind_read_replace_seq.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x4_body.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x5_body.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- sn_x6_body.
    rewrite bind_read_replace_seq.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x7_body.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x8_body.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- sn_x9_body.
    rewrite bind_read_replace_seq.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x10_body.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x11_body.
    rewrite fire_comm_eq_direct.
    rewrite fire_direct_read.
    rewrite <- sn_x12_body.
    rewrite <- A_Conv4d_1x1_s1.
    rewrite <- sn_x13_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_ReLU4d.
    rewrite <- sn_x14_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_GlobalAvgPool4d.
    rewrite <- sn_x15_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    rewrite <- sn_x16_body.
    reflexivity.
  Qed.

  Lemma A_SqueezeNet_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    squeezenet_fresh output rho ->
    squeezenet_comm_direct output rho p = A(output, SqueezeNet) rho p.
  Proof.
    intros.
    unfold squeezenet_comm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold SqueezeNet. reflexivity.
  Qed.

  Theorem A_SqueezeNet :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    squeezenet_fresh output rho ->
    squeezenet_comm output rho p = A(output, SqueezeNet) rho p.
  Proof.
    intros. rewrite squeezenet_comm_eq_direct.
    apply A_SqueezeNet_direct; assumption.
  Qed.

End SqueezeNet.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Fire.
Print Assumptions A_SqueezeNet.
