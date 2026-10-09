(* DPIA-style end-to-end Leibniz correctness proof for GoogLeNet
   (Inception v1, route A).

   Structure: classic GoogLeNet main path in 4d batched form, spatial size
   symbolic (m), no batchnorm (GoogLeNet has none):
     stem: conv1(7x7,p3,s2; 64) - relu - maxpool(3x3,s2,p1)
           conv3(3x3,p1,s1; 192) - relu - maxpool(3x3,s2,p1)
     inception 3a,3b | 4a, maxpool(3x3,s2,p1), 4b, 4c, 4d,
                       maxpool(3x3,s2,p1), 4e | 5a, 5b
     GlobalAvgPool - fc(1000) - softmax

   The two auxiliary classifiers of the original paper are training-time
   branches; they are not part of the inference forward pass and are
   therefore omitted here.

   Each Inception module (size-preserving) is
     branch1: conv1x1 - relu
     branch2: conv1x1 - relu - conv3x3(p1) - relu
     branch3: conv1x1 - relu - conv5x5(p2) - relu
     branch4: maxpool(3x3,p1,s1) - conv1x1 - relu
     Concat4d4 (channel concatenation of the four branches).

   The 1x1 / 3x3 stride-1 same-size convolutions reuse [Conv4d_1x1_s1]
   (ResNet50_DPIA) and [Conv4d_3x3_s1] (ResNet18_DPIA); the 5x5 p2 s1
   same-size variant [Conv4d_5x5_s1] and the stride-1 same-size pool
   [Maxpool4d_3x3_s1] are added here, proved exactly like [A_Conv4d_3x3_s1]
   resp. [A_Maxpool4d_pad].  The stem reuses [Conv4d_p3_k7_s2] and
   [Maxpool4d_pad]; the concatenation reuses [Concat4d4] (Ops_Concat).

   As in ResNet50_DPIA.v, the block combinator [inception_id_comm] is proved
   equal to a buffer-free "direct" form ([inception_id_comm_eq_direct]); the
   network-level proof rewrites the comm form to the direct form, and the
   direct form observed at an output path equals the functional network.
   The four Concat4d4 inputs are bound right after each branch completes
   (bind_read adjacent to the branch's last assign), the same device as the
   projection shortcut in ResNet50_DPIA.v. *)

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
Definition s_pool4 (m : nat) : nat := (s_pool3 m - 3 + 2 * 1) / 2 + 1.

(* -------------------------------------------------------------------------- *)
(* Conv4d_5x5_s1 : same-size 5x5 convolution, padding 2, stride 1             *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_5x5_s1 {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{5} (ary '{5} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin m1 => mkvSeq (fun j0 : fin m2 =>
      add (sum (mkvSeq (fun c : fin inch =>
            sum (mkvSeq (fun i1 : fin 5 =>
              sum (mkvSeq (fun j1 : fin 5 =>
                mul (pad_idx2d 2 (idx (idx input b) c)
                               (fin2nat i0 + fin2nat i1)
                               (fin2nat j0 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition Conv4d_5x5_s1_comm {batch inch outch m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{5} (ary '{5} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin inch =>
             sum (mkvSeq (fun i1 : fin 5 =>
               sum (mkvSeq (fun j1 : fin 5 =>
                 mul (pad_idx2d 2 (idx (idx input b) c)
                                (fin2nat i0 + fin2nat i1)
                                (fin2nat j0 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_Conv4d_5x5_s1 : forall (batch inch outch m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch} (ary '{5} (ary '{5} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  A(output, Conv4d_5x5_s1 bias w input) = Conv4d_5x5_s1_comm bias w input output.
Proof.
  intros. unfold Conv4d_5x5_s1, Conv4d_5x5_s1_comm.
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
(* Maxpool4d_3x3_s1 : same-size 3x3 maxpool, padding 1, stride 1              *)
(* (output size declared as m1 x m2 directly: (m-3+2*1)/1+1 is not            *)
(*  definitionally m, so the general [Maxpool4d_pad] cannot be used in a      *)
(*  same-size context)                                                        *)
(* -------------------------------------------------------------------------- *)

Definition Maxpool4d_3x3_s1 {batch filernum m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))) :=
  tlet pad := Padding4d 1 input in
  mkvSeq (fun b : fin batch =>
    mkvSeq (fun num : fin filernum =>
      mkvSeq (fun i0 : fin m1 =>
        mkvSeq (fun j0 : fin m2 =>
          max (mkvSeq (fun i1 : fin 3 => max (mkvSeq (fun j1 : fin 3 =>
            safe_idx_nat
              (safe_idx_nat (idx (idx pad b) num)
                            (fin2nat i0 + fin2nat i1))
              (fin2nat j0 + fin2nat j1))))))))).

Definition Maxpool4d_3x3_s1_comm {batch filernum m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun num oc => mkvSeql (fun i0 o0 =>
    mkvSeql (fun j0 o1 =>
      maxl (mkvSeq (fun i1 : fin 3 => max (mkvSeq (fun j1 : fin 3 =>
        safe_idx_nat
          (safe_idx_nat (idx (idx (Padding4d 1 input) b) num)
                        (fin2nat i0 + fin2nat i1))
          (fin2nat j0 + fin2nat j1)))))
           (fun r => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_Maxpool4d_3x3_s1 : forall (batch filernum m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))),
  A(output, Maxpool4d_3x3_s1 input)
  = Maxpool4d_3x3_s1_comm input output.
Proof.
  intros. unfold Maxpool4d_3x3_s1, Maxpool4d_3x3_s1_comm, let_binding. cbv beta.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_max_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Inception_id : size-preserving four-branch inception module                 *)
(* -------------------------------------------------------------------------- *)

Definition Inception_id {batch inch c1 c2r c2 c3r c3 c4 m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c1} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{c1} num))
  (w2r : exp (ary '{c2r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b2r : exp (ary '{c2r} num))
  (w2 : exp (ary '{c2} (ary '{c2r} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c2} num))
  (w3r : exp (ary '{c3r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b3r : exp (ary '{c3r} num))
  (w3 : exp (ary '{c3} (ary '{c3r} (ary '{5} (ary '{5} num)))))
  (b3 : exp (ary '{c3} num))
  (w4 : exp (ary '{c4} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b4 : exp (ary '{c4} num))
  : exp (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num)))) :=
  let v1 := Conv4d_1x1_s1 b1 w1 input in
  let r1 := ReLU4d v1 in
  let v2 := Conv4d_1x1_s1 b2r w2r input in
  let u2 := ReLU4d v2 in
  let o2 := Conv4d_3x3_s1 b2 w2 u2 in
  let r2 := ReLU4d o2 in
  let v3 := Conv4d_1x1_s1 b3r w3r input in
  let u3 := ReLU4d v3 in
  let o3 := Conv4d_5x5_s1 b3 w3 u3 in
  let r3 := ReLU4d o3 in
  let p4 := Maxpool4d_3x3_s1 input in
  let v4 := Conv4d_1x1_s1 b4 w4 p4 in
  let r4 := ReLU4d v4 in
  Concat4d4 r1 r2 r3 r4.

(* Imperative block: temporaries it1..it13, output written in place.  Each
   branch's result is bound (bind_read) immediately after its last assign so
   that the replacement lemmas apply to adjacent pairs. *)
Definition inception_id_comm {batch inch c1 c2r c2 c3r c3 c4 m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c1} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{c1} num))
  (w2r : exp (ary '{c2r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b2r : exp (ary '{c2r} num))
  (w2 : exp (ary '{c2} (ary '{c2r} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c2} num))
  (w3r : exp (ary '{c3r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b3r : exp (ary '{c3r} num))
  (w3 : exp (ary '{c3} (ary '{c3r} (ary '{5} (ary '{5} num)))))
  (b3 : exp (ary '{c3} num))
  (w4 : exp (ary '{c4} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b4 : exp (ary '{c4} num))
  (output : acc (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm b1 w1 input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => ReLU4d_comm e1 t2))
(bind_read t2 (fun o1 =>
new (fun t3 => seq (Conv4d_1x1_s1_comm b2r w2r input t3)
(new (fun t4 => seq (bind_read t3 (fun e3 => ReLU4d_comm e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => Conv4d_3x3_s1_comm b2 w2 e4 t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => ReLU4d_comm e5 t6))
(bind_read t6 (fun o2 =>
new (fun t7 => seq (Conv4d_1x1_s1_comm b3r w3r input t7)
(new (fun t8 => seq (bind_read t7 (fun e7 => ReLU4d_comm e7 t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => Conv4d_5x5_s1_comm b3 w3 e8 t9))
(new (fun t10 => seq (bind_read t9 (fun e9 => ReLU4d_comm e9 t10))
(bind_read t10 (fun o3 =>
new (fun t11 => seq (Maxpool4d_3x3_s1_comm input t11)
(new (fun t12 => seq (bind_read t11 (fun e11 => Conv4d_1x1_s1_comm b4 w4 e11 t12))
(new (fun t13 => seq (bind_read t12 (fun e12 => ReLU4d_comm e12 t13))
     (bind_read t13 (fun o4 => Concat4d4_comm o1 o2 o3 o4 output))
) (acc' (Var "it13")))
) (acc' (Var "it12")))
) (acc' (Var "it11"))))
) (acc' (Var "it10")))
) (acc' (Var "it9")))
) (acc' (Var "it8")))
) (acc' (Var "it7"))))
) (acc' (Var "it6")))
) (acc' (Var "it5")))
) (acc' (Var "it4")))
) (acc' (Var "it3"))))
) (acc' (Var "it2")))
) (acc' (Var "it1")).

(* Direct (DPIA-normal) form of the block. *)
Definition inception_id_direct {batch inch c1 c2r c2 c3r c3 c4 m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c1} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{c1} num))
  (w2r : exp (ary '{c2r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b2r : exp (ary '{c2r} num))
  (w2 : exp (ary '{c2} (ary '{c2r} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c2} num))
  (w3r : exp (ary '{c3r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b3r : exp (ary '{c3r} num))
  (w3 : exp (ary '{c3} (ary '{c3r} (ary '{5} (ary '{5} num)))))
  (b3 : exp (ary '{c3} num))
  (w4 : exp (ary '{c4} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b4 : exp (ary '{c4} num))
  (output : acc (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let v1 := Conv4d_1x1_s1 b1 w1 input in
  let r1 := ReLU4d v1 in
  let v2 := Conv4d_1x1_s1 b2r w2r input in
  let u2 := ReLU4d v2 in
  let o2 := Conv4d_3x3_s1 b2 w2 u2 in
  let r2 := ReLU4d o2 in
  let v3 := Conv4d_1x1_s1 b3r w3r input in
  let u3 := ReLU4d v3 in
  let o3 := Conv4d_5x5_s1 b3 w3 u3 in
  let r3 := ReLU4d o3 in
  let p4 := Maxpool4d_3x3_s1 input in
  let v4 := Conv4d_1x1_s1 b4 w4 p4 in
  let r4 := ReLU4d v4 in
seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "it1"), v1)))
                                (A(acc' (Var "it2"), r1)))
                                (A(acc' (Var "it3"), v2)))
                                (A(acc' (Var "it4"), u2)))
                                (A(acc' (Var "it5"), o2)))
                                (A(acc' (Var "it6"), r2)))
                                (A(acc' (Var "it7"), v3)))
                                (A(acc' (Var "it8"), u3)))
                                (A(acc' (Var "it9"), o3)))
                                (A(acc' (Var "it10"), r3)))
                                (A(acc' (Var "it11"), p4)))
                                (A(acc' (Var "it12"), v4)))
                                (A(acc' (Var "it13"), r4)))
                                (A(output, Inception_id input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4)).

Lemma inception_id_comm_eq_direct : forall (batch inch c1 c2r c2 c3r c3 c4 m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c1} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{c1} num))
  (w2r : exp (ary '{c2r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b2r : exp (ary '{c2r} num))
  (w2 : exp (ary '{c2} (ary '{c2r} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c2} num))
  (w3r : exp (ary '{c3r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b3r : exp (ary '{c3r} num))
  (w3 : exp (ary '{c3} (ary '{c3r} (ary '{5} (ary '{5} num)))))
  (b3 : exp (ary '{c3} num))
  (w4 : exp (ary '{c4} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b4 : exp (ary '{c4} num))
  (output : acc (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num))))),
  inception_id_comm input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4 output =
  inception_id_direct input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4 output.
Proof.
  intros.
  unfold inception_id_comm, inception_id_direct, new.
  cbv beta zeta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_5x5_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Maxpool4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace.
  rewrite <- A_Concat4d4.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [Inception_id]. *)
Lemma A_Inception_id : forall (batch inch c1 c2r c2 c3r c3 c4 m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c1} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{c1} num))
  (w2r : exp (ary '{c2r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b2r : exp (ary '{c2r} num))
  (w2 : exp (ary '{c2} (ary '{c2r} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c2} num))
  (w3r : exp (ary '{c3r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b3r : exp (ary '{c3r} num))
  (w3 : exp (ary '{c3} (ary '{c3r} (ary '{5} (ary '{5} num)))))
  (b3 : exp (ary '{c3} num))
  (w4 : exp (ary '{c4} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b4 : exp (ary '{c4} num))
  (output : acc (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  inception_id_comm input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4 output rho p =
  A(output, Inception_id input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4) rho p.
Proof.
  intros. rewrite inception_id_comm_eq_direct.
  unfold inception_id_direct, Inception_id, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value.  This lets the network-level proof advance
   past a block without ever unfolding its direct form. *)
Lemma inception_id_direct_read : forall (batch inch c1 c2r c2 c3r c3 c4 m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (w1 : exp (ary '{c1} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1 : exp (ary '{c1} num))
  (w2r : exp (ary '{c2r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b2r : exp (ary '{c2r} num))
  (w2 : exp (ary '{c2} (ary '{c2r} (ary '{3} (ary '{3} num)))))
  (b2 : exp (ary '{c2} num))
  (w3r : exp (ary '{c3r} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b3r : exp (ary '{c3r} num))
  (w3 : exp (ary '{c3} (ary '{c3r} (ary '{5} (ary '{5} num)))))
  (b3 : exp (ary '{c3} num))
  (w4 : exp (ary '{c4} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b4 : exp (ary '{c4} num))
  (q : path)
  (k : exp (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num)))) -> comm)
  (c0 : comm),
  seq (inception_id_direct input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4 (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (inception_id_direct input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4 (acc' q))
      (seq (k (Inception_id input w1 b1 w2r b2r w2 b2 w3r b3r w3 b3 w4 b4)) c0).
Proof.
  intros. unfold inception_id_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.
(* -------------------------------------------------------------------------- *)
(* GoogLeNet (symbolic spatial size m, symbolic batch and input channels)     *)
(* -------------------------------------------------------------------------- *)

Section GoogLeNet.
  Context {batch channel m : nat}.
  Context (input : exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num))))).

  (* Stem *)
  Context (c1_w : exp (ary '{64} (ary '{channel} (ary '{7} (ary '{7} num)))))
          (c1_b : exp (ary '{64} num))
          (c2_w : exp (ary '{192} (ary '{64} (ary '{3} (ary '{3} num)))))
          (c2_b : exp (ary '{192} num)).
  (* Inception 3a: 192 -> 64+128+32+32 *)
  Context (i3a_w1 : exp (ary '{64} (ary '{192} (ary '{1} (ary '{1} num)))))
          (i3a_b1 : exp (ary '{64} num))
          (i3a_w2r : exp (ary '{96} (ary '{192} (ary '{1} (ary '{1} num)))))
          (i3a_b2r : exp (ary '{96} num))
          (i3a_w2 : exp (ary '{128} (ary '{96} (ary '{3} (ary '{3} num)))))
          (i3a_b2 : exp (ary '{128} num))
          (i3a_w3r : exp (ary '{16} (ary '{192} (ary '{1} (ary '{1} num)))))
          (i3a_b3r : exp (ary '{16} num))
          (i3a_w3 : exp (ary '{32} (ary '{16} (ary '{5} (ary '{5} num)))))
          (i3a_b3 : exp (ary '{32} num))
          (i3a_w4 : exp (ary '{32} (ary '{192} (ary '{1} (ary '{1} num)))))
          (i3a_b4 : exp (ary '{32} num)).
  (* Inception 3b: 64+128+32+32 -> 128+192+96+64 *)
  Context (i3b_w1 : exp (ary '{128} (ary '{64+128+32+32} (ary '{1} (ary '{1} num)))))
          (i3b_b1 : exp (ary '{128} num))
          (i3b_w2r : exp (ary '{128} (ary '{64+128+32+32} (ary '{1} (ary '{1} num)))))
          (i3b_b2r : exp (ary '{128} num))
          (i3b_w2 : exp (ary '{192} (ary '{128} (ary '{3} (ary '{3} num)))))
          (i3b_b2 : exp (ary '{192} num))
          (i3b_w3r : exp (ary '{32} (ary '{64+128+32+32} (ary '{1} (ary '{1} num)))))
          (i3b_b3r : exp (ary '{32} num))
          (i3b_w3 : exp (ary '{96} (ary '{32} (ary '{5} (ary '{5} num)))))
          (i3b_b3 : exp (ary '{96} num))
          (i3b_w4 : exp (ary '{64} (ary '{64+128+32+32} (ary '{1} (ary '{1} num)))))
          (i3b_b4 : exp (ary '{64} num)).
  (* Inception 4a: 128+192+96+64 -> 192+208+48+64 *)
  Context (i4a_w1 : exp (ary '{192} (ary '{128+192+96+64} (ary '{1} (ary '{1} num)))))
          (i4a_b1 : exp (ary '{192} num))
          (i4a_w2r : exp (ary '{96} (ary '{128+192+96+64} (ary '{1} (ary '{1} num)))))
          (i4a_b2r : exp (ary '{96} num))
          (i4a_w2 : exp (ary '{208} (ary '{96} (ary '{3} (ary '{3} num)))))
          (i4a_b2 : exp (ary '{208} num))
          (i4a_w3r : exp (ary '{16} (ary '{128+192+96+64} (ary '{1} (ary '{1} num)))))
          (i4a_b3r : exp (ary '{16} num))
          (i4a_w3 : exp (ary '{48} (ary '{16} (ary '{5} (ary '{5} num)))))
          (i4a_b3 : exp (ary '{48} num))
          (i4a_w4 : exp (ary '{64} (ary '{128+192+96+64} (ary '{1} (ary '{1} num)))))
          (i4a_b4 : exp (ary '{64} num)).
  (* Inception 4b: 192+208+48+64 -> 160+224+64+64 *)
  Context (i4b_w1 : exp (ary '{160} (ary '{192+208+48+64} (ary '{1} (ary '{1} num)))))
          (i4b_b1 : exp (ary '{160} num))
          (i4b_w2r : exp (ary '{112} (ary '{192+208+48+64} (ary '{1} (ary '{1} num)))))
          (i4b_b2r : exp (ary '{112} num))
          (i4b_w2 : exp (ary '{224} (ary '{112} (ary '{3} (ary '{3} num)))))
          (i4b_b2 : exp (ary '{224} num))
          (i4b_w3r : exp (ary '{24} (ary '{192+208+48+64} (ary '{1} (ary '{1} num)))))
          (i4b_b3r : exp (ary '{24} num))
          (i4b_w3 : exp (ary '{64} (ary '{24} (ary '{5} (ary '{5} num)))))
          (i4b_b3 : exp (ary '{64} num))
          (i4b_w4 : exp (ary '{64} (ary '{192+208+48+64} (ary '{1} (ary '{1} num)))))
          (i4b_b4 : exp (ary '{64} num)).
  (* Inception 4c: 160+224+64+64 -> 128+256+64+64 *)
  Context (i4c_w1 : exp (ary '{128} (ary '{160+224+64+64} (ary '{1} (ary '{1} num)))))
          (i4c_b1 : exp (ary '{128} num))
          (i4c_w2r : exp (ary '{128} (ary '{160+224+64+64} (ary '{1} (ary '{1} num)))))
          (i4c_b2r : exp (ary '{128} num))
          (i4c_w2 : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
          (i4c_b2 : exp (ary '{256} num))
          (i4c_w3r : exp (ary '{24} (ary '{160+224+64+64} (ary '{1} (ary '{1} num)))))
          (i4c_b3r : exp (ary '{24} num))
          (i4c_w3 : exp (ary '{64} (ary '{24} (ary '{5} (ary '{5} num)))))
          (i4c_b3 : exp (ary '{64} num))
          (i4c_w4 : exp (ary '{64} (ary '{160+224+64+64} (ary '{1} (ary '{1} num)))))
          (i4c_b4 : exp (ary '{64} num)).
  (* Inception 4d: 128+256+64+64 -> 112+288+64+64 *)
  Context (i4d_w1 : exp (ary '{112} (ary '{128+256+64+64} (ary '{1} (ary '{1} num)))))
          (i4d_b1 : exp (ary '{112} num))
          (i4d_w2r : exp (ary '{144} (ary '{128+256+64+64} (ary '{1} (ary '{1} num)))))
          (i4d_b2r : exp (ary '{144} num))
          (i4d_w2 : exp (ary '{288} (ary '{144} (ary '{3} (ary '{3} num)))))
          (i4d_b2 : exp (ary '{288} num))
          (i4d_w3r : exp (ary '{32} (ary '{128+256+64+64} (ary '{1} (ary '{1} num)))))
          (i4d_b3r : exp (ary '{32} num))
          (i4d_w3 : exp (ary '{64} (ary '{32} (ary '{5} (ary '{5} num)))))
          (i4d_b3 : exp (ary '{64} num))
          (i4d_w4 : exp (ary '{64} (ary '{128+256+64+64} (ary '{1} (ary '{1} num)))))
          (i4d_b4 : exp (ary '{64} num)).
  (* Inception 4e: 112+288+64+64 -> 256+320+128+128 *)
  Context (i4e_w1 : exp (ary '{256} (ary '{112+288+64+64} (ary '{1} (ary '{1} num)))))
          (i4e_b1 : exp (ary '{256} num))
          (i4e_w2r : exp (ary '{160} (ary '{112+288+64+64} (ary '{1} (ary '{1} num)))))
          (i4e_b2r : exp (ary '{160} num))
          (i4e_w2 : exp (ary '{320} (ary '{160} (ary '{3} (ary '{3} num)))))
          (i4e_b2 : exp (ary '{320} num))
          (i4e_w3r : exp (ary '{32} (ary '{112+288+64+64} (ary '{1} (ary '{1} num)))))
          (i4e_b3r : exp (ary '{32} num))
          (i4e_w3 : exp (ary '{128} (ary '{32} (ary '{5} (ary '{5} num)))))
          (i4e_b3 : exp (ary '{128} num))
          (i4e_w4 : exp (ary '{128} (ary '{112+288+64+64} (ary '{1} (ary '{1} num)))))
          (i4e_b4 : exp (ary '{128} num)).
  (* Inception 5a: 256+320+128+128 -> 256+320+128+128 *)
  Context (i5a_w1 : exp (ary '{256} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5a_b1 : exp (ary '{256} num))
          (i5a_w2r : exp (ary '{160} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5a_b2r : exp (ary '{160} num))
          (i5a_w2 : exp (ary '{320} (ary '{160} (ary '{3} (ary '{3} num)))))
          (i5a_b2 : exp (ary '{320} num))
          (i5a_w3r : exp (ary '{32} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5a_b3r : exp (ary '{32} num))
          (i5a_w3 : exp (ary '{128} (ary '{32} (ary '{5} (ary '{5} num)))))
          (i5a_b3 : exp (ary '{128} num))
          (i5a_w4 : exp (ary '{128} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5a_b4 : exp (ary '{128} num)).
  (* Inception 5b: 256+320+128+128 -> 384+384+128+128 *)
  Context (i5b_w1 : exp (ary '{384} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5b_b1 : exp (ary '{384} num))
          (i5b_w2r : exp (ary '{192} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5b_b2r : exp (ary '{192} num))
          (i5b_w2 : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
          (i5b_b2 : exp (ary '{384} num))
          (i5b_w3r : exp (ary '{48} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5b_b3r : exp (ary '{48} num))
          (i5b_w3 : exp (ary '{128} (ary '{48} (ary '{5} (ary '{5} num)))))
          (i5b_b3 : exp (ary '{128} num))
          (i5b_w4 : exp (ary '{128} (ary '{256+320+128+128} (ary '{1} (ary '{1} num)))))
          (i5b_b4 : exp (ary '{128} num)).

  (* Classifier *)
  Context (fc_w : exp (ary '{1000} (ary '{384+384+128+128} num)))
          (fc_b : exp (ary '{1000} num)).

  (* ---------------- Functional GoogLeNet (opaque layer wrappers) ---------
     Each layer value is a separate definition; after the body lemmas they
     are made [Opaque] so that the network-level proofs never inline a layer
     into the next one (quadratic/exponential goal blow-up otherwise). *)
  Definition gn_x1 := Conv4d_p3_k7_s2 input c1_w c1_b.
  Definition gn_x2 := ReLU4d gn_x1.
  Definition gn_x3 := Maxpool4d_pad 3 2 1 gn_x2.
  Definition gn_x4 := Conv4d_3x3_s1 c2_b c2_w gn_x3.
  Definition gn_x5 := ReLU4d gn_x4.
  Definition gn_x6 := Maxpool4d_pad 3 2 1 gn_x5.
  Definition gn_x7 := Inception_id gn_x6 i3a_w1 i3a_b1 i3a_w2r i3a_b2r i3a_w2 i3a_b2 i3a_w3r i3a_b3r i3a_w3 i3a_b3 i3a_w4 i3a_b4.
  Definition gn_x8 := Inception_id gn_x7 i3b_w1 i3b_b1 i3b_w2r i3b_b2r i3b_w2 i3b_b2 i3b_w3r i3b_b3r i3b_w3 i3b_b3 i3b_w4 i3b_b4.
  Definition gn_x9 := Inception_id gn_x8 i4a_w1 i4a_b1 i4a_w2r i4a_b2r i4a_w2 i4a_b2 i4a_w3r i4a_b3r i4a_w3 i4a_b3 i4a_w4 i4a_b4.
  Definition gn_x10 := Maxpool4d_pad 3 2 1 gn_x9.
  Definition gn_x11 := Inception_id gn_x10 i4b_w1 i4b_b1 i4b_w2r i4b_b2r i4b_w2 i4b_b2 i4b_w3r i4b_b3r i4b_w3 i4b_b3 i4b_w4 i4b_b4.
  Definition gn_x12 := Inception_id gn_x11 i4c_w1 i4c_b1 i4c_w2r i4c_b2r i4c_w2 i4c_b2 i4c_w3r i4c_b3r i4c_w3 i4c_b3 i4c_w4 i4c_b4.
  Definition gn_x13 := Inception_id gn_x12 i4d_w1 i4d_b1 i4d_w2r i4d_b2r i4d_w2 i4d_b2 i4d_w3r i4d_b3r i4d_w3 i4d_b3 i4d_w4 i4d_b4.
  Definition gn_x14 := Maxpool4d_pad 3 2 1 gn_x13.
  Definition gn_x15 := Inception_id gn_x14 i4e_w1 i4e_b1 i4e_w2r i4e_b2r i4e_w2 i4e_b2 i4e_w3r i4e_b3r i4e_w3 i4e_b3 i4e_w4 i4e_b4.
  Definition gn_x16 := Inception_id gn_x15 i5a_w1 i5a_b1 i5a_w2r i5a_b2r i5a_w2 i5a_b2 i5a_w3r i5a_b3r i5a_w3 i5a_b3 i5a_w4 i5a_b4.
  Definition gn_x17 := Inception_id gn_x16 i5b_w1 i5b_b1 i5b_w2r i5b_b2r i5b_w2 i5b_b2 i5b_w3r i5b_b3r i5b_w3 i5b_b3 i5b_w4 i5b_b4.
  Definition gn_x18 := GlobalAvgPool4d gn_x17.
  Definition gn_x19 := Softmax2d (Linear2d fc_w fc_b gn_x18).

  Lemma gn_x1_body : gn_x1 = Conv4d_p3_k7_s2 input c1_w c1_b.
  Proof. reflexivity. Qed.
  Lemma gn_x2_body : gn_x2 = ReLU4d gn_x1.
  Proof. reflexivity. Qed.
  Lemma gn_x3_body : gn_x3 = Maxpool4d_pad 3 2 1 gn_x2.
  Proof. reflexivity. Qed.
  Lemma gn_x4_body : gn_x4 = Conv4d_3x3_s1 c2_b c2_w gn_x3.
  Proof. reflexivity. Qed.
  Lemma gn_x5_body : gn_x5 = ReLU4d gn_x4.
  Proof. reflexivity. Qed.
  Lemma gn_x6_body : gn_x6 = Maxpool4d_pad 3 2 1 gn_x5.
  Proof. reflexivity. Qed.
  Lemma gn_x7_body : gn_x7 = Inception_id gn_x6 i3a_w1 i3a_b1 i3a_w2r i3a_b2r i3a_w2 i3a_b2 i3a_w3r i3a_b3r i3a_w3 i3a_b3 i3a_w4 i3a_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x8_body : gn_x8 = Inception_id gn_x7 i3b_w1 i3b_b1 i3b_w2r i3b_b2r i3b_w2 i3b_b2 i3b_w3r i3b_b3r i3b_w3 i3b_b3 i3b_w4 i3b_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x9_body : gn_x9 = Inception_id gn_x8 i4a_w1 i4a_b1 i4a_w2r i4a_b2r i4a_w2 i4a_b2 i4a_w3r i4a_b3r i4a_w3 i4a_b3 i4a_w4 i4a_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x10_body : gn_x10 = Maxpool4d_pad 3 2 1 gn_x9.
  Proof. reflexivity. Qed.
  Lemma gn_x11_body : gn_x11 = Inception_id gn_x10 i4b_w1 i4b_b1 i4b_w2r i4b_b2r i4b_w2 i4b_b2 i4b_w3r i4b_b3r i4b_w3 i4b_b3 i4b_w4 i4b_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x12_body : gn_x12 = Inception_id gn_x11 i4c_w1 i4c_b1 i4c_w2r i4c_b2r i4c_w2 i4c_b2 i4c_w3r i4c_b3r i4c_w3 i4c_b3 i4c_w4 i4c_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x13_body : gn_x13 = Inception_id gn_x12 i4d_w1 i4d_b1 i4d_w2r i4d_b2r i4d_w2 i4d_b2 i4d_w3r i4d_b3r i4d_w3 i4d_b3 i4d_w4 i4d_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x14_body : gn_x14 = Maxpool4d_pad 3 2 1 gn_x13.
  Proof. reflexivity. Qed.
  Lemma gn_x15_body : gn_x15 = Inception_id gn_x14 i4e_w1 i4e_b1 i4e_w2r i4e_b2r i4e_w2 i4e_b2 i4e_w3r i4e_b3r i4e_w3 i4e_b3 i4e_w4 i4e_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x16_body : gn_x16 = Inception_id gn_x15 i5a_w1 i5a_b1 i5a_w2r i5a_b2r i5a_w2 i5a_b2 i5a_w3r i5a_b3r i5a_w3 i5a_b3 i5a_w4 i5a_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x17_body : gn_x17 = Inception_id gn_x16 i5b_w1 i5b_b1 i5b_w2r i5b_b2r i5b_w2 i5b_b2 i5b_w3r i5b_b3r i5b_w3 i5b_b3 i5b_w4 i5b_b4.
  Proof. reflexivity. Qed.
  Lemma gn_x18_body : gn_x18 = GlobalAvgPool4d gn_x17.
  Proof. reflexivity. Qed.
  Lemma gn_x19_body : gn_x19 = Softmax2d (Linear2d fc_w fc_b gn_x18).
  Proof. reflexivity. Qed.

  Opaque gn_x1 gn_x2 gn_x3 gn_x4 gn_x5 gn_x6 gn_x7 gn_x8 gn_x9 gn_x10 gn_x11 gn_x12 gn_x13 gn_x14 gn_x15 gn_x16 gn_x17 gn_x18 gn_x19.

  Definition GoogLeNet : exp (ary '{batch} (ary '{1000} num)) := gn_x19.

  (* ---------------- Imperative GoogLeNet (buffer-layered) ---------------- *)

  Definition googlenet_comm (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
new (fun t1 => seq (Conv4d_p3_k7_s2_comm input c1_w c1_b t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => ReLU4d_comm e1 t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Maxpool4d_pad_comm 3 2 1 e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_3x3_s1_comm c2_b c2_w e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => ReLU4d_comm e4 t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Maxpool4d_pad_comm 3 2 1 e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => inception_id_comm e6 i3a_w1 i3a_b1 i3a_w2r i3a_b2r i3a_w2 i3a_b2 i3a_w3r i3a_b3r i3a_w3 i3a_b3 i3a_w4 i3a_b4 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => inception_id_comm e7 i3b_w1 i3b_b1 i3b_w2r i3b_b2r i3b_w2 i3b_b2 i3b_w3r i3b_b3r i3b_w3 i3b_b3 i3b_w4 i3b_b4 t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => inception_id_comm e8 i4a_w1 i4a_b1 i4a_w2r i4a_b2r i4a_w2 i4a_b2 i4a_w3r i4a_b3r i4a_w3 i4a_b3 i4a_w4 i4a_b4 t9))
(new (fun t10 => seq (bind_read t9 (fun e9 => Maxpool4d_pad_comm 3 2 1 e9 t10))
(new (fun t11 => seq (bind_read t10 (fun e10 => inception_id_comm e10 i4b_w1 i4b_b1 i4b_w2r i4b_b2r i4b_w2 i4b_b2 i4b_w3r i4b_b3r i4b_w3 i4b_b3 i4b_w4 i4b_b4 t11))
(new (fun t12 => seq (bind_read t11 (fun e11 => inception_id_comm e11 i4c_w1 i4c_b1 i4c_w2r i4c_b2r i4c_w2 i4c_b2 i4c_w3r i4c_b3r i4c_w3 i4c_b3 i4c_w4 i4c_b4 t12))
(new (fun t13 => seq (bind_read t12 (fun e12 => inception_id_comm e12 i4d_w1 i4d_b1 i4d_w2r i4d_b2r i4d_w2 i4d_b2 i4d_w3r i4d_b3r i4d_w3 i4d_b3 i4d_w4 i4d_b4 t13))
(new (fun t14 => seq (bind_read t13 (fun e13 => Maxpool4d_pad_comm 3 2 1 e13 t14))
(new (fun t15 => seq (bind_read t14 (fun e14 => inception_id_comm e14 i4e_w1 i4e_b1 i4e_w2r i4e_b2r i4e_w2 i4e_b2 i4e_w3r i4e_b3r i4e_w3 i4e_b3 i4e_w4 i4e_b4 t15))
(new (fun t16 => seq (bind_read t15 (fun e15 => inception_id_comm e15 i5a_w1 i5a_b1 i5a_w2r i5a_b2r i5a_w2 i5a_b2 i5a_w3r i5a_b3r i5a_w3 i5a_b3 i5a_w4 i5a_b4 t16))
(new (fun t17 => seq (bind_read t16 (fun e16 => inception_id_comm e16 i5b_w1 i5b_b1 i5b_w2r i5b_b2r i5b_w2 i5b_b2 i5b_w3r i5b_b3r i5b_w3 i5b_b3 i5b_w4 i5b_b4 t17))
(new (fun t18 => seq (bind_read t17 (fun e17 => GlobalAvgPool4d_comm e17 t18))
     (bind_read t18 (fun e18 => Softmax2d_comm (Linear2d fc_w fc_b e18) output))
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

  Definition googlenet_comm_direct (output : acc (ary '{batch} (ary '{1000} num)))
    : comm :=
    seq (A(acc' (Var "l1"), gn_x1))
    (seq (A(acc' (Var "l2"), gn_x2))
    (seq (A(acc' (Var "l3"), gn_x3))
    (seq (A(acc' (Var "l4"), gn_x4))
    (seq (A(acc' (Var "l5"), gn_x5))
    (seq (A(acc' (Var "l6"), gn_x6))
    (seq (inception_id_direct gn_x6 i3a_w1 i3a_b1 i3a_w2r i3a_b2r i3a_w2 i3a_b2 i3a_w3r i3a_b3r i3a_w3 i3a_b3 i3a_w4 i3a_b4 (acc' (Var "l7")))
    (seq (inception_id_direct gn_x7 i3b_w1 i3b_b1 i3b_w2r i3b_b2r i3b_w2 i3b_b2 i3b_w3r i3b_b3r i3b_w3 i3b_b3 i3b_w4 i3b_b4 (acc' (Var "l8")))
    (seq (inception_id_direct gn_x8 i4a_w1 i4a_b1 i4a_w2r i4a_b2r i4a_w2 i4a_b2 i4a_w3r i4a_b3r i4a_w3 i4a_b3 i4a_w4 i4a_b4 (acc' (Var "l9")))
    (seq (A(acc' (Var "l10"), gn_x10))
    (seq (inception_id_direct gn_x10 i4b_w1 i4b_b1 i4b_w2r i4b_b2r i4b_w2 i4b_b2 i4b_w3r i4b_b3r i4b_w3 i4b_b3 i4b_w4 i4b_b4 (acc' (Var "l11")))
    (seq (inception_id_direct gn_x11 i4c_w1 i4c_b1 i4c_w2r i4c_b2r i4c_w2 i4c_b2 i4c_w3r i4c_b3r i4c_w3 i4c_b3 i4c_w4 i4c_b4 (acc' (Var "l12")))
    (seq (inception_id_direct gn_x12 i4d_w1 i4d_b1 i4d_w2r i4d_b2r i4d_w2 i4d_b2 i4d_w3r i4d_b3r i4d_w3 i4d_b3 i4d_w4 i4d_b4 (acc' (Var "l13")))
    (seq (A(acc' (Var "l14"), gn_x14))
    (seq (inception_id_direct gn_x14 i4e_w1 i4e_b1 i4e_w2r i4e_b2r i4e_w2 i4e_b2 i4e_w3r i4e_b3r i4e_w3 i4e_b3 i4e_w4 i4e_b4 (acc' (Var "l15")))
    (seq (inception_id_direct gn_x15 i5a_w1 i5a_b1 i5a_w2r i5a_b2r i5a_w2 i5a_b2 i5a_w3r i5a_b3r i5a_w3 i5a_b3 i5a_w4 i5a_b4 (acc' (Var "l16")))
    (seq (inception_id_direct gn_x16 i5b_w1 i5b_b1 i5b_w2r i5b_b2r i5b_w2 i5b_b2 i5b_w3r i5b_b3r i5b_w3 i5b_b3 i5b_w4 i5b_b4 (acc' (Var "l17")))
    (seq (A(acc' (Var "l18"), gn_x18))
    ((A(output, gn_x19)))))))))))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition r1_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{batch} (ary '{64} (ary '{s_stem m} (ary '{s_stem m} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{batch} (ary '{64} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{batch} (ary '{192} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{batch} (ary '{192} (ary '{s_pool m} (ary '{s_pool m} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{batch} (ary '{192} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{batch} (ary '{64+128+32+32} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l7").
  Definition r8_acc : acc (ary '{batch} (ary '{128+192+96+64} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l8").
  Definition r9_acc : acc (ary '{batch} (ary '{192+208+48+64} (ary '{s_pool2 m} (ary '{s_pool2 m} num))))
    := acc' (Var "l9").
  Definition r10_acc : acc (ary '{batch} (ary '{192+208+48+64} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l10").
  Definition r11_acc : acc (ary '{batch} (ary '{160+224+64+64} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{batch} (ary '{128+256+64+64} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{batch} (ary '{112+288+64+64} (ary '{s_pool3 m} (ary '{s_pool3 m} num))))
    := acc' (Var "l13").
  Definition r14_acc : acc (ary '{batch} (ary '{112+288+64+64} (ary '{s_pool4 m} (ary '{s_pool4 m} num))))
    := acc' (Var "l14").
  Definition r15_acc : acc (ary '{batch} (ary '{256+320+128+128} (ary '{s_pool4 m} (ary '{s_pool4 m} num))))
    := acc' (Var "l15").
  Definition r16_acc : acc (ary '{batch} (ary '{256+320+128+128} (ary '{s_pool4 m} (ary '{s_pool4 m} num))))
    := acc' (Var "l16").
  Definition r17_acc : acc (ary '{batch} (ary '{384+384+128+128} (ary '{s_pool4 m} (ary '{s_pool4 m} num))))
    := acc' (Var "l17").
  Definition r18_acc : acc (ary '{batch} (ary '{384+384+128+128} num))
    := acc' (Var "l18").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries it1..it13 are shared between blocks and are required to be
     fresh at every type. *)
  Definition googlenet_fresh
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
    (forall d : data, StructUndefined (acc' (Var "it1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it5") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it6") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it7") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it8") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it9") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it10") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it11") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it12") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "it13") : acc d) rho) /\
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
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it5") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it6") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it7") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it8") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it9") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it10") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it11") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it12") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "it13") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  (* The proof keeps the goal small throughout: layer values are folded to
     their opaque [gn_xK] constants as soon as they are assigned, and block
     direct forms are never unfolded at the network level
     ([inception_id_direct_read] advances past them). *)
  Lemma googlenet_comm_eq_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num))),
    googlenet_comm output = googlenet_comm_direct output.
  Proof.
    intros.
    unfold googlenet_comm, googlenet_comm_direct, new.
    cbv beta.
    rewrite <- A_Conv4d_p3_k7_s2.
    rewrite <- gn_x1_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_ReLU4d.
    rewrite <- gn_x2_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- gn_x3_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Conv4d_3x3_s1.
    rewrite <- gn_x4_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_ReLU4d.
    rewrite <- gn_x5_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- gn_x6_body.
    rewrite bind_read_replace_seq.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x7_body.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x8_body.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x9_body.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- gn_x10_body.
    rewrite bind_read_replace_seq.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x11_body.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x12_body.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x13_body.
    rewrite <- A_Maxpool4d_pad.
    rewrite <- gn_x14_body.
    rewrite bind_read_replace_seq.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x15_body.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x16_body.
    rewrite inception_id_comm_eq_direct.
    rewrite inception_id_direct_read.
    rewrite <- gn_x17_body.
    rewrite <- A_GlobalAvgPool4d.
    rewrite <- gn_x18_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    rewrite <- gn_x19_body.
    reflexivity.
  Qed.

  Lemma A_GoogLeNet_direct :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    googlenet_fresh output rho ->
    googlenet_comm_direct output rho p = A(output, GoogLeNet) rho p.
  Proof.
    intros.
    unfold googlenet_comm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold GoogLeNet. reflexivity.
  Qed.

  Theorem A_GoogLeNet :
    forall (output : acc (ary '{batch} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    googlenet_fresh output rho ->
    googlenet_comm output rho p = A(output, GoogLeNet) rho p.
  Proof.
    intros. rewrite googlenet_comm_eq_direct.
    apply A_GoogLeNet_direct; assumption.
  Qed.

End GoogLeNet.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Conv4d_5x5_s1.
Print Assumptions A_Maxpool4d_3x3_s1.
Print Assumptions A_Inception_id.
Print Assumptions A_GoogLeNet.
