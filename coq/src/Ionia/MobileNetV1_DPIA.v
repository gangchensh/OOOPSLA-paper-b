(* DPIA-style end-to-end Leibniz correctness proof for MobileNetV1 (route A).

   Structure: classic MobileNetV1 in 4d batched form, batch = 1, spatial size
   symbolic (m):
     stem conv(3x3,p1,s2) - bn - relu                       (channel -> 32)
     13 x DW-PW block, each block =
       DWConv(3x3) - bn - relu - Conv(1x1 pointwise) - bn - relu
     channels 32->64->128->128->256->256->512->512(x5)->1024->1024,
     stride 2 on the DW conv of blocks 2, 4, 6 and 12
     (64->128, 128->256, 256->512, 512->1024)
     GlobalAvgPool - fc(1000) - softmax

   The depthwise convolutions reuse the proved generic [A_DWConv4d] design of
   Ops_Concat.v, but (as with the convolutions in ResNet18_DPIA.v) the generic
   output-size expression [(m - 3 + 2*1)/s + 1] is not definitionally equal to
   the canonical sizes [m] resp. [half m = (m+1)/2] used to compose layers;
   the blocks therefore use canonical-size variants [DWConv4d_3x3_s1] /
   [DWConv4d_3x3_s2] defined here with identical indexing, proved exactly like
   [A_DWConv4d].  The pointwise 1x1 convolutions reuse [Conv4d_1x1_s1] of
   ResNet50_DPIA.v; the stem reuses [Conv4d_3x3_s2] of ResNet18_DPIA.v.

   As in ResNet50_DPIA.v, each block combinator [dwpwblock_*_comm] is proved
   equal to a buffer-free "direct" form ([dwpwblock_*_comm_eq_direct]); the
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
Require Import Ionia.Ops_Concat.
Require Import Ionia.ResNet18_DPIA.
Require Import Ionia.ResNet50_DPIA.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* DWConv4d_3x3_s1 : same-size depthwise 3x3 convolution, padding 1, stride 1 *)
(* -------------------------------------------------------------------------- *)

Definition DWConv4d_3x3_s1 {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{3} (ary '{3} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun ch : fin c =>
    mkvSeq (fun i0 : fin m1 => mkvSeq (fun j0 : fin m2 =>
      sum (mkvSeq (fun i1 : fin 3 =>
        sum (mkvSeq (fun j1 : fin 3 =>
          mul (idx (idx (idx w ch) i1) j1)
              (pad_idx2d 1 (idx (idx input b) ch)
                         (fin2nat i0 + fin2nat i1)
                         (fin2nat j0 + fin2nat j1)))))))))).

Definition DWConv4d_3x3_s1_comm {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{3} (ary '{3} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun ch oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun i1 : fin 3 =>
             sum (mkvSeq (fun j1 : fin 3 =>
               mul (idx (idx (idx w ch) i1) j1)
                   (pad_idx2d 1 (idx (idx input b) ch)
                              (fin2nat i0 + fin2nat i1)
                              (fin2nat j0 + fin2nat j1))))))
           (fun r : exp num => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_DWConv4d_3x3_s1 : forall (batch c m1 m2 : nat)
  (w : exp (ary '{c} (ary '{3} (ary '{3} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  A(output, DWConv4d_3x3_s1 w input) = DWConv4d_3x3_s1_comm w input output.
Proof.
  intros. unfold DWConv4d_3x3_s1, DWConv4d_3x3_s1_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ch.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* DWConv4d_3x3_s2 : depthwise 3x3 convolution, padding 1, stride 2, [half]   *)
(* -------------------------------------------------------------------------- *)

Definition DWConv4d_3x3_s2 {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{3} (ary '{3} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{c} (ary '{half m1} (ary '{half m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun ch : fin c =>
    mkvSeq (fun i0 : fin (half m1) => mkvSeq (fun j0 : fin (half m2) =>
      sum (mkvSeq (fun i1 : fin 3 =>
        sum (mkvSeq (fun j1 : fin 3 =>
          mul (idx (idx (idx w ch) i1) j1)
              (pad_idx2d 1 (idx (idx input b) ch)
                         (fin2nat i0 * 2 + fin2nat i1)
                         (fin2nat j0 * 2 + fin2nat j1)))))))))).

Definition DWConv4d_3x3_s2_comm {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{3} (ary '{3} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun ch oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun i1 : fin 3 =>
             sum (mkvSeq (fun j1 : fin 3 =>
               mul (idx (idx (idx w ch) i1) j1)
                   (pad_idx2d 1 (idx (idx input b) ch)
                              (fin2nat i0 * 2 + fin2nat i1)
                              (fin2nat j0 * 2 + fin2nat j1))))))
           (fun r : exp num => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_DWConv4d_3x3_s2 : forall (batch c m1 m2 : nat)
  (w : exp (ary '{c} (ary '{3} (ary '{3} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{half m1} (ary '{half m2} num))))),
  A(output, DWConv4d_3x3_s2 w input) = DWConv4d_3x3_s2_comm w input output.
Proof.
  intros. unfold DWConv4d_3x3_s2, DWConv4d_3x3_s2_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro ch.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* DW-PW block, stride 1 (DWConv 3x3 s1 - BN - ReLU - Conv 1x1 - BN - ReLU)   *)
(* -------------------------------------------------------------------------- *)

Definition DWPWBlock_s1 {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  let d1 := DWConv4d_3x3_s1 wdw input in
  let n1 := BatchNorm4d d1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let p1 := Conv4d_1x1_s1 bpw wpw r1 in
  let n2 := BatchNorm4d p1 g2 z2 eps in
  ReLU4d n2.

(* Imperative block: temporaries bt1..bt5, output written in place. *)
Definition dwpwblock_s1_comm {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (DWConv4d_3x3_s1_comm wdw input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_1x1_s1_comm bpw wpw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
     (bind_read t5 (fun e5 => ReLU4d_comm e5 output))
) (acc' (Var "bt5")))
) (acc' (Var "bt4")))
) (acc' (Var "bt3")))
) (acc' (Var "bt2")))
) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition dwpwblock_s1_direct {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let d1 := DWConv4d_3x3_s1 wdw input in
  let n1 := BatchNorm4d d1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let p1 := Conv4d_1x1_s1 bpw wpw r1 in
  let n2 := BatchNorm4d p1 g2 z2 eps in
  seq (seq (seq (seq (seq (A(acc' (Var "bt1"), d1))
                          (A(acc' (Var "bt2"), n1)))
                          (A(acc' (Var "bt3"), r1)))
                          (A(acc' (Var "bt4"), p1)))
                          (A(acc' (Var "bt5"), n2)))
       (A(output, DWPWBlock_s1 input wdw g1 z1 wpw bpw g2 z2 eps)).

Lemma dwpwblock_s1_comm_eq_direct : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  dwpwblock_s1_comm input wdw g1 z1 wpw bpw g2 z2 eps output =
  dwpwblock_s1_direct input wdw g1 z1 wpw bpw g2 z2 eps output.
Proof.
  intros.
  unfold dwpwblock_s1_comm, dwpwblock_s1_direct, new.
  cbv zeta beta.
  rewrite <- A_DWConv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [DWPWBlock_s1]. *)
Lemma A_DWPWBlock_s1 : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  dwpwblock_s1_comm input wdw g1 z1 wpw bpw g2 z2 eps output rho p =
  A(output, DWPWBlock_s1 input wdw g1 z1 wpw bpw g2 z2 eps) rho p.
Proof.
  intros. rewrite dwpwblock_s1_comm_eq_direct.
  unfold dwpwblock_s1_direct, DWPWBlock_s1, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value.  This lets the network-level proof advance
   past a block without ever unfolding its direct form. *)
Lemma dwpwblock_s1_direct_read : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (dwpwblock_s1_direct input wdw g1 z1 wpw bpw g2 z2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (dwpwblock_s1_direct input wdw g1 z1 wpw bpw g2 z2 eps (acc' q))
      (seq (k (DWPWBlock_s1 input wdw g1 z1 wpw bpw g2 z2 eps)) c0).
Proof.
  intros. unfold dwpwblock_s1_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* DW-PW block, stride 2 (DWConv 3x3 s2 - BN - ReLU - Conv 1x1 - BN - ReLU)   *)
(* -------------------------------------------------------------------------- *)

Definition DWPWBlock_s2 {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  let d1 := DWConv4d_3x3_s2 wdw input in
  let n1 := BatchNorm4d d1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let p1 := Conv4d_1x1_s1 bpw wpw r1 in
  let n2 := BatchNorm4d p1 g2 z2 eps in
  ReLU4d n2.

(* Imperative block: temporaries bt1..bt5, output written in place. *)
Definition dwpwblock_s2_comm {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
new (fun t1 => seq (DWConv4d_3x3_s2_comm wdw input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Conv4d_1x1_s1_comm bpw wpw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
     (bind_read t5 (fun e5 => ReLU4d_comm e5 output))
) (acc' (Var "bt5")))
) (acc' (Var "bt4")))
) (acc' (Var "bt3")))
) (acc' (Var "bt2")))
) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition dwpwblock_s2_direct {batch inch outch m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  let d1 := DWConv4d_3x3_s2 wdw input in
  let n1 := BatchNorm4d d1 g1 z1 eps in
  let r1 := ReLU4d n1 in
  let p1 := Conv4d_1x1_s1 bpw wpw r1 in
  let n2 := BatchNorm4d p1 g2 z2 eps in
  seq (seq (seq (seq (seq (A(acc' (Var "bt1"), d1))
                          (A(acc' (Var "bt2"), n1)))
                          (A(acc' (Var "bt3"), r1)))
                          (A(acc' (Var "bt4"), p1)))
                          (A(acc' (Var "bt5"), n2)))
       (A(output, DWPWBlock_s2 input wdw g1 z1 wpw bpw g2 z2 eps)).

Lemma dwpwblock_s2_comm_eq_direct : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  dwpwblock_s2_comm input wdw g1 z1 wpw bpw g2 z2 eps output =
  dwpwblock_s2_direct input wdw g1 z1 wpw bpw g2 z2 eps output.
Proof.
  intros.
  unfold dwpwblock_s2_comm, dwpwblock_s2_direct, new.
  cbv zeta beta.
  rewrite <- A_DWConv4d_3x3_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_ReLU4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [DWPWBlock_s2]. *)
Lemma A_DWPWBlock_s2 : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  dwpwblock_s2_comm input wdw g1 z1 wpw bpw g2 z2 eps output rho p =
  A(output, DWPWBlock_s2 input wdw g1 z1 wpw bpw g2 z2 eps) rho p.
Proof.
  intros. rewrite dwpwblock_s2_comm_eq_direct.
  unfold dwpwblock_s2_direct, DWPWBlock_s2, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma dwpwblock_s2_direct_read : forall (batch inch outch m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) -> comm) (c0 : comm),
  seq (dwpwblock_s2_direct input wdw g1 z1 wpw bpw g2 z2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (dwpwblock_s2_direct input wdw g1 z1 wpw bpw g2 z2 eps (acc' q))
      (seq (k (DWPWBlock_s2 input wdw g1 z1 wpw bpw g2 z2 eps)) c0).
Proof.
  intros. unfold dwpwblock_s2_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MobileNetV1 (batch = 1, symbolic input channels and spatial size m)        *)
(* -------------------------------------------------------------------------- *)

Section MobileNetV1.
  Context {channel m : nat}.
  Context (input : exp (ary '{1} (ary '{channel} (ary '{m} (ary '{m} num))))).

  (* Stem: conv 3x3 p1 s2 + BN (channel -> 32) *)
  Context (s_w : exp (ary '{32} (ary '{channel} (ary '{3} (ary '{3} num)))))
          (s_b : exp (ary '{32} num))
          (s_g : exp (ary '{32} num)) (s_z : exp (ary '{32} num))
          (eps : exp num).

  (* Block 1 (s1, 32 -> 64) *)
  Context (d1_wdw : exp (ary '{32} (ary '{3} (ary '{3} num))))
          (d1_g1 d1_z1 : exp (ary '{32} num))
          (d1_wpw : exp (ary '{64} (ary '{32} (ary '{1} (ary '{1} num)))))
          (d1_bpw d1_g2 d1_z2 : exp (ary '{64} num)).
  (* Block 2 (s2, 64 -> 128) *)
  Context (d2_wdw : exp (ary '{64} (ary '{3} (ary '{3} num))))
          (d2_g1 d2_z1 : exp (ary '{64} num))
          (d2_wpw : exp (ary '{128} (ary '{64} (ary '{1} (ary '{1} num)))))
          (d2_bpw d2_g2 d2_z2 : exp (ary '{128} num)).
  (* Block 3 (s1, 128 -> 128) *)
  Context (d3_wdw : exp (ary '{128} (ary '{3} (ary '{3} num))))
          (d3_g1 d3_z1 : exp (ary '{128} num))
          (d3_wpw : exp (ary '{128} (ary '{128} (ary '{1} (ary '{1} num)))))
          (d3_bpw d3_g2 d3_z2 : exp (ary '{128} num)).
  (* Block 4 (s2, 128 -> 256) *)
  Context (d4_wdw : exp (ary '{128} (ary '{3} (ary '{3} num))))
          (d4_g1 d4_z1 : exp (ary '{128} num))
          (d4_wpw : exp (ary '{256} (ary '{128} (ary '{1} (ary '{1} num)))))
          (d4_bpw d4_g2 d4_z2 : exp (ary '{256} num)).
  (* Block 5 (s1, 256 -> 256) *)
  Context (d5_wdw : exp (ary '{256} (ary '{3} (ary '{3} num))))
          (d5_g1 d5_z1 : exp (ary '{256} num))
          (d5_wpw : exp (ary '{256} (ary '{256} (ary '{1} (ary '{1} num)))))
          (d5_bpw d5_g2 d5_z2 : exp (ary '{256} num)).
  (* Block 6 (s2, 256 -> 512) *)
  Context (d6_wdw : exp (ary '{256} (ary '{3} (ary '{3} num))))
          (d6_g1 d6_z1 : exp (ary '{256} num))
          (d6_wpw : exp (ary '{512} (ary '{256} (ary '{1} (ary '{1} num)))))
          (d6_bpw d6_g2 d6_z2 : exp (ary '{512} num)).
  (* Block 7 (s1, 512 -> 512) *)
  Context (d7_wdw : exp (ary '{512} (ary '{3} (ary '{3} num))))
          (d7_g1 d7_z1 : exp (ary '{512} num))
          (d7_wpw : exp (ary '{512} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d7_bpw d7_g2 d7_z2 : exp (ary '{512} num)).
  (* Block 8 (s1, 512 -> 512) *)
  Context (d8_wdw : exp (ary '{512} (ary '{3} (ary '{3} num))))
          (d8_g1 d8_z1 : exp (ary '{512} num))
          (d8_wpw : exp (ary '{512} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d8_bpw d8_g2 d8_z2 : exp (ary '{512} num)).
  (* Block 9 (s1, 512 -> 512) *)
  Context (d9_wdw : exp (ary '{512} (ary '{3} (ary '{3} num))))
          (d9_g1 d9_z1 : exp (ary '{512} num))
          (d9_wpw : exp (ary '{512} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d9_bpw d9_g2 d9_z2 : exp (ary '{512} num)).
  (* Block 10 (s1, 512 -> 512) *)
  Context (d10_wdw : exp (ary '{512} (ary '{3} (ary '{3} num))))
          (d10_g1 d10_z1 : exp (ary '{512} num))
          (d10_wpw : exp (ary '{512} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d10_bpw d10_g2 d10_z2 : exp (ary '{512} num)).
  (* Block 11 (s1, 512 -> 512) *)
  Context (d11_wdw : exp (ary '{512} (ary '{3} (ary '{3} num))))
          (d11_g1 d11_z1 : exp (ary '{512} num))
          (d11_wpw : exp (ary '{512} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d11_bpw d11_g2 d11_z2 : exp (ary '{512} num)).
  (* Block 12 (s2, 512 -> 1024) *)
  Context (d12_wdw : exp (ary '{512} (ary '{3} (ary '{3} num))))
          (d12_g1 d12_z1 : exp (ary '{512} num))
          (d12_wpw : exp (ary '{1024} (ary '{512} (ary '{1} (ary '{1} num)))))
          (d12_bpw d12_g2 d12_z2 : exp (ary '{1024} num)).
  (* Block 13 (s1, 1024 -> 1024) *)
  Context (d13_wdw : exp (ary '{1024} (ary '{3} (ary '{3} num))))
          (d13_g1 d13_z1 : exp (ary '{1024} num))
          (d13_wpw : exp (ary '{1024} (ary '{1024} (ary '{1} (ary '{1} num)))))
          (d13_bpw d13_g2 d13_z2 : exp (ary '{1024} num)).

  (* Classifier *)
  Context (fc_w : exp (ary '{1000} (ary '{1024} num)))
          (fc_b : exp (ary '{1000} num)).

  (* ---------------- Functional MobileNetV1 (opaque layer wrappers) --------
     Each layer value is a separate definition; after the body lemmas they
     are made [Opaque] so that the network-level proofs never inline a layer
     into the next one (quadratic/exponential goal blow-up otherwise). *)

  Definition mbv1_x1 := Conv4d_3x3_s2 s_b s_w input.
  Definition mbv1_x2 := BatchNorm4d mbv1_x1 s_g s_z eps.
  Definition mbv1_x3 := ReLU4d mbv1_x2.
  Definition mbv1_x4 := DWPWBlock_s1 mbv1_x3 d1_wdw d1_g1 d1_z1
                                    d1_wpw d1_bpw d1_g2 d1_z2 eps.
  Definition mbv1_x5 := DWPWBlock_s2 mbv1_x4 d2_wdw d2_g1 d2_z1
                                    d2_wpw d2_bpw d2_g2 d2_z2 eps.
  Definition mbv1_x6 := DWPWBlock_s1 mbv1_x5 d3_wdw d3_g1 d3_z1
                                    d3_wpw d3_bpw d3_g2 d3_z2 eps.
  Definition mbv1_x7 := DWPWBlock_s2 mbv1_x6 d4_wdw d4_g1 d4_z1
                                    d4_wpw d4_bpw d4_g2 d4_z2 eps.
  Definition mbv1_x8 := DWPWBlock_s1 mbv1_x7 d5_wdw d5_g1 d5_z1
                                    d5_wpw d5_bpw d5_g2 d5_z2 eps.
  Definition mbv1_x9 := DWPWBlock_s2 mbv1_x8 d6_wdw d6_g1 d6_z1
                                    d6_wpw d6_bpw d6_g2 d6_z2 eps.
  Definition mbv1_x10 := DWPWBlock_s1 mbv1_x9 d7_wdw d7_g1 d7_z1
                                     d7_wpw d7_bpw d7_g2 d7_z2 eps.
  Definition mbv1_x11 := DWPWBlock_s1 mbv1_x10 d8_wdw d8_g1 d8_z1
                                     d8_wpw d8_bpw d8_g2 d8_z2 eps.
  Definition mbv1_x12 := DWPWBlock_s1 mbv1_x11 d9_wdw d9_g1 d9_z1
                                     d9_wpw d9_bpw d9_g2 d9_z2 eps.
  Definition mbv1_x13 := DWPWBlock_s1 mbv1_x12 d10_wdw d10_g1 d10_z1
                                     d10_wpw d10_bpw d10_g2 d10_z2 eps.
  Definition mbv1_x14 := DWPWBlock_s1 mbv1_x13 d11_wdw d11_g1 d11_z1
                                     d11_wpw d11_bpw d11_g2 d11_z2 eps.
  Definition mbv1_x15 := DWPWBlock_s2 mbv1_x14 d12_wdw d12_g1 d12_z1
                                     d12_wpw d12_bpw d12_g2 d12_z2 eps.
  Definition mbv1_x16 := DWPWBlock_s1 mbv1_x15 d13_wdw d13_g1 d13_z1
                                     d13_wpw d13_bpw d13_g2 d13_z2 eps.
  Definition mbv1_x17 := GlobalAvgPool4d mbv1_x16.
  Definition mbv1_x18 := Softmax2d (Linear2d fc_w fc_b mbv1_x17).

  Lemma mbv1_x1_body : mbv1_x1 = Conv4d_3x3_s2 s_b s_w input.
  Proof. reflexivity. Qed.
  Lemma mbv1_x2_body : mbv1_x2 = BatchNorm4d mbv1_x1 s_g s_z eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x3_body : mbv1_x3 = ReLU4d mbv1_x2.
  Proof. reflexivity. Qed.
  Lemma mbv1_x4_body : mbv1_x4 = DWPWBlock_s1 mbv1_x3 d1_wdw d1_g1 d1_z1
                                    d1_wpw d1_bpw d1_g2 d1_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x5_body : mbv1_x5 = DWPWBlock_s2 mbv1_x4 d2_wdw d2_g1 d2_z1
                                    d2_wpw d2_bpw d2_g2 d2_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x6_body : mbv1_x6 = DWPWBlock_s1 mbv1_x5 d3_wdw d3_g1 d3_z1
                                    d3_wpw d3_bpw d3_g2 d3_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x7_body : mbv1_x7 = DWPWBlock_s2 mbv1_x6 d4_wdw d4_g1 d4_z1
                                    d4_wpw d4_bpw d4_g2 d4_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x8_body : mbv1_x8 = DWPWBlock_s1 mbv1_x7 d5_wdw d5_g1 d5_z1
                                    d5_wpw d5_bpw d5_g2 d5_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x9_body : mbv1_x9 = DWPWBlock_s2 mbv1_x8 d6_wdw d6_g1 d6_z1
                                    d6_wpw d6_bpw d6_g2 d6_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x10_body : mbv1_x10 = DWPWBlock_s1 mbv1_x9 d7_wdw d7_g1 d7_z1
                                     d7_wpw d7_bpw d7_g2 d7_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x11_body : mbv1_x11 = DWPWBlock_s1 mbv1_x10 d8_wdw d8_g1 d8_z1
                                     d8_wpw d8_bpw d8_g2 d8_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x12_body : mbv1_x12 = DWPWBlock_s1 mbv1_x11 d9_wdw d9_g1 d9_z1
                                     d9_wpw d9_bpw d9_g2 d9_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x13_body : mbv1_x13 = DWPWBlock_s1 mbv1_x12 d10_wdw d10_g1 d10_z1
                                     d10_wpw d10_bpw d10_g2 d10_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x14_body : mbv1_x14 = DWPWBlock_s1 mbv1_x13 d11_wdw d11_g1 d11_z1
                                     d11_wpw d11_bpw d11_g2 d11_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x15_body : mbv1_x15 = DWPWBlock_s2 mbv1_x14 d12_wdw d12_g1 d12_z1
                                     d12_wpw d12_bpw d12_g2 d12_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x16_body : mbv1_x16 = DWPWBlock_s1 mbv1_x15 d13_wdw d13_g1 d13_z1
                                     d13_wpw d13_bpw d13_g2 d13_z2 eps.
  Proof. reflexivity. Qed.
  Lemma mbv1_x17_body : mbv1_x17 = GlobalAvgPool4d mbv1_x16.
  Proof. reflexivity. Qed.
  Lemma mbv1_x18_body : mbv1_x18 = Softmax2d (Linear2d fc_w fc_b mbv1_x17).
  Proof. reflexivity. Qed.

  Opaque mbv1_x1 mbv1_x2 mbv1_x3 mbv1_x4 mbv1_x5 mbv1_x6 mbv1_x7 mbv1_x8
         mbv1_x9 mbv1_x10 mbv1_x11 mbv1_x12 mbv1_x13 mbv1_x14 mbv1_x15
         mbv1_x16 mbv1_x17 mbv1_x18.

  Definition MobileNetV1 : exp (ary '{1} (ary '{1000} num)) := mbv1_x18.

  (* ---------------- Imperative MobileNetV1 (buffer-layered) -------------- *)

  Definition mobilenetv1_comm (output : acc (ary '{1} (ary '{1000} num)))
    : comm :=
new (fun t1 => seq (Conv4d_3x3_s2_comm s_b s_w input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 s_g s_z eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => ReLU4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 =>
        dwpwblock_s1_comm e3 d1_wdw d1_g1 d1_z1
                               d1_wpw d1_bpw d1_g2 d1_z2 eps t4))
(new (fun t5 => seq (bind_read t4 (fun e4 =>
        dwpwblock_s2_comm e4 d2_wdw d2_g1 d2_z1
                               d2_wpw d2_bpw d2_g2 d2_z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 =>
        dwpwblock_s1_comm e5 d3_wdw d3_g1 d3_z1
                               d3_wpw d3_bpw d3_g2 d3_z2 eps t6))
(new (fun t7 => seq (bind_read t6 (fun e6 =>
        dwpwblock_s2_comm e6 d4_wdw d4_g1 d4_z1
                               d4_wpw d4_bpw d4_g2 d4_z2 eps t7))
(new (fun t8 => seq (bind_read t7 (fun e7 =>
        dwpwblock_s1_comm e7 d5_wdw d5_g1 d5_z1
                               d5_wpw d5_bpw d5_g2 d5_z2 eps t8))
(new (fun t9 => seq (bind_read t8 (fun e8 =>
        dwpwblock_s2_comm e8 d6_wdw d6_g1 d6_z1
                               d6_wpw d6_bpw d6_g2 d6_z2 eps t9))
(new (fun t10 => seq (bind_read t9 (fun e9 =>
        dwpwblock_s1_comm e9 d7_wdw d7_g1 d7_z1
                               d7_wpw d7_bpw d7_g2 d7_z2 eps t10))
(new (fun t11 => seq (bind_read t10 (fun e10 =>
        dwpwblock_s1_comm e10 d8_wdw d8_g1 d8_z1
                               d8_wpw d8_bpw d8_g2 d8_z2 eps t11))
(new (fun t12 => seq (bind_read t11 (fun e11 =>
        dwpwblock_s1_comm e11 d9_wdw d9_g1 d9_z1
                               d9_wpw d9_bpw d9_g2 d9_z2 eps t12))
(new (fun t13 => seq (bind_read t12 (fun e12 =>
        dwpwblock_s1_comm e12 d10_wdw d10_g1 d10_z1
                               d10_wpw d10_bpw d10_g2 d10_z2 eps t13))
(new (fun t14 => seq (bind_read t13 (fun e13 =>
        dwpwblock_s1_comm e13 d11_wdw d11_g1 d11_z1
                               d11_wpw d11_bpw d11_g2 d11_z2 eps t14))
(new (fun t15 => seq (bind_read t14 (fun e14 =>
        dwpwblock_s2_comm e14 d12_wdw d12_g1 d12_z1
                               d12_wpw d12_bpw d12_g2 d12_z2 eps t15))
(new (fun t16 => seq (bind_read t15 (fun e15 =>
        dwpwblock_s1_comm e15 d13_wdw d13_g1 d13_z1
                               d13_wpw d13_bpw d13_g2 d13_z2 eps t16))
(new (fun t17 => seq (bind_read t16 (fun e16 => GlobalAvgPool4d_comm e16 t17))
     (bind_read t17 (fun e17 => Softmax2d_comm (Linear2d fc_w fc_b e17) output))
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

  Definition mobilenetv1_comm_direct (output : acc (ary '{1} (ary '{1000} num)))
    : comm :=
    seq (A(acc' (Var "l1"), mbv1_x1))
    (seq (A(acc' (Var "l2"), mbv1_x2))
    (seq (A(acc' (Var "l3"), mbv1_x3))
    (seq (dwpwblock_s1_direct mbv1_x3 d1_wdw d1_g1 d1_z1
                                   d1_wpw d1_bpw d1_g2 d1_z2 eps (acc' (Var "l4")))
    (seq (dwpwblock_s2_direct mbv1_x4 d2_wdw d2_g1 d2_z1
                                   d2_wpw d2_bpw d2_g2 d2_z2 eps (acc' (Var "l5")))
    (seq (dwpwblock_s1_direct mbv1_x5 d3_wdw d3_g1 d3_z1
                                   d3_wpw d3_bpw d3_g2 d3_z2 eps (acc' (Var "l6")))
    (seq (dwpwblock_s2_direct mbv1_x6 d4_wdw d4_g1 d4_z1
                                   d4_wpw d4_bpw d4_g2 d4_z2 eps (acc' (Var "l7")))
    (seq (dwpwblock_s1_direct mbv1_x7 d5_wdw d5_g1 d5_z1
                                   d5_wpw d5_bpw d5_g2 d5_z2 eps (acc' (Var "l8")))
    (seq (dwpwblock_s2_direct mbv1_x8 d6_wdw d6_g1 d6_z1
                                   d6_wpw d6_bpw d6_g2 d6_z2 eps (acc' (Var "l9")))
    (seq (dwpwblock_s1_direct mbv1_x9 d7_wdw d7_g1 d7_z1
                                   d7_wpw d7_bpw d7_g2 d7_z2 eps (acc' (Var "l10")))
    (seq (dwpwblock_s1_direct mbv1_x10 d8_wdw d8_g1 d8_z1
                                   d8_wpw d8_bpw d8_g2 d8_z2 eps (acc' (Var "l11")))
    (seq (dwpwblock_s1_direct mbv1_x11 d9_wdw d9_g1 d9_z1
                                   d9_wpw d9_bpw d9_g2 d9_z2 eps (acc' (Var "l12")))
    (seq (dwpwblock_s1_direct mbv1_x12 d10_wdw d10_g1 d10_z1
                                   d10_wpw d10_bpw d10_g2 d10_z2 eps (acc' (Var "l13")))
    (seq (dwpwblock_s1_direct mbv1_x13 d11_wdw d11_g1 d11_z1
                                   d11_wpw d11_bpw d11_g2 d11_z2 eps (acc' (Var "l14")))
    (seq (dwpwblock_s2_direct mbv1_x14 d12_wdw d12_g1 d12_z1
                                   d12_wpw d12_bpw d12_g2 d12_z2 eps (acc' (Var "l15")))
    (seq (dwpwblock_s1_direct mbv1_x15 d13_wdw d13_g1 d13_z1
                                   d13_wpw d13_bpw d13_g2 d13_z2 eps (acc' (Var "l16")))
    (seq (A(acc' (Var "l17"), mbv1_x17))
    ((A(output, mbv1_x18))))))))))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition r1_acc : acc (ary '{1} (ary '{32} (ary '{half m} (ary '{half m} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{1} (ary '{32} (ary '{half m} (ary '{half m} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{1} (ary '{32} (ary '{half m} (ary '{half m} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{1} (ary '{64} (ary '{half m} (ary '{half m} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{1} (ary '{128} (ary '{half (half m)} (ary '{half (half m)} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{1} (ary '{128} (ary '{half (half m)} (ary '{half (half m)} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{1} (ary '{256} (ary '{half (half (half m))} (ary '{half (half (half m))} num))))
    := acc' (Var "l7").
  Definition r8_acc : acc (ary '{1} (ary '{256} (ary '{half (half (half m))} (ary '{half (half (half m))} num))))
    := acc' (Var "l8").
  Definition r9_acc : acc (ary '{1} (ary '{512} (ary '{half (half (half (half m)))} (ary '{half (half (half (half m)))} num))))
    := acc' (Var "l9").
  Definition r10_acc : acc (ary '{1} (ary '{512} (ary '{half (half (half (half m)))} (ary '{half (half (half (half m)))} num))))
    := acc' (Var "l10").
  Definition r11_acc : acc (ary '{1} (ary '{512} (ary '{half (half (half (half m)))} (ary '{half (half (half (half m)))} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{1} (ary '{512} (ary '{half (half (half (half m)))} (ary '{half (half (half (half m)))} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{1} (ary '{512} (ary '{half (half (half (half m)))} (ary '{half (half (half (half m)))} num))))
    := acc' (Var "l13").
  Definition r14_acc : acc (ary '{1} (ary '{512} (ary '{half (half (half (half m)))} (ary '{half (half (half (half m)))} num))))
    := acc' (Var "l14").
  Definition r15_acc : acc (ary '{1} (ary '{1024} (ary '{half (half (half (half (half m))))} (ary '{half (half (half (half (half m))))} num))))
    := acc' (Var "l15").
  Definition r16_acc : acc (ary '{1} (ary '{1024} (ary '{half (half (half (half (half m))))} (ary '{half (half (half (half (half m))))} num))))
    := acc' (Var "l16").
  Definition r17_acc : acc (ary '{1} (ary '{1024} num))
    := acc' (Var "l17").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries bt1..bt5 are shared between blocks and are required to be
     fresh at every type. *)
  Definition mobilenetv1_fresh
    (output : acc (ary '{1} (ary '{1000} num))) (rho : env) : Prop :=
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
    (forall d : data, StructUndefined (acc' (Var "bt1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt5") : acc d) rho) /\
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
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt5") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  (* The proof keeps the goal small throughout: layer values are folded to
     their opaque [mbv1_xK] constants as soon as they are assigned, and block
     direct forms are never unfolded at the network level
     ([dwpwblock_*_direct_read] advances past them). *)
  Lemma mobilenetv1_comm_eq_direct :
    forall (output : acc (ary '{1} (ary '{1000} num))),
    mobilenetv1_comm output = mobilenetv1_comm_direct output.
  Proof.
    intros.
    unfold mobilenetv1_comm, mobilenetv1_comm_direct, new.
    cbv beta.
    rewrite <- A_Conv4d_3x3_s2.
    rewrite <- mbv1_x1_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_BatchNorm4d.
    rewrite bind_read_replace_seq.
    rewrite <- mbv1_x2_body.
    rewrite <- A_ReLU4d.
    rewrite bind_read_replace_seq.
    rewrite <- mbv1_x3_body.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s2_comm_eq_direct.
    rewrite <- mbv1_x4_body.
    rewrite dwpwblock_s2_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x5_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s2_comm_eq_direct.
    rewrite <- mbv1_x6_body.
    rewrite dwpwblock_s2_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x7_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s2_comm_eq_direct.
    rewrite <- mbv1_x8_body.
    rewrite dwpwblock_s2_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x9_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x10_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x11_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x12_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x13_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite dwpwblock_s2_comm_eq_direct.
    rewrite <- mbv1_x14_body.
    rewrite dwpwblock_s2_direct_read.
    rewrite dwpwblock_s1_comm_eq_direct.
    rewrite <- mbv1_x15_body.
    rewrite dwpwblock_s1_direct_read.
    rewrite <- mbv1_x16_body.
    rewrite <- A_GlobalAvgPool4d.
    rewrite <- mbv1_x17_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    rewrite <- mbv1_x18_body.
    reflexivity.
  Qed.

  Lemma A_MobileNetV1_direct :
    forall (output : acc (ary '{1} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    mobilenetv1_fresh output rho ->
    mobilenetv1_comm_direct output rho p = A(output, MobileNetV1) rho p.
  Proof.
    intros.
    unfold mobilenetv1_comm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold MobileNetV1. reflexivity.
  Qed.

  Theorem A_MobileNetV1 :
    forall (output : acc (ary '{1} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    mobilenetv1_fresh output rho ->
    mobilenetv1_comm output rho p = A(output, MobileNetV1) rho p.
  Proof.
    intros. rewrite mobilenetv1_comm_eq_direct.
    apply A_MobileNetV1_direct; assumption.
  Qed.

End MobileNetV1.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_DWConv4d_3x3_s1.
Print Assumptions A_DWConv4d_3x3_s2.
Print Assumptions A_DWPWBlock_s1.
Print Assumptions A_DWPWBlock_s2.
Print Assumptions A_MobileNetV1.
