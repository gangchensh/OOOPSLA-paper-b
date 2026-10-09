(* DPIA-style end-to-end Leibniz correctness proof for EfficientNet-B0
   (route A), batch = 1, spatial size symbolic (m).

   Structure (classic EfficientNet-B0):
     stem conv(3x3,p1,s2) - bn - swish                       (channel -> 32)
     16 MBConv blocks (expand ratio 6 except block 1, SE on the expanded
       channels, SE hidden = in/4, swish after every bn except the
       post-projection bn; residual add when s1 and in-ch = out-ch):
       b1  MBConv1  k3 s1  32  -> 16   (no expand, no skip)
       b2  MBConv6  k3 s2  16  -> 24   (e=96)
       b3  MBConv6  k3 s1  24  -> 24   (e=144, skip)
       b4  MBConv6  k5 s2  24  -> 40   (e=144)
       b5  MBConv6  k5 s1  40  -> 40   (e=240, skip)
       b6  MBConv6  k3 s2  40  -> 80   (e=240)
       b7  MBConv6  k3 s1  80  -> 80   (e=480, skip)
       b8  MBConv6  k3 s1  80  -> 80   (e=480, skip)
       b9  MBConv6  k5 s1  80  -> 112  (e=480, no skip)
       b10 MBConv6  k5 s1  112 -> 112  (e=672, skip)
       b11 MBConv6  k5 s1  112 -> 112  (e=672, skip)
       b12 MBConv6  k5 s2  112 -> 192  (e=672)
       b13 MBConv6  k5 s1  192 -> 192  (e=1152, skip)
       b14 MBConv6  k5 s1  192 -> 192  (e=1152, skip)
       b15 MBConv6  k5 s1  192 -> 192  (e=1152, skip)
       b16 MBConv6  k3 s1  192 -> 320  (e=1152, no skip)
     head conv(1x1) 320 -> 1280 - bn - swish - GlobalAvgPool - fc(1000)
       - softmax

   Swish4d = mul x (sigmoid x), following the pointwise template of
   Ionia.Ops_Elementwise.  The k=5 depthwise convolutions use canonical-size
   variants DWConv4d_5x5_s1 / DWConv4d_5x5_s2 (same-size resp. [half]),
   proved exactly like A_DWConv4d; the k=3 variants come from
   MobileNetV1_DPIA.  The 1x1 convolutions reuse [Conv4d_1x1_s1] of
   ResNet50_DPIA.v; the stem reuses [Conv4d_3x3_s2] of ResNet18_DPIA.v.

   The SE sub-block (GAP - fc - fc - sigmoid - ChannelScale, batch = 1 so
   the 1-channel scale vector is obtained by indexing the pooled tensor at
   batch index [ltS 0]) is itself a proved block ([seblock_comm_eq_direct],
   [A_SEBlock]) nested inside each MBConv block, mirroring the way blocks
   are nested inside the network in MobileNetV1_DPIA.v.

   As in ResNet50_DPIA.v / MobileNetV1_DPIA.v, each block combinator is
   proved equal to a buffer-free "direct" form; the network-level proof
   rewrites the comm form to the direct form, and the direct form observed
   at an output path equals the functional network. *)

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
Require Import Ionia.MobileNetV1_DPIA.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Swish4d : out = x * sigmoid(x) = x / (1 + exp(-x))                          *)
(* -------------------------------------------------------------------------- *)

Definition Swish4d {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      mul (idx (idx (idx (idx input b) c) i) j)
          (div one (add one (pExp (negate
            (idx (idx (idx (idx input b) c) i) j))))))))).

Definition Swish4d_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        mul (idx (idx (idx (idx input b) c) i) j)
            (div one (add one (pExp (negate
              (idx (idx (idx (idx input b) c) i) j))))))))).

Lemma A_Swish4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, Swish4d input) = Swish4d_comm input output.
Proof.
  intros. unfold Swish4d, Swish4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* DWConv4d_5x5_s1 : depthwise 5x5 convolution, padding 2, stride 1, same-size     *)
(* -------------------------------------------------------------------------- *)

Definition DWConv4d_5x5_s1 {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{5} (ary '{5} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun ch : fin c =>
    mkvSeq (fun i0 : fin (m1) => mkvSeq (fun j0 : fin (m2) =>
      sum (mkvSeq (fun i1 : fin 5 =>
        sum (mkvSeq (fun j1 : fin 5 =>
          mul (idx (idx (idx w ch) i1) j1)
              (pad_idx2d 2 (idx (idx input b) ch)
                         (fin2nat i0 + fin2nat i1)
                         (fin2nat j0 + fin2nat j1)))))))))).

Definition DWConv4d_5x5_s1_comm {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{5} (ary '{5} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun ch oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun i1 : fin 5 =>
             sum (mkvSeq (fun j1 : fin 5 =>
               mul (idx (idx (idx w ch) i1) j1)
                   (pad_idx2d 2 (idx (idx input b) ch)
                              (fin2nat i0 + fin2nat i1)
                              (fin2nat j0 + fin2nat j1))))))
           (fun r : exp num => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_DWConv4d_5x5_s1 : forall (batch c m1 m2 : nat)
  (w : exp (ary '{c} (ary '{5} (ary '{5} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  A(output, DWConv4d_5x5_s1 w input) = DWConv4d_5x5_s1_comm w input output.
Proof.
  intros. unfold DWConv4d_5x5_s1, DWConv4d_5x5_s1_comm.
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
(* DWConv4d_5x5_s2 : depthwise 5x5 convolution, padding 2, stride 2, [half]     *)
(* -------------------------------------------------------------------------- *)

Definition DWConv4d_5x5_s2 {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{5} (ary '{5} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{c} (ary '{half m1} (ary '{half m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun ch : fin c =>
    mkvSeq (fun i0 : fin (half m1) => mkvSeq (fun j0 : fin (half m2) =>
      sum (mkvSeq (fun i1 : fin 5 =>
        sum (mkvSeq (fun j1 : fin 5 =>
          mul (idx (idx (idx w ch) i1) j1)
              (pad_idx2d 2 (idx (idx input b) ch)
                         (fin2nat i0 * 2 + fin2nat i1)
                         (fin2nat j0 * 2 + fin2nat j1)))))))))).

Definition DWConv4d_5x5_s2_comm {batch c m1 m2 : nat}
  (w : exp (ary '{c} (ary '{5} (ary '{5} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun ch oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun i1 : fin 5 =>
             sum (mkvSeq (fun j1 : fin 5 =>
               mul (idx (idx (idx w ch) i1) j1)
                   (pad_idx2d 2 (idx (idx input b) ch)
                              (fin2nat i0 * 2 + fin2nat i1)
                              (fin2nat j0 * 2 + fin2nat j1))))))
           (fun r : exp num => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_DWConv4d_5x5_s2 : forall (batch c m1 m2 : nat)
  (w : exp (ary '{c} (ary '{5} (ary '{5} num))))
  (input : exp (ary '{batch} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{c} (ary '{half m1} (ary '{half m2} num))))),
  A(output, DWConv4d_5x5_s2 w input) = DWConv4d_5x5_s2_comm w input output.
Proof.
  intros. unfold DWConv4d_5x5_s2, DWConv4d_5x5_s2_comm.
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
(* SEBlock (squeeze-excitation, batch = 1):                                    *)
(*   GAP - Linear(c->se) - Linear(se->c) - sigmoid - ChannelScale              *)
(* The per-channel scale vector is the pooled 1 x c tensor indexed at the      *)
(* (single) batch index [ltS 0].                                               *)
(* -------------------------------------------------------------------------- *)

Definition SEBlock {c se m1 m2 : nat}
  (sw1 : exp (ary '{se} (ary '{c} num))) (sb1 : exp (ary '{se} num))
  (sw2 : exp (ary '{c} (ary '{se} num))) (sb2 : exp (ary '{c} num))
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  let g := GlobalAvgPool4d input in
  let f1 := Linear2d sw1 sb1 g in
  let f2 := Linear2d sw2 sb2 f1 in
  let sg := Sigmoid2d f2 in
  ChannelScale4d (idx sg (ltS 0)) input.

Definition seblock_comm {c se m1 m2 : nat}
  (sw1 : exp (ary '{se} (ary '{c} num))) (sb1 : exp (ary '{se} num))
  (sw2 : exp (ary '{c} (ary '{se} num))) (sb2 : exp (ary '{c} num))
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (GlobalAvgPool4d_comm input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => Linear2d_comm sw1 sb1 e1 t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Linear2d_comm sw2 sb2 e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => Sigmoid2d_comm e3 t4))
     (bind_read t4 (fun e4 => ChannelScale4d_comm (idx e4 (ltS 0)) input output))
) (acc' (Var "sg4")))
) (acc' (Var "sg3")))
) (acc' (Var "sg2")))
) (acc' (Var "sg1")).

(* Direct (DPIA-normal) form of the SE sub-block. *)
Definition seblock_direct {c se m1 m2 : nat}
  (sw1 : exp (ary '{se} (ary '{c} num))) (sb1 : exp (ary '{se} num))
  (sw2 : exp (ary '{c} (ary '{se} num))) (sb2 : exp (ary '{c} num))
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let g := GlobalAvgPool4d input in
  let f1 := Linear2d sw1 sb1 g in
  let f2 := Linear2d sw2 sb2 f1 in
  let sg := Sigmoid2d f2 in
  seq (seq (seq (seq (A(acc' (Var "sg1"), g))
                     (A(acc' (Var "sg2"), f1)))
                     (A(acc' (Var "sg3"), f2)))
                     (A(acc' (Var "sg4"), sg)))
       (A(output, SEBlock sw1 sb1 sw2 sb2 input)).

Lemma seblock_comm_eq_direct : forall (c se m1 m2 : nat)
  (sw1 : exp (ary '{se} (ary '{c} num))) (sb1 : exp (ary '{se} num))
  (sw2 : exp (ary '{c} (ary '{se} num))) (sb2 : exp (ary '{c} num))
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  seblock_comm sw1 sb1 sw2 sb2 input output =
  seblock_direct sw1 sb1 sw2 sb2 input output.
Proof.
  intros.
  unfold seblock_comm, seblock_direct, new.
  cbv zeta beta.
  rewrite <- A_GlobalAvgPool4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Linear2d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Linear2d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Sigmoid2d.
  rewrite bind_read_replace.
  rewrite <- A_ChannelScale4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness of the SE sub-block. *)
Lemma A_SEBlock : forall (c se m1 m2 : nat)
  (sw1 : exp (ary '{se} (ary '{c} num))) (sb1 : exp (ary '{se} num))
  (sw2 : exp (ary '{c} (ary '{se} num))) (sb2 : exp (ary '{c} num))
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  seblock_comm sw1 sb1 sw2 sb2 input output rho p =
  A(output, SEBlock sw1 sb1 sw2 sb2 input) rho p.
Proof.
  intros. rewrite seblock_comm_eq_direct.
  unfold seblock_direct, SEBlock, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the SE output buffer after the (folded) direct form yields the
   functional SEBlock value; used when the SE sub-block is nested inside an
   MBConv block and followed by further commands. *)
Lemma seblock_direct_read : forall (c se m1 m2 : nat)
  (sw1 : exp (ary '{se} (ary '{c} num))) (sb1 : exp (ary '{se} num))
  (sw2 : exp (ary '{c} (ary '{se} num))) (sb2 : exp (ary '{c} num))
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (q : path)
  (k : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (seblock_direct sw1 sb1 sw2 sb2 input (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (seblock_direct sw1 sb1 sw2 sb2 input (acc' q))
      (seq (k (SEBlock sw1 sb1 sw2 sb2 input)) c0).
Proof.
  intros. unfold seblock_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConv1 : MBConv1 block (no expand): DWConv 3x3 s1 - bn - swish
   - SE - 1x1 project - bn (no residual) *)
(* -------------------------------------------------------------------------- *)

Definition MBConv1 {inch outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (sw1 : exp (ary '{se} (ary '{inch} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{inch} (ary '{se} num)))
    (sb2 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  let d1 := DWConv4d_3x3_s1 wdw input in
  let n1 := BatchNorm4d d1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r1 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n2 := BatchNorm4d p1 g2 z2 eps in
  n2.

(* Imperative block: temporaries bt1..bt5, output written in place. *)
Definition mbconv1_comm {inch outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (sw1 : exp (ary '{se} (ary '{inch} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{inch} (ary '{se} num)))
    (sb2 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (DWConv4d_3x3_s1_comm wdw input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => seblock_comm sw1 sb1 sw2 sb2 e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => Conv4d_1x1_s1_comm bpw wpw e4 t5))
     (bind_read t5 (fun e5 => BatchNorm4d_comm e5 g2 z2 eps output))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconv1_direct {inch outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (sw1 : exp (ary '{se} (ary '{inch} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{inch} (ary '{se} num)))
    (sb2 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let d1 := DWConv4d_3x3_s1 wdw input in
  let n1 := BatchNorm4d d1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r1 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n2 := BatchNorm4d p1 g2 z2 eps in
  seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), d1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((seblock_direct sw1 sb1 sw2 sb2 r1 (acc' (Var "bt4")))))
         ((A(acc' (Var "bt5"), p1))))
         ((A(output, MBConv1 input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps))).

Lemma mbconv1_comm_eq_direct : forall (inch outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (sw1 : exp (ary '{se} (ary '{inch} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{inch} (ary '{se} num)))
    (sb2 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  mbconv1_comm input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps output =
  mbconv1_direct input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps output.
Proof.
  intros.
  unfold mbconv1_comm, mbconv1_direct, new.
  cbv zeta beta.
  rewrite <- A_DWConv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace.
  rewrite <- A_BatchNorm4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConv1]. *)
Lemma A_MBConv1 : forall (inch outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (sw1 : exp (ary '{se} (ary '{inch} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{inch} (ary '{se} num)))
    (sb2 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconv1_comm input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps output rho p =
  A(output, MBConv1 input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps) rho p.
Proof.
  intros. rewrite mbconv1_comm_eq_direct.
  unfold mbconv1_direct, MBConv1, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconv1_direct_read : forall (inch outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wdw : exp (ary '{inch} (ary '{3} (ary '{3} num))))
    (g1 : exp (ary '{inch} num))
    (z1 : exp (ary '{inch} num))
  (sw1 : exp (ary '{se} (ary '{inch} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{inch} (ary '{se} num)))
    (sb2 : exp (ary '{inch} num))
  (wpw : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g2 : exp (ary '{outch} num))
    (z2 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (mbconv1_direct input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconv1_direct input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps (acc' q))
      (seq (k (MBConv1 input wdw g1 z1 sw1 sb1 sw2 sb2 wpw bpw g2 z2 eps)) c0).
Proof.
  intros. unfold mbconv1_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConvE3s2 : MBConv block: 1x1 expand - bn - swish - DWConv 3x3 s2
   - bn - swish - SE - 1x1 project - bn *)
(* -------------------------------------------------------------------------- *)

Definition MBConvE3s2 {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_3x3_s2 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  n3.

(* Imperative block: temporaries bt1..bt8, output written in place. *)
Definition mbconve3s2_comm {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bex wex input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => DWConv4d_3x3_s2_comm wdw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Swish4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => seblock_comm sw1 sb1 sw2 sb2 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => Conv4d_1x1_s1_comm bpw wpw e7 t8))
     (bind_read t8 (fun e8 => BatchNorm4d_comm e8 g3 z3 eps output))) (acc' (Var "bt8")))) (acc' (Var "bt7")))) (acc' (Var "bt6")))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconve3s2_direct {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_3x3_s2 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), c1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((A(acc' (Var "bt4"), d1))))
         ((A(acc' (Var "bt5"), n2))))
         ((A(acc' (Var "bt6"), r2))))
         ((seblock_direct sw1 sb1 sw2 sb2 r2 (acc' (Var "bt7")))))
         ((A(acc' (Var "bt8"), p1))))
         ((A(output, MBConvE3s2 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps))).

Lemma mbconve3s2_comm_eq_direct : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  mbconve3s2_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output =
  mbconve3s2_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output.
Proof.
  intros.
  unfold mbconve3s2_comm, mbconve3s2_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_DWConv4d_3x3_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace.
  rewrite <- A_BatchNorm4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConvE3s2]. *)
Lemma A_MBConvE3s2 : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconve3s2_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output rho p =
  A(output, MBConvE3s2 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps) rho p.
Proof.
  intros. rewrite mbconve3s2_comm_eq_direct.
  unfold mbconve3s2_direct, MBConvE3s2, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconve3s2_direct_read : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) -> comm) (c0 : comm),
  seq (mbconve3s2_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconve3s2_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (k (MBConvE3s2 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps)) c0).
Proof.
  intros. unfold mbconve3s2_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConvE5s2 : MBConv block: 1x1 expand - bn - swish - DWConv 5x5 s2
   - bn - swish - SE - 1x1 project - bn *)
(* -------------------------------------------------------------------------- *)

Definition MBConvE5s2 {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_5x5_s2 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  n3.

(* Imperative block: temporaries bt1..bt8, output written in place. *)
Definition mbconve5s2_comm {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bex wex input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => DWConv4d_5x5_s2_comm wdw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Swish4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => seblock_comm sw1 sb1 sw2 sb2 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => Conv4d_1x1_s1_comm bpw wpw e7 t8))
     (bind_read t8 (fun e8 => BatchNorm4d_comm e8 g3 z3 eps output))) (acc' (Var "bt8")))) (acc' (Var "bt7")))) (acc' (Var "bt6")))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconve5s2_direct {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_5x5_s2 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), c1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((A(acc' (Var "bt4"), d1))))
         ((A(acc' (Var "bt5"), n2))))
         ((A(acc' (Var "bt6"), r2))))
         ((seblock_direct sw1 sb1 sw2 sb2 r2 (acc' (Var "bt7")))))
         ((A(acc' (Var "bt8"), p1))))
         ((A(output, MBConvE5s2 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps))).

Lemma mbconve5s2_comm_eq_direct : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  mbconve5s2_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output =
  mbconve5s2_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output.
Proof.
  intros.
  unfold mbconve5s2_comm, mbconve5s2_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_DWConv4d_5x5_s2.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace.
  rewrite <- A_BatchNorm4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConvE5s2]. *)
Lemma A_MBConvE5s2 : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconve5s2_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output rho p =
  A(output, MBConvE5s2 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps) rho p.
Proof.
  intros. rewrite mbconve5s2_comm_eq_direct.
  unfold mbconve5s2_direct, MBConvE5s2, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconve5s2_direct_read : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) -> comm) (c0 : comm),
  seq (mbconve5s2_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconve5s2_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (k (MBConvE5s2 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps)) c0).
Proof.
  intros. unfold mbconve5s2_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConvE3s1 : MBConv block: 1x1 expand - bn - swish - DWConv 3x3 s1
   - bn - swish - SE - 1x1 project - bn *)
(* -------------------------------------------------------------------------- *)

Definition MBConvE3s1 {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_3x3_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  n3.

(* Imperative block: temporaries bt1..bt8, output written in place. *)
Definition mbconve3s1_comm {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bex wex input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => DWConv4d_3x3_s1_comm wdw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Swish4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => seblock_comm sw1 sb1 sw2 sb2 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => Conv4d_1x1_s1_comm bpw wpw e7 t8))
     (bind_read t8 (fun e8 => BatchNorm4d_comm e8 g3 z3 eps output))) (acc' (Var "bt8")))) (acc' (Var "bt7")))) (acc' (Var "bt6")))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconve3s1_direct {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_3x3_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), c1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((A(acc' (Var "bt4"), d1))))
         ((A(acc' (Var "bt5"), n2))))
         ((A(acc' (Var "bt6"), r2))))
         ((seblock_direct sw1 sb1 sw2 sb2 r2 (acc' (Var "bt7")))))
         ((A(acc' (Var "bt8"), p1))))
         ((A(output, MBConvE3s1 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps))).

Lemma mbconve3s1_comm_eq_direct : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  mbconve3s1_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output =
  mbconve3s1_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output.
Proof.
  intros.
  unfold mbconve3s1_comm, mbconve3s1_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_DWConv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace.
  rewrite <- A_BatchNorm4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConvE3s1]. *)
Lemma A_MBConvE3s1 : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconve3s1_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output rho p =
  A(output, MBConvE3s1 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps) rho p.
Proof.
  intros. rewrite mbconve3s1_comm_eq_direct.
  unfold mbconve3s1_direct, MBConvE3s1, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconve3s1_direct_read : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (mbconve3s1_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconve3s1_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (k (MBConvE3s1 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps)) c0).
Proof.
  intros. unfold mbconve3s1_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConvE5s1 : MBConv block: 1x1 expand - bn - swish - DWConv 5x5 s1
   - bn - swish - SE - 1x1 project - bn *)
(* -------------------------------------------------------------------------- *)

Definition MBConvE5s1 {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_5x5_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  n3.

(* Imperative block: temporaries bt1..bt8, output written in place. *)
Definition mbconve5s1_comm {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bex wex input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => DWConv4d_5x5_s1_comm wdw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Swish4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => seblock_comm sw1 sb1 sw2 sb2 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => Conv4d_1x1_s1_comm bpw wpw e7 t8))
     (bind_read t8 (fun e8 => BatchNorm4d_comm e8 g3 z3 eps output))) (acc' (Var "bt8")))) (acc' (Var "bt7")))) (acc' (Var "bt6")))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconve5s1_direct {inch e outch se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_5x5_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), c1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((A(acc' (Var "bt4"), d1))))
         ((A(acc' (Var "bt5"), n2))))
         ((A(acc' (Var "bt6"), r2))))
         ((seblock_direct sw1 sb1 sw2 sb2 r2 (acc' (Var "bt7")))))
         ((A(acc' (Var "bt8"), p1))))
         ((A(output, MBConvE5s1 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps))).

Lemma mbconve5s1_comm_eq_direct : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  mbconve5s1_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output =
  mbconve5s1_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output.
Proof.
  intros.
  unfold mbconve5s1_comm, mbconve5s1_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_DWConv4d_5x5_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace.
  rewrite <- A_BatchNorm4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConvE5s1]. *)
Lemma A_MBConvE5s1 : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconve5s1_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output rho p =
  A(output, MBConvE5s1 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps) rho p.
Proof.
  intros. rewrite mbconve5s1_comm_eq_direct.
  unfold mbconve5s1_direct, MBConvE5s1, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconve5s1_direct_read : forall (inch e outch se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{inch} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{outch} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{outch} num))
    (g3 : exp (ary '{outch} num))
    (z3 : exp (ary '{outch} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{outch} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (mbconve5s1_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconve5s1_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (k (MBConvE5s1 input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps)) c0).
Proof.
  intros. unfold mbconve5s1_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConvE3s1R : MBConv block: 1x1 expand - bn - swish - DWConv 3x3 s1
   - bn - swish - SE - 1x1 project - bn - residual add *)
(* -------------------------------------------------------------------------- *)

Definition MBConvE3s1R {c e se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_3x3_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  let a1 := Add4d n3 input in
  a1.

(* Imperative block: temporaries bt1..bt9, output written in place. *)
Definition mbconve3s1r_comm {c e se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bex wex input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => DWConv4d_3x3_s1_comm wdw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Swish4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => seblock_comm sw1 sb1 sw2 sb2 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => Conv4d_1x1_s1_comm bpw wpw e7 t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => BatchNorm4d_comm e8 g3 z3 eps t9))
     (bind_read t9 (fun e9 => Add4d_comm e9 input output))) (acc' (Var "bt9")))) (acc' (Var "bt8")))) (acc' (Var "bt7")))) (acc' (Var "bt6")))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconve3s1r_direct {c e se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_3x3_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  let a1 := Add4d n3 input in
  seq (seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), c1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((A(acc' (Var "bt4"), d1))))
         ((A(acc' (Var "bt5"), n2))))
         ((A(acc' (Var "bt6"), r2))))
         ((seblock_direct sw1 sb1 sw2 sb2 r2 (acc' (Var "bt7")))))
         ((A(acc' (Var "bt8"), p1))))
         ((A(acc' (Var "bt9"), n3))))
         ((A(output, MBConvE3s1R input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps))).

Lemma mbconve3s1r_comm_eq_direct : forall (c e se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  mbconve3s1r_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output =
  mbconve3s1r_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output.
Proof.
  intros.
  unfold mbconve3s1r_comm, mbconve3s1r_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_DWConv4d_3x3_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_Add4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConvE3s1R]. *)
Lemma A_MBConvE3s1R : forall (c e se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconve3s1r_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output rho p =
  A(output, MBConvE3s1R input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps) rho p.
Proof.
  intros. rewrite mbconve3s1r_comm_eq_direct.
  unfold mbconve3s1r_direct, MBConvE3s1R, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconve3s1r_direct_read : forall (c e se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{3} (ary '{3} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (mbconve3s1r_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconve3s1r_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (k (MBConvE3s1R input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps)) c0).
Proof.
  intros. unfold mbconve3s1r_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* MBConvE5s1R : MBConv block: 1x1 expand - bn - swish - DWConv 5x5 s1
   - bn - swish - SE - 1x1 project - bn - residual add *)
(* -------------------------------------------------------------------------- *)

Definition MBConvE5s1R {c e se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))) :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_5x5_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  let a1 := Add4d n3 input in
  a1.

(* Imperative block: temporaries bt1..bt9, output written in place. *)
Definition mbconve5s1r_comm {c e se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
new (fun t1 => seq (Conv4d_1x1_s1_comm bex wex input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 g1 z1 eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => DWConv4d_5x5_s1_comm wdw e3 t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => BatchNorm4d_comm e4 g2 z2 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => Swish4d_comm e5 t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => seblock_comm sw1 sb1 sw2 sb2 e6 t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => Conv4d_1x1_s1_comm bpw wpw e7 t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => BatchNorm4d_comm e8 g3 z3 eps t9))
     (bind_read t9 (fun e9 => Add4d_comm e9 input output))) (acc' (Var "bt9")))) (acc' (Var "bt8")))) (acc' (Var "bt7")))) (acc' (Var "bt6")))) (acc' (Var "bt5")))) (acc' (Var "bt4")))) (acc' (Var "bt3")))) (acc' (Var "bt2")))) (acc' (Var "bt1")).

(* Direct (DPIA-normal) form of the block. *)
Definition mbconve5s1r_direct {c e se m1 m2 : nat}
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  let c1 := Conv4d_1x1_s1 bex wex input in
  let n1 := BatchNorm4d c1 g1 z1 eps in
  let r1 := Swish4d n1 in
  let d1 := DWConv4d_5x5_s1 wdw r1 in
  let n2 := BatchNorm4d d1 g2 z2 eps in
  let r2 := Swish4d n2 in
  let se1 := SEBlock sw1 sb1 sw2 sb2 r2 in
  let p1 := Conv4d_1x1_s1 bpw wpw se1 in
  let n3 := BatchNorm4d p1 g3 z3 eps in
  let a1 := Add4d n3 input in
  seq (seq (seq (seq (seq (seq (seq (seq (seq ((A(acc' (Var "bt1"), c1)))
         ((A(acc' (Var "bt2"), n1))))
         ((A(acc' (Var "bt3"), r1))))
         ((A(acc' (Var "bt4"), d1))))
         ((A(acc' (Var "bt5"), n2))))
         ((A(acc' (Var "bt6"), r2))))
         ((seblock_direct sw1 sb1 sw2 sb2 r2 (acc' (Var "bt7")))))
         ((A(acc' (Var "bt8"), p1))))
         ((A(acc' (Var "bt9"), n3))))
         ((A(output, MBConvE5s1R input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps))).

Lemma mbconve5s1r_comm_eq_direct : forall (c e se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num))))),
  mbconve5s1r_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output =
  mbconve5s1r_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output.
Proof.
  intros.
  unfold mbconve5s1r_comm, mbconve5s1r_direct, new.
  cbv zeta beta.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_DWConv4d_5x5_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Swish4d.
  rewrite bind_read_replace_seq.
  rewrite seblock_comm_eq_direct.
  rewrite seblock_direct_read.
  rewrite <- A_Conv4d_1x1_s1.
  rewrite bind_read_replace_seq.
  rewrite <- A_BatchNorm4d.
  rewrite bind_read_replace.
  rewrite <- A_Add4d.
  reflexivity.
Qed.

(* Block-level DPIA correctness: observed at an output path, the imperative
   block computes the functional [MBConvE5s1R]. *)
Lemma A_MBConvE5s1R : forall (c e se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (output : acc (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (rho : env) (p : path),
  in_acc p output ->
  mbconve5s1r_comm input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps output rho p =
  A(output, MBConvE5s1R input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps) rho p.
Proof.
  intros. rewrite mbconve5s1r_comm_eq_direct.
  unfold mbconve5s1r_direct, MBConvE5s1R, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* Reading the block's output buffer after the (folded) direct form yields
   the functional block value. *)
Lemma mbconve5s1r_direct_read : forall (c e se m1 m2 : nat)
  (input : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))))
  (wex : exp (ary '{e} (ary '{c} (ary '{1} (ary '{1} num)))))
    (bex : exp (ary '{e} num))
    (g1 : exp (ary '{e} num))
    (z1 : exp (ary '{e} num))
  (wdw : exp (ary '{e} (ary '{5} (ary '{5} num))))
    (g2 : exp (ary '{e} num))
    (z2 : exp (ary '{e} num))
  (sw1 : exp (ary '{se} (ary '{e} num)))
    (sb1 : exp (ary '{se} num))
    (sw2 : exp (ary '{e} (ary '{se} num)))
    (sb2 : exp (ary '{e} num))
  (wpw : exp (ary '{c} (ary '{e} (ary '{1} (ary '{1} num)))))
    (bpw : exp (ary '{c} num))
    (g3 : exp (ary '{c} num))
    (z3 : exp (ary '{c} num))
  (eps : exp num)
  (q : path) (k : exp (ary '{1} (ary '{c} (ary '{m1} (ary '{m2} num)))) -> comm) (c0 : comm),
  seq (mbconve5s1r_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (bind_read (acc' q) k) c0) =
  seq (mbconve5s1r_direct input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps (acc' q))
      (seq (k (MBConvE5s1R input wex bex g1 z1 wdw g2 z2 sw1 sb1 sw2 sb2 wpw bpw g3 z3 eps)) c0).
Proof.
  intros. unfold mbconve5s1r_direct. cbv beta zeta.
  apply bind_read_replace_seq_r.
Qed.

(* -------------------------------------------------------------------------- *)
(* EfficientNet-B0 (batch = 1, symbolic input channels and spatial size m)    *)
(* -------------------------------------------------------------------------- *)

Section EfficientNetB0.
  Context {channel m : nat}.
  Context (input : exp (ary '{1} (ary '{channel} (ary '{m} (ary '{m} num))))).
  Context (eps : exp num).

  (* Stem: conv 3x3 p1 s2 + BN + swish (channel -> 32) *)
  Context (s_w : exp (ary '{32} (ary '{channel} (ary '{3} (ary '{3} num)))))
          (s_b : exp (ary '{32} num))
          (s_g : exp (ary '{32} num)) (s_z : exp (ary '{32} num)).
  (* Block 1 (MBConv1 k3 s1, 32 -> 16, se=8) *)
  Context (b1_wdw : exp (ary '{32} (ary '{3} (ary '{3} num))))
          (b1_g1 b1_z1 : exp (ary '{32} num))
          (b1_sw1 : exp (ary '{8} (ary '{32} num))) (b1_sb1 : exp (ary '{8} num))
          (b1_sw2 : exp (ary '{32} (ary '{8} num))) (b1_sb2 : exp (ary '{32} num))
          (b1_wpw : exp (ary '{16} (ary '{32} (ary '{1} (ary '{1} num)))))
          (b1_bpw b1_g2 b1_z2 : exp (ary '{16} num)).
  (* Block 2 (MBConvE3s2, 16 -> 24, e=96, se=4) *)
  Context (b2_wex : exp (ary '{96} (ary '{16} (ary '{1} (ary '{1} num)))))
          (b2_bex b2_g1 b2_z1 : exp (ary '{96} num))
          (b2_wdw : exp (ary '{96} (ary '{3} (ary '{3} num))))
          (b2_g2 b2_z2 : exp (ary '{96} num))
          (b2_sw1 : exp (ary '{4} (ary '{96} num))) (b2_sb1 : exp (ary '{4} num))
          (b2_sw2 : exp (ary '{96} (ary '{4} num))) (b2_sb2 : exp (ary '{96} num))
          (b2_wpw : exp (ary '{24} (ary '{96} (ary '{1} (ary '{1} num)))))
          (b2_bpw b2_g3 b2_z3 : exp (ary '{24} num)).
  (* Block 3 (MBConvE3s1R, 24 -> 24, e=144, se=6) *)
  Context (b3_wex : exp (ary '{144} (ary '{24} (ary '{1} (ary '{1} num)))))
          (b3_bex b3_g1 b3_z1 : exp (ary '{144} num))
          (b3_wdw : exp (ary '{144} (ary '{3} (ary '{3} num))))
          (b3_g2 b3_z2 : exp (ary '{144} num))
          (b3_sw1 : exp (ary '{6} (ary '{144} num))) (b3_sb1 : exp (ary '{6} num))
          (b3_sw2 : exp (ary '{144} (ary '{6} num))) (b3_sb2 : exp (ary '{144} num))
          (b3_wpw : exp (ary '{24} (ary '{144} (ary '{1} (ary '{1} num)))))
          (b3_bpw b3_g3 b3_z3 : exp (ary '{24} num)).
  (* Block 4 (MBConvE5s2, 24 -> 40, e=144, se=6) *)
  Context (b4_wex : exp (ary '{144} (ary '{24} (ary '{1} (ary '{1} num)))))
          (b4_bex b4_g1 b4_z1 : exp (ary '{144} num))
          (b4_wdw : exp (ary '{144} (ary '{5} (ary '{5} num))))
          (b4_g2 b4_z2 : exp (ary '{144} num))
          (b4_sw1 : exp (ary '{6} (ary '{144} num))) (b4_sb1 : exp (ary '{6} num))
          (b4_sw2 : exp (ary '{144} (ary '{6} num))) (b4_sb2 : exp (ary '{144} num))
          (b4_wpw : exp (ary '{40} (ary '{144} (ary '{1} (ary '{1} num)))))
          (b4_bpw b4_g3 b4_z3 : exp (ary '{40} num)).
  (* Block 5 (MBConvE5s1R, 40 -> 40, e=240, se=10) *)
  Context (b5_wex : exp (ary '{240} (ary '{40} (ary '{1} (ary '{1} num)))))
          (b5_bex b5_g1 b5_z1 : exp (ary '{240} num))
          (b5_wdw : exp (ary '{240} (ary '{5} (ary '{5} num))))
          (b5_g2 b5_z2 : exp (ary '{240} num))
          (b5_sw1 : exp (ary '{10} (ary '{240} num))) (b5_sb1 : exp (ary '{10} num))
          (b5_sw2 : exp (ary '{240} (ary '{10} num))) (b5_sb2 : exp (ary '{240} num))
          (b5_wpw : exp (ary '{40} (ary '{240} (ary '{1} (ary '{1} num)))))
          (b5_bpw b5_g3 b5_z3 : exp (ary '{40} num)).
  (* Block 6 (MBConvE3s2, 40 -> 80, e=240, se=10) *)
  Context (b6_wex : exp (ary '{240} (ary '{40} (ary '{1} (ary '{1} num)))))
          (b6_bex b6_g1 b6_z1 : exp (ary '{240} num))
          (b6_wdw : exp (ary '{240} (ary '{3} (ary '{3} num))))
          (b6_g2 b6_z2 : exp (ary '{240} num))
          (b6_sw1 : exp (ary '{10} (ary '{240} num))) (b6_sb1 : exp (ary '{10} num))
          (b6_sw2 : exp (ary '{240} (ary '{10} num))) (b6_sb2 : exp (ary '{240} num))
          (b6_wpw : exp (ary '{80} (ary '{240} (ary '{1} (ary '{1} num)))))
          (b6_bpw b6_g3 b6_z3 : exp (ary '{80} num)).
  (* Block 7 (MBConvE3s1R, 80 -> 80, e=480, se=20) *)
  Context (b7_wex : exp (ary '{480} (ary '{80} (ary '{1} (ary '{1} num)))))
          (b7_bex b7_g1 b7_z1 : exp (ary '{480} num))
          (b7_wdw : exp (ary '{480} (ary '{3} (ary '{3} num))))
          (b7_g2 b7_z2 : exp (ary '{480} num))
          (b7_sw1 : exp (ary '{20} (ary '{480} num))) (b7_sb1 : exp (ary '{20} num))
          (b7_sw2 : exp (ary '{480} (ary '{20} num))) (b7_sb2 : exp (ary '{480} num))
          (b7_wpw : exp (ary '{80} (ary '{480} (ary '{1} (ary '{1} num)))))
          (b7_bpw b7_g3 b7_z3 : exp (ary '{80} num)).
  (* Block 8 (MBConvE3s1R, 80 -> 80, e=480, se=20) *)
  Context (b8_wex : exp (ary '{480} (ary '{80} (ary '{1} (ary '{1} num)))))
          (b8_bex b8_g1 b8_z1 : exp (ary '{480} num))
          (b8_wdw : exp (ary '{480} (ary '{3} (ary '{3} num))))
          (b8_g2 b8_z2 : exp (ary '{480} num))
          (b8_sw1 : exp (ary '{20} (ary '{480} num))) (b8_sb1 : exp (ary '{20} num))
          (b8_sw2 : exp (ary '{480} (ary '{20} num))) (b8_sb2 : exp (ary '{480} num))
          (b8_wpw : exp (ary '{80} (ary '{480} (ary '{1} (ary '{1} num)))))
          (b8_bpw b8_g3 b8_z3 : exp (ary '{80} num)).
  (* Block 9 (MBConvE5s1, 80 -> 112, e=480, se=20) *)
  Context (b9_wex : exp (ary '{480} (ary '{80} (ary '{1} (ary '{1} num)))))
          (b9_bex b9_g1 b9_z1 : exp (ary '{480} num))
          (b9_wdw : exp (ary '{480} (ary '{5} (ary '{5} num))))
          (b9_g2 b9_z2 : exp (ary '{480} num))
          (b9_sw1 : exp (ary '{20} (ary '{480} num))) (b9_sb1 : exp (ary '{20} num))
          (b9_sw2 : exp (ary '{480} (ary '{20} num))) (b9_sb2 : exp (ary '{480} num))
          (b9_wpw : exp (ary '{112} (ary '{480} (ary '{1} (ary '{1} num)))))
          (b9_bpw b9_g3 b9_z3 : exp (ary '{112} num)).
  (* Block 10 (MBConvE5s1R, 112 -> 112, e=672, se=28) *)
  Context (b10_wex : exp (ary '{672} (ary '{112} (ary '{1} (ary '{1} num)))))
          (b10_bex b10_g1 b10_z1 : exp (ary '{672} num))
          (b10_wdw : exp (ary '{672} (ary '{5} (ary '{5} num))))
          (b10_g2 b10_z2 : exp (ary '{672} num))
          (b10_sw1 : exp (ary '{28} (ary '{672} num))) (b10_sb1 : exp (ary '{28} num))
          (b10_sw2 : exp (ary '{672} (ary '{28} num))) (b10_sb2 : exp (ary '{672} num))
          (b10_wpw : exp (ary '{112} (ary '{672} (ary '{1} (ary '{1} num)))))
          (b10_bpw b10_g3 b10_z3 : exp (ary '{112} num)).
  (* Block 11 (MBConvE5s1R, 112 -> 112, e=672, se=28) *)
  Context (b11_wex : exp (ary '{672} (ary '{112} (ary '{1} (ary '{1} num)))))
          (b11_bex b11_g1 b11_z1 : exp (ary '{672} num))
          (b11_wdw : exp (ary '{672} (ary '{5} (ary '{5} num))))
          (b11_g2 b11_z2 : exp (ary '{672} num))
          (b11_sw1 : exp (ary '{28} (ary '{672} num))) (b11_sb1 : exp (ary '{28} num))
          (b11_sw2 : exp (ary '{672} (ary '{28} num))) (b11_sb2 : exp (ary '{672} num))
          (b11_wpw : exp (ary '{112} (ary '{672} (ary '{1} (ary '{1} num)))))
          (b11_bpw b11_g3 b11_z3 : exp (ary '{112} num)).
  (* Block 12 (MBConvE5s2, 112 -> 192, e=672, se=28) *)
  Context (b12_wex : exp (ary '{672} (ary '{112} (ary '{1} (ary '{1} num)))))
          (b12_bex b12_g1 b12_z1 : exp (ary '{672} num))
          (b12_wdw : exp (ary '{672} (ary '{5} (ary '{5} num))))
          (b12_g2 b12_z2 : exp (ary '{672} num))
          (b12_sw1 : exp (ary '{28} (ary '{672} num))) (b12_sb1 : exp (ary '{28} num))
          (b12_sw2 : exp (ary '{672} (ary '{28} num))) (b12_sb2 : exp (ary '{672} num))
          (b12_wpw : exp (ary '{192} (ary '{672} (ary '{1} (ary '{1} num)))))
          (b12_bpw b12_g3 b12_z3 : exp (ary '{192} num)).
  (* Block 13 (MBConvE5s1R, 192 -> 192, e=1152, se=48) *)
  Context (b13_wex : exp (ary '{1152} (ary '{192} (ary '{1} (ary '{1} num)))))
          (b13_bex b13_g1 b13_z1 : exp (ary '{1152} num))
          (b13_wdw : exp (ary '{1152} (ary '{5} (ary '{5} num))))
          (b13_g2 b13_z2 : exp (ary '{1152} num))
          (b13_sw1 : exp (ary '{48} (ary '{1152} num))) (b13_sb1 : exp (ary '{48} num))
          (b13_sw2 : exp (ary '{1152} (ary '{48} num))) (b13_sb2 : exp (ary '{1152} num))
          (b13_wpw : exp (ary '{192} (ary '{1152} (ary '{1} (ary '{1} num)))))
          (b13_bpw b13_g3 b13_z3 : exp (ary '{192} num)).
  (* Block 14 (MBConvE5s1R, 192 -> 192, e=1152, se=48) *)
  Context (b14_wex : exp (ary '{1152} (ary '{192} (ary '{1} (ary '{1} num)))))
          (b14_bex b14_g1 b14_z1 : exp (ary '{1152} num))
          (b14_wdw : exp (ary '{1152} (ary '{5} (ary '{5} num))))
          (b14_g2 b14_z2 : exp (ary '{1152} num))
          (b14_sw1 : exp (ary '{48} (ary '{1152} num))) (b14_sb1 : exp (ary '{48} num))
          (b14_sw2 : exp (ary '{1152} (ary '{48} num))) (b14_sb2 : exp (ary '{1152} num))
          (b14_wpw : exp (ary '{192} (ary '{1152} (ary '{1} (ary '{1} num)))))
          (b14_bpw b14_g3 b14_z3 : exp (ary '{192} num)).
  (* Block 15 (MBConvE5s1R, 192 -> 192, e=1152, se=48) *)
  Context (b15_wex : exp (ary '{1152} (ary '{192} (ary '{1} (ary '{1} num)))))
          (b15_bex b15_g1 b15_z1 : exp (ary '{1152} num))
          (b15_wdw : exp (ary '{1152} (ary '{5} (ary '{5} num))))
          (b15_g2 b15_z2 : exp (ary '{1152} num))
          (b15_sw1 : exp (ary '{48} (ary '{1152} num))) (b15_sb1 : exp (ary '{48} num))
          (b15_sw2 : exp (ary '{1152} (ary '{48} num))) (b15_sb2 : exp (ary '{1152} num))
          (b15_wpw : exp (ary '{192} (ary '{1152} (ary '{1} (ary '{1} num)))))
          (b15_bpw b15_g3 b15_z3 : exp (ary '{192} num)).
  (* Block 16 (MBConvE3s1, 192 -> 320, e=1152, se=48) *)
  Context (b16_wex : exp (ary '{1152} (ary '{192} (ary '{1} (ary '{1} num)))))
          (b16_bex b16_g1 b16_z1 : exp (ary '{1152} num))
          (b16_wdw : exp (ary '{1152} (ary '{3} (ary '{3} num))))
          (b16_g2 b16_z2 : exp (ary '{1152} num))
          (b16_sw1 : exp (ary '{48} (ary '{1152} num))) (b16_sb1 : exp (ary '{48} num))
          (b16_sw2 : exp (ary '{1152} (ary '{48} num))) (b16_sb2 : exp (ary '{1152} num))
          (b16_wpw : exp (ary '{320} (ary '{1152} (ary '{1} (ary '{1} num)))))
          (b16_bpw b16_g3 b16_z3 : exp (ary '{320} num)).

  (* Head: conv 1x1 (320 -> 1280) + BN + swish; classifier fc(1000) *)
  Context (h_w : exp (ary '{1280} (ary '{320} (ary '{1} (ary '{1} num)))))
          (h_b : exp (ary '{1280} num))
          (h_g : exp (ary '{1280} num)) (h_z : exp (ary '{1280} num)).
  Context (fc_w : exp (ary '{1000} (ary '{1280} num)))
          (fc_b : exp (ary '{1000} num)).

  (* ---------------- Functional EfficientNet-B0 (opaque layer wrappers) ---
     Each layer value is a separate definition; after the body lemmas they
     are made [Opaque] so that the network-level proofs never inline a layer
     into the next one. *)

  Definition eb_x1 := Conv4d_3x3_s2 s_b s_w input.
  Definition eb_x2 := BatchNorm4d eb_x1 s_g s_z eps.
  Definition eb_x3 := Swish4d eb_x2.
  Definition eb_x4 := MBConv1 eb_x3 b1_wdw b1_g1 b1_z1 b1_sw1 b1_sb1 b1_sw2 b1_sb2 b1_wpw b1_bpw b1_g2 b1_z2 eps.
  Definition eb_x5 := MBConvE3s2 eb_x4 b2_wex b2_bex b2_g1 b2_z1 b2_wdw b2_g2 b2_z2 b2_sw1 b2_sb1 b2_sw2 b2_sb2 b2_wpw b2_bpw b2_g3 b2_z3 eps.
  Definition eb_x6 := MBConvE3s1R eb_x5 b3_wex b3_bex b3_g1 b3_z1 b3_wdw b3_g2 b3_z2 b3_sw1 b3_sb1 b3_sw2 b3_sb2 b3_wpw b3_bpw b3_g3 b3_z3 eps.
  Definition eb_x7 := MBConvE5s2 eb_x6 b4_wex b4_bex b4_g1 b4_z1 b4_wdw b4_g2 b4_z2 b4_sw1 b4_sb1 b4_sw2 b4_sb2 b4_wpw b4_bpw b4_g3 b4_z3 eps.
  Definition eb_x8 := MBConvE5s1R eb_x7 b5_wex b5_bex b5_g1 b5_z1 b5_wdw b5_g2 b5_z2 b5_sw1 b5_sb1 b5_sw2 b5_sb2 b5_wpw b5_bpw b5_g3 b5_z3 eps.
  Definition eb_x9 := MBConvE3s2 eb_x8 b6_wex b6_bex b6_g1 b6_z1 b6_wdw b6_g2 b6_z2 b6_sw1 b6_sb1 b6_sw2 b6_sb2 b6_wpw b6_bpw b6_g3 b6_z3 eps.
  Definition eb_x10 := MBConvE3s1R eb_x9 b7_wex b7_bex b7_g1 b7_z1 b7_wdw b7_g2 b7_z2 b7_sw1 b7_sb1 b7_sw2 b7_sb2 b7_wpw b7_bpw b7_g3 b7_z3 eps.
  Definition eb_x11 := MBConvE3s1R eb_x10 b8_wex b8_bex b8_g1 b8_z1 b8_wdw b8_g2 b8_z2 b8_sw1 b8_sb1 b8_sw2 b8_sb2 b8_wpw b8_bpw b8_g3 b8_z3 eps.
  Definition eb_x12 := MBConvE5s1 eb_x11 b9_wex b9_bex b9_g1 b9_z1 b9_wdw b9_g2 b9_z2 b9_sw1 b9_sb1 b9_sw2 b9_sb2 b9_wpw b9_bpw b9_g3 b9_z3 eps.
  Definition eb_x13 := MBConvE5s1R eb_x12 b10_wex b10_bex b10_g1 b10_z1 b10_wdw b10_g2 b10_z2 b10_sw1 b10_sb1 b10_sw2 b10_sb2 b10_wpw b10_bpw b10_g3 b10_z3 eps.
  Definition eb_x14 := MBConvE5s1R eb_x13 b11_wex b11_bex b11_g1 b11_z1 b11_wdw b11_g2 b11_z2 b11_sw1 b11_sb1 b11_sw2 b11_sb2 b11_wpw b11_bpw b11_g3 b11_z3 eps.
  Definition eb_x15 := MBConvE5s2 eb_x14 b12_wex b12_bex b12_g1 b12_z1 b12_wdw b12_g2 b12_z2 b12_sw1 b12_sb1 b12_sw2 b12_sb2 b12_wpw b12_bpw b12_g3 b12_z3 eps.
  Definition eb_x16 := MBConvE5s1R eb_x15 b13_wex b13_bex b13_g1 b13_z1 b13_wdw b13_g2 b13_z2 b13_sw1 b13_sb1 b13_sw2 b13_sb2 b13_wpw b13_bpw b13_g3 b13_z3 eps.
  Definition eb_x17 := MBConvE5s1R eb_x16 b14_wex b14_bex b14_g1 b14_z1 b14_wdw b14_g2 b14_z2 b14_sw1 b14_sb1 b14_sw2 b14_sb2 b14_wpw b14_bpw b14_g3 b14_z3 eps.
  Definition eb_x18 := MBConvE5s1R eb_x17 b15_wex b15_bex b15_g1 b15_z1 b15_wdw b15_g2 b15_z2 b15_sw1 b15_sb1 b15_sw2 b15_sb2 b15_wpw b15_bpw b15_g3 b15_z3 eps.
  Definition eb_x19 := MBConvE3s1 eb_x18 b16_wex b16_bex b16_g1 b16_z1 b16_wdw b16_g2 b16_z2 b16_sw1 b16_sb1 b16_sw2 b16_sb2 b16_wpw b16_bpw b16_g3 b16_z3 eps.
  Definition eb_x20 := Conv4d_1x1_s1 h_b h_w eb_x19.
  Definition eb_x21 := BatchNorm4d eb_x20 h_g h_z eps.
  Definition eb_x22 := Swish4d eb_x21.
  Definition eb_x23 := GlobalAvgPool4d eb_x22.
  Definition eb_x24 := Softmax2d (Linear2d fc_w fc_b eb_x23).

  Lemma eb_x1_body : eb_x1 = Conv4d_3x3_s2 s_b s_w input.
  Proof. reflexivity. Qed.
  Lemma eb_x2_body : eb_x2 = BatchNorm4d eb_x1 s_g s_z eps.
  Proof. reflexivity. Qed.
  Lemma eb_x3_body : eb_x3 = Swish4d eb_x2.
  Proof. reflexivity. Qed.
  Lemma eb_x4_body : eb_x4 = MBConv1 eb_x3 b1_wdw b1_g1 b1_z1 b1_sw1 b1_sb1 b1_sw2 b1_sb2 b1_wpw b1_bpw b1_g2 b1_z2 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x5_body : eb_x5 = MBConvE3s2 eb_x4 b2_wex b2_bex b2_g1 b2_z1 b2_wdw b2_g2 b2_z2 b2_sw1 b2_sb1 b2_sw2 b2_sb2 b2_wpw b2_bpw b2_g3 b2_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x6_body : eb_x6 = MBConvE3s1R eb_x5 b3_wex b3_bex b3_g1 b3_z1 b3_wdw b3_g2 b3_z2 b3_sw1 b3_sb1 b3_sw2 b3_sb2 b3_wpw b3_bpw b3_g3 b3_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x7_body : eb_x7 = MBConvE5s2 eb_x6 b4_wex b4_bex b4_g1 b4_z1 b4_wdw b4_g2 b4_z2 b4_sw1 b4_sb1 b4_sw2 b4_sb2 b4_wpw b4_bpw b4_g3 b4_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x8_body : eb_x8 = MBConvE5s1R eb_x7 b5_wex b5_bex b5_g1 b5_z1 b5_wdw b5_g2 b5_z2 b5_sw1 b5_sb1 b5_sw2 b5_sb2 b5_wpw b5_bpw b5_g3 b5_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x9_body : eb_x9 = MBConvE3s2 eb_x8 b6_wex b6_bex b6_g1 b6_z1 b6_wdw b6_g2 b6_z2 b6_sw1 b6_sb1 b6_sw2 b6_sb2 b6_wpw b6_bpw b6_g3 b6_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x10_body : eb_x10 = MBConvE3s1R eb_x9 b7_wex b7_bex b7_g1 b7_z1 b7_wdw b7_g2 b7_z2 b7_sw1 b7_sb1 b7_sw2 b7_sb2 b7_wpw b7_bpw b7_g3 b7_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x11_body : eb_x11 = MBConvE3s1R eb_x10 b8_wex b8_bex b8_g1 b8_z1 b8_wdw b8_g2 b8_z2 b8_sw1 b8_sb1 b8_sw2 b8_sb2 b8_wpw b8_bpw b8_g3 b8_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x12_body : eb_x12 = MBConvE5s1 eb_x11 b9_wex b9_bex b9_g1 b9_z1 b9_wdw b9_g2 b9_z2 b9_sw1 b9_sb1 b9_sw2 b9_sb2 b9_wpw b9_bpw b9_g3 b9_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x13_body : eb_x13 = MBConvE5s1R eb_x12 b10_wex b10_bex b10_g1 b10_z1 b10_wdw b10_g2 b10_z2 b10_sw1 b10_sb1 b10_sw2 b10_sb2 b10_wpw b10_bpw b10_g3 b10_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x14_body : eb_x14 = MBConvE5s1R eb_x13 b11_wex b11_bex b11_g1 b11_z1 b11_wdw b11_g2 b11_z2 b11_sw1 b11_sb1 b11_sw2 b11_sb2 b11_wpw b11_bpw b11_g3 b11_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x15_body : eb_x15 = MBConvE5s2 eb_x14 b12_wex b12_bex b12_g1 b12_z1 b12_wdw b12_g2 b12_z2 b12_sw1 b12_sb1 b12_sw2 b12_sb2 b12_wpw b12_bpw b12_g3 b12_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x16_body : eb_x16 = MBConvE5s1R eb_x15 b13_wex b13_bex b13_g1 b13_z1 b13_wdw b13_g2 b13_z2 b13_sw1 b13_sb1 b13_sw2 b13_sb2 b13_wpw b13_bpw b13_g3 b13_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x17_body : eb_x17 = MBConvE5s1R eb_x16 b14_wex b14_bex b14_g1 b14_z1 b14_wdw b14_g2 b14_z2 b14_sw1 b14_sb1 b14_sw2 b14_sb2 b14_wpw b14_bpw b14_g3 b14_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x18_body : eb_x18 = MBConvE5s1R eb_x17 b15_wex b15_bex b15_g1 b15_z1 b15_wdw b15_g2 b15_z2 b15_sw1 b15_sb1 b15_sw2 b15_sb2 b15_wpw b15_bpw b15_g3 b15_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x19_body : eb_x19 = MBConvE3s1 eb_x18 b16_wex b16_bex b16_g1 b16_z1 b16_wdw b16_g2 b16_z2 b16_sw1 b16_sb1 b16_sw2 b16_sb2 b16_wpw b16_bpw b16_g3 b16_z3 eps.
  Proof. reflexivity. Qed.
  Lemma eb_x20_body : eb_x20 = Conv4d_1x1_s1 h_b h_w eb_x19.
  Proof. reflexivity. Qed.
  Lemma eb_x21_body : eb_x21 = BatchNorm4d eb_x20 h_g h_z eps.
  Proof. reflexivity. Qed.
  Lemma eb_x22_body : eb_x22 = Swish4d eb_x21.
  Proof. reflexivity. Qed.
  Lemma eb_x23_body : eb_x23 = GlobalAvgPool4d eb_x22.
  Proof. reflexivity. Qed.
  Lemma eb_x24_body : eb_x24 = Softmax2d (Linear2d fc_w fc_b eb_x23).
  Proof. reflexivity. Qed.

  Opaque eb_x1 eb_x2 eb_x3 eb_x4 eb_x5 eb_x6 eb_x7 eb_x8 eb_x9 eb_x10
         eb_x11 eb_x12 eb_x13 eb_x14 eb_x15 eb_x16 eb_x17 eb_x18 eb_x19
         eb_x20 eb_x21 eb_x22 eb_x23 eb_x24.

  Definition EfficientNetB0 : exp (ary '{1} (ary '{1000} num)) := eb_x24.

  (* ---------------- Imperative EfficientNet-B0 (buffer-layered) --------- *)
  Definition efficientnetb0_comm (output : acc (ary '{1} (ary '{1000} num)))
    : comm :=
new (fun t1 => seq (Conv4d_3x3_s2_comm s_b s_w input t1)
(new (fun t2 => seq (bind_read t1 (fun e1 => BatchNorm4d_comm e1 s_g s_z eps t2))
(new (fun t3 => seq (bind_read t2 (fun e2 => Swish4d_comm e2 t3))
(new (fun t4 => seq (bind_read t3 (fun e3 => mbconv1_comm e3 b1_wdw b1_g1 b1_z1 b1_sw1 b1_sb1 b1_sw2 b1_sb2 b1_wpw b1_bpw b1_g2 b1_z2 eps t4))
(new (fun t5 => seq (bind_read t4 (fun e4 => mbconve3s2_comm e4 b2_wex b2_bex b2_g1 b2_z1 b2_wdw b2_g2 b2_z2 b2_sw1 b2_sb1 b2_sw2 b2_sb2 b2_wpw b2_bpw b2_g3 b2_z3 eps t5))
(new (fun t6 => seq (bind_read t5 (fun e5 => mbconve3s1r_comm e5 b3_wex b3_bex b3_g1 b3_z1 b3_wdw b3_g2 b3_z2 b3_sw1 b3_sb1 b3_sw2 b3_sb2 b3_wpw b3_bpw b3_g3 b3_z3 eps t6))
(new (fun t7 => seq (bind_read t6 (fun e6 => mbconve5s2_comm e6 b4_wex b4_bex b4_g1 b4_z1 b4_wdw b4_g2 b4_z2 b4_sw1 b4_sb1 b4_sw2 b4_sb2 b4_wpw b4_bpw b4_g3 b4_z3 eps t7))
(new (fun t8 => seq (bind_read t7 (fun e7 => mbconve5s1r_comm e7 b5_wex b5_bex b5_g1 b5_z1 b5_wdw b5_g2 b5_z2 b5_sw1 b5_sb1 b5_sw2 b5_sb2 b5_wpw b5_bpw b5_g3 b5_z3 eps t8))
(new (fun t9 => seq (bind_read t8 (fun e8 => mbconve3s2_comm e8 b6_wex b6_bex b6_g1 b6_z1 b6_wdw b6_g2 b6_z2 b6_sw1 b6_sb1 b6_sw2 b6_sb2 b6_wpw b6_bpw b6_g3 b6_z3 eps t9))
(new (fun t10 => seq (bind_read t9 (fun e9 => mbconve3s1r_comm e9 b7_wex b7_bex b7_g1 b7_z1 b7_wdw b7_g2 b7_z2 b7_sw1 b7_sb1 b7_sw2 b7_sb2 b7_wpw b7_bpw b7_g3 b7_z3 eps t10))
(new (fun t11 => seq (bind_read t10 (fun e10 => mbconve3s1r_comm e10 b8_wex b8_bex b8_g1 b8_z1 b8_wdw b8_g2 b8_z2 b8_sw1 b8_sb1 b8_sw2 b8_sb2 b8_wpw b8_bpw b8_g3 b8_z3 eps t11))
(new (fun t12 => seq (bind_read t11 (fun e11 => mbconve5s1_comm e11 b9_wex b9_bex b9_g1 b9_z1 b9_wdw b9_g2 b9_z2 b9_sw1 b9_sb1 b9_sw2 b9_sb2 b9_wpw b9_bpw b9_g3 b9_z3 eps t12))
(new (fun t13 => seq (bind_read t12 (fun e12 => mbconve5s1r_comm e12 b10_wex b10_bex b10_g1 b10_z1 b10_wdw b10_g2 b10_z2 b10_sw1 b10_sb1 b10_sw2 b10_sb2 b10_wpw b10_bpw b10_g3 b10_z3 eps t13))
(new (fun t14 => seq (bind_read t13 (fun e13 => mbconve5s1r_comm e13 b11_wex b11_bex b11_g1 b11_z1 b11_wdw b11_g2 b11_z2 b11_sw1 b11_sb1 b11_sw2 b11_sb2 b11_wpw b11_bpw b11_g3 b11_z3 eps t14))
(new (fun t15 => seq (bind_read t14 (fun e14 => mbconve5s2_comm e14 b12_wex b12_bex b12_g1 b12_z1 b12_wdw b12_g2 b12_z2 b12_sw1 b12_sb1 b12_sw2 b12_sb2 b12_wpw b12_bpw b12_g3 b12_z3 eps t15))
(new (fun t16 => seq (bind_read t15 (fun e15 => mbconve5s1r_comm e15 b13_wex b13_bex b13_g1 b13_z1 b13_wdw b13_g2 b13_z2 b13_sw1 b13_sb1 b13_sw2 b13_sb2 b13_wpw b13_bpw b13_g3 b13_z3 eps t16))
(new (fun t17 => seq (bind_read t16 (fun e16 => mbconve5s1r_comm e16 b14_wex b14_bex b14_g1 b14_z1 b14_wdw b14_g2 b14_z2 b14_sw1 b14_sb1 b14_sw2 b14_sb2 b14_wpw b14_bpw b14_g3 b14_z3 eps t17))
(new (fun t18 => seq (bind_read t17 (fun e17 => mbconve5s1r_comm e17 b15_wex b15_bex b15_g1 b15_z1 b15_wdw b15_g2 b15_z2 b15_sw1 b15_sb1 b15_sw2 b15_sb2 b15_wpw b15_bpw b15_g3 b15_z3 eps t18))
(new (fun t19 => seq (bind_read t18 (fun e18 => mbconve3s1_comm e18 b16_wex b16_bex b16_g1 b16_z1 b16_wdw b16_g2 b16_z2 b16_sw1 b16_sb1 b16_sw2 b16_sb2 b16_wpw b16_bpw b16_g3 b16_z3 eps t19))
(new (fun t20 => seq (bind_read t19 (fun e19 => Conv4d_1x1_s1_comm h_b h_w e19 t20))
(new (fun t21 => seq (bind_read t20 (fun e20 => BatchNorm4d_comm e20 h_g h_z eps t21))
(new (fun t22 => seq (bind_read t21 (fun e21 => Swish4d_comm e21 t22))
(new (fun t23 => seq (bind_read t22 (fun e22 => GlobalAvgPool4d_comm e22 t23))
     (bind_read t23 (fun e23 => Softmax2d_comm (Linear2d fc_w fc_b e23) output))) (acc' (Var "l23")))) (acc' (Var "l22")))) (acc' (Var "l21")))) (acc' (Var "l20")))) (acc' (Var "l19")))) (acc' (Var "l18")))) (acc' (Var "l17")))) (acc' (Var "l16")))) (acc' (Var "l15")))) (acc' (Var "l14")))) (acc' (Var "l13")))) (acc' (Var "l12")))) (acc' (Var "l11")))) (acc' (Var "l10")))) (acc' (Var "l9")))) (acc' (Var "l8")))) (acc' (Var "l7")))) (acc' (Var "l6")))) (acc' (Var "l5")))) (acc' (Var "l4")))) (acc' (Var "l3")))) (acc' (Var "l2")))) (acc' (Var "l1")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)
  Definition efficientnetb0_comm_direct (output : acc (ary '{1} (ary '{1000} num)))
    : comm :=
    seq (A(acc' (Var "l1"), eb_x1))
    (seq (A(acc' (Var "l2"), eb_x2))
    (seq (A(acc' (Var "l3"), eb_x3))
    (seq (mbconv1_direct eb_x3 b1_wdw b1_g1 b1_z1 b1_sw1 b1_sb1 b1_sw2 b1_sb2 b1_wpw b1_bpw b1_g2 b1_z2 eps (acc' (Var "l4")))
    (seq (mbconve3s2_direct eb_x4 b2_wex b2_bex b2_g1 b2_z1 b2_wdw b2_g2 b2_z2 b2_sw1 b2_sb1 b2_sw2 b2_sb2 b2_wpw b2_bpw b2_g3 b2_z3 eps (acc' (Var "l5")))
    (seq (mbconve3s1r_direct eb_x5 b3_wex b3_bex b3_g1 b3_z1 b3_wdw b3_g2 b3_z2 b3_sw1 b3_sb1 b3_sw2 b3_sb2 b3_wpw b3_bpw b3_g3 b3_z3 eps (acc' (Var "l6")))
    (seq (mbconve5s2_direct eb_x6 b4_wex b4_bex b4_g1 b4_z1 b4_wdw b4_g2 b4_z2 b4_sw1 b4_sb1 b4_sw2 b4_sb2 b4_wpw b4_bpw b4_g3 b4_z3 eps (acc' (Var "l7")))
    (seq (mbconve5s1r_direct eb_x7 b5_wex b5_bex b5_g1 b5_z1 b5_wdw b5_g2 b5_z2 b5_sw1 b5_sb1 b5_sw2 b5_sb2 b5_wpw b5_bpw b5_g3 b5_z3 eps (acc' (Var "l8")))
    (seq (mbconve3s2_direct eb_x8 b6_wex b6_bex b6_g1 b6_z1 b6_wdw b6_g2 b6_z2 b6_sw1 b6_sb1 b6_sw2 b6_sb2 b6_wpw b6_bpw b6_g3 b6_z3 eps (acc' (Var "l9")))
    (seq (mbconve3s1r_direct eb_x9 b7_wex b7_bex b7_g1 b7_z1 b7_wdw b7_g2 b7_z2 b7_sw1 b7_sb1 b7_sw2 b7_sb2 b7_wpw b7_bpw b7_g3 b7_z3 eps (acc' (Var "l10")))
    (seq (mbconve3s1r_direct eb_x10 b8_wex b8_bex b8_g1 b8_z1 b8_wdw b8_g2 b8_z2 b8_sw1 b8_sb1 b8_sw2 b8_sb2 b8_wpw b8_bpw b8_g3 b8_z3 eps (acc' (Var "l11")))
    (seq (mbconve5s1_direct eb_x11 b9_wex b9_bex b9_g1 b9_z1 b9_wdw b9_g2 b9_z2 b9_sw1 b9_sb1 b9_sw2 b9_sb2 b9_wpw b9_bpw b9_g3 b9_z3 eps (acc' (Var "l12")))
    (seq (mbconve5s1r_direct eb_x12 b10_wex b10_bex b10_g1 b10_z1 b10_wdw b10_g2 b10_z2 b10_sw1 b10_sb1 b10_sw2 b10_sb2 b10_wpw b10_bpw b10_g3 b10_z3 eps (acc' (Var "l13")))
    (seq (mbconve5s1r_direct eb_x13 b11_wex b11_bex b11_g1 b11_z1 b11_wdw b11_g2 b11_z2 b11_sw1 b11_sb1 b11_sw2 b11_sb2 b11_wpw b11_bpw b11_g3 b11_z3 eps (acc' (Var "l14")))
    (seq (mbconve5s2_direct eb_x14 b12_wex b12_bex b12_g1 b12_z1 b12_wdw b12_g2 b12_z2 b12_sw1 b12_sb1 b12_sw2 b12_sb2 b12_wpw b12_bpw b12_g3 b12_z3 eps (acc' (Var "l15")))
    (seq (mbconve5s1r_direct eb_x15 b13_wex b13_bex b13_g1 b13_z1 b13_wdw b13_g2 b13_z2 b13_sw1 b13_sb1 b13_sw2 b13_sb2 b13_wpw b13_bpw b13_g3 b13_z3 eps (acc' (Var "l16")))
    (seq (mbconve5s1r_direct eb_x16 b14_wex b14_bex b14_g1 b14_z1 b14_wdw b14_g2 b14_z2 b14_sw1 b14_sb1 b14_sw2 b14_sb2 b14_wpw b14_bpw b14_g3 b14_z3 eps (acc' (Var "l17")))
    (seq (mbconve5s1r_direct eb_x17 b15_wex b15_bex b15_g1 b15_z1 b15_wdw b15_g2 b15_z2 b15_sw1 b15_sb1 b15_sw2 b15_sb2 b15_wpw b15_bpw b15_g3 b15_z3 eps (acc' (Var "l18")))
    (seq (mbconve3s1_direct eb_x18 b16_wex b16_bex b16_g1 b16_z1 b16_wdw b16_g2 b16_z2 b16_sw1 b16_sb1 b16_sw2 b16_sb2 b16_wpw b16_bpw b16_g3 b16_z3 eps (acc' (Var "l19")))
    (seq (A(acc' (Var "l20"), eb_x20))
    (seq (A(acc' (Var "l21"), eb_x21))
    (seq (A(acc' (Var "l22"), eb_x22))
    (seq (A(acc' (Var "l23"), eb_x23))
    ((A(output, eb_x24))))))))))))))))))))))))).

  (* ---------------- Freshness ------------------------------------------- *)
  Definition r1_acc : acc (ary '{1} (ary '{32} (ary '{half (m)} (ary '{half (m)} num))))
    := acc' (Var "l1").
  Definition r2_acc : acc (ary '{1} (ary '{32} (ary '{half (m)} (ary '{half (m)} num))))
    := acc' (Var "l2").
  Definition r3_acc : acc (ary '{1} (ary '{32} (ary '{half (m)} (ary '{half (m)} num))))
    := acc' (Var "l3").
  Definition r4_acc : acc (ary '{1} (ary '{16} (ary '{half (m)} (ary '{half (m)} num))))
    := acc' (Var "l4").
  Definition r5_acc : acc (ary '{1} (ary '{24} (ary '{half (half (m))} (ary '{half (half (m))} num))))
    := acc' (Var "l5").
  Definition r6_acc : acc (ary '{1} (ary '{24} (ary '{half (half (m))} (ary '{half (half (m))} num))))
    := acc' (Var "l6").
  Definition r7_acc : acc (ary '{1} (ary '{40} (ary '{half (half (half (m)))} (ary '{half (half (half (m)))} num))))
    := acc' (Var "l7").
  Definition r8_acc : acc (ary '{1} (ary '{40} (ary '{half (half (half (m)))} (ary '{half (half (half (m)))} num))))
    := acc' (Var "l8").
  Definition r9_acc : acc (ary '{1} (ary '{80} (ary '{half (half (half (half (m))))} (ary '{half (half (half (half (m))))} num))))
    := acc' (Var "l9").
  Definition r10_acc : acc (ary '{1} (ary '{80} (ary '{half (half (half (half (m))))} (ary '{half (half (half (half (m))))} num))))
    := acc' (Var "l10").
  Definition r11_acc : acc (ary '{1} (ary '{80} (ary '{half (half (half (half (m))))} (ary '{half (half (half (half (m))))} num))))
    := acc' (Var "l11").
  Definition r12_acc : acc (ary '{1} (ary '{112} (ary '{half (half (half (half (m))))} (ary '{half (half (half (half (m))))} num))))
    := acc' (Var "l12").
  Definition r13_acc : acc (ary '{1} (ary '{112} (ary '{half (half (half (half (m))))} (ary '{half (half (half (half (m))))} num))))
    := acc' (Var "l13").
  Definition r14_acc : acc (ary '{1} (ary '{112} (ary '{half (half (half (half (m))))} (ary '{half (half (half (half (m))))} num))))
    := acc' (Var "l14").
  Definition r15_acc : acc (ary '{1} (ary '{192} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l15").
  Definition r16_acc : acc (ary '{1} (ary '{192} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l16").
  Definition r17_acc : acc (ary '{1} (ary '{192} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l17").
  Definition r18_acc : acc (ary '{1} (ary '{192} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l18").
  Definition r19_acc : acc (ary '{1} (ary '{320} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l19").
  Definition r20_acc : acc (ary '{1} (ary '{1280} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l20").
  Definition r21_acc : acc (ary '{1} (ary '{1280} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l21").
  Definition r22_acc : acc (ary '{1} (ary '{1280} (ary '{half (half (half (half (half (m)))))} (ary '{half (half (half (half (half (m)))))} num))))
    := acc' (Var "l22").
  Definition r23_acc : acc (ary '{1} (ary '{1280} num))
    := acc' (Var "l23").

  (* Freshness: all temporary buffers are undefined in the incoming
     environment and their paths do not overlap the final output.  The block
     temporaries bt1..bt9 and the SE temporaries sg1..sg4 are shared between
     blocks and are required to be fresh at every type. *)
  Definition efficientnetb0_fresh
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
    StructUndefined r18_acc rho /\
    StructUndefined r19_acc rho /\
    StructUndefined r20_acc rho /\
    StructUndefined r21_acc rho /\
    StructUndefined r22_acc rho /\
    StructUndefined r23_acc rho /\
    (forall d : data, StructUndefined (acc' (Var "bt1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt4") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt5") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt6") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt7") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt8") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "bt9") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "sg1") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "sg2") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "sg3") : acc d) rho) /\
    (forall d : data, StructUndefined (acc' (Var "sg4") : acc d) rho) /\
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
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt4") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt5") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt6") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt7") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt8") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "bt9") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "sg1") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "sg2") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "sg3") : acc d)) /\
    (forall (d : data) p, in_acc p output -> ~ in_acc p (acc' (Var "sg4") : acc d)).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma efficientnetb0_comm_eq_direct :
    forall (output : acc (ary '{1} (ary '{1000} num))),
    efficientnetb0_comm output = efficientnetb0_comm_direct output.
  Proof.
    intros.
    unfold efficientnetb0_comm, efficientnetb0_comm_direct, new.
    cbv beta.
    rewrite <- A_Conv4d_3x3_s2.
    rewrite <- eb_x1_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_BatchNorm4d.
    rewrite <- eb_x2_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Swish4d.
    rewrite <- eb_x3_body.
    rewrite bind_read_replace_seq.
    rewrite mbconv1_comm_eq_direct.
    rewrite mbconv1_direct_read.
    rewrite <- eb_x4_body.
    rewrite mbconve3s2_comm_eq_direct.
    rewrite mbconve3s2_direct_read.
    rewrite <- eb_x5_body.
    rewrite mbconve3s1r_comm_eq_direct.
    rewrite mbconve3s1r_direct_read.
    rewrite <- eb_x6_body.
    rewrite mbconve5s2_comm_eq_direct.
    rewrite mbconve5s2_direct_read.
    rewrite <- eb_x7_body.
    rewrite mbconve5s1r_comm_eq_direct.
    rewrite mbconve5s1r_direct_read.
    rewrite <- eb_x8_body.
    rewrite mbconve3s2_comm_eq_direct.
    rewrite mbconve3s2_direct_read.
    rewrite <- eb_x9_body.
    rewrite mbconve3s1r_comm_eq_direct.
    rewrite mbconve3s1r_direct_read.
    rewrite <- eb_x10_body.
    rewrite mbconve3s1r_comm_eq_direct.
    rewrite mbconve3s1r_direct_read.
    rewrite <- eb_x11_body.
    rewrite mbconve5s1_comm_eq_direct.
    rewrite mbconve5s1_direct_read.
    rewrite <- eb_x12_body.
    rewrite mbconve5s1r_comm_eq_direct.
    rewrite mbconve5s1r_direct_read.
    rewrite <- eb_x13_body.
    rewrite mbconve5s1r_comm_eq_direct.
    rewrite mbconve5s1r_direct_read.
    rewrite <- eb_x14_body.
    rewrite mbconve5s2_comm_eq_direct.
    rewrite mbconve5s2_direct_read.
    rewrite <- eb_x15_body.
    rewrite mbconve5s1r_comm_eq_direct.
    rewrite mbconve5s1r_direct_read.
    rewrite <- eb_x16_body.
    rewrite mbconve5s1r_comm_eq_direct.
    rewrite mbconve5s1r_direct_read.
    rewrite <- eb_x17_body.
    rewrite mbconve5s1r_comm_eq_direct.
    rewrite mbconve5s1r_direct_read.
    rewrite <- eb_x18_body.
    rewrite mbconve3s1_comm_eq_direct.
    rewrite mbconve3s1_direct_read.
    rewrite <- eb_x19_body.
    rewrite <- A_Conv4d_1x1_s1.
    rewrite <- eb_x20_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_BatchNorm4d.
    rewrite <- eb_x21_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Swish4d.
    rewrite <- eb_x22_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_GlobalAvgPool4d.
    rewrite <- eb_x23_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax2d.
    rewrite <- eb_x24_body.
    reflexivity.
  Qed.

  Lemma A_EfficientNetB0_direct :
    forall (output : acc (ary '{1} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    efficientnetb0_fresh output rho ->
    efficientnetb0_comm_direct output rho p = A(output, EfficientNetB0) rho p.
  Proof.
    intros.
    unfold efficientnetb0_comm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold EfficientNetB0. reflexivity.
  Qed.

  Theorem A_EfficientNetB0 :
    forall (output : acc (ary '{1} (ary '{1000} num)))
      (rho : env) (p : path),
    in_acc p output ->
    efficientnetb0_fresh output rho ->
    efficientnetb0_comm output rho p = A(output, EfficientNetB0) rho p.
  Proof.
    intros. rewrite efficientnetb0_comm_eq_direct.
    apply A_EfficientNetB0_direct; assumption.
  Qed.

End EfficientNetB0.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Swish4d.
Print Assumptions A_DWConv4d_5x5_s1.
Print Assumptions A_DWConv4d_5x5_s2.
Print Assumptions A_SEBlock.
Print Assumptions A_MBConv1.
Print Assumptions A_MBConvE3s2.
Print Assumptions A_MBConvE5s2.
Print Assumptions A_MBConvE3s1.
Print Assumptions A_MBConvE5s1.
Print Assumptions A_MBConvE3s1R.
Print Assumptions A_MBConvE5s1R.
Print Assumptions A_EfficientNetB0.
