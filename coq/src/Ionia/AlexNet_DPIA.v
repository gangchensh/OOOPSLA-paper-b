(* DPIA-style end-to-end Leibniz correctness proof for AlexNet (route A).

   Structure: classic AlexNet in 4d batched form
     conv1(11x11,p2,s4)-relu-pool(3x3,s2)
     conv2(5x5,p2,s1)-relu-pool(3x3,s2)
     conv3(3x3,p1,s1)-relu
     conv4(3x3,p1,s1)-relu
     conv5(3x3,p1,s1)-relu-pool(3x3,s2)
     flatten - fc1(4096)-relu - fc2(4096)-relu - fc3(1000) - softmax

   All operator equalities are reused as lemmas (rewrite only, no unfold of
   the operator bodies in the network-level proofs).  Two operators missing
   from the proved set are supplied here as trivial template lifts:
   [Flatten4d] (batch-preserving flatten, mirrors [Flatten3d]) and
   [Maxpool4d_pad] (batched [Maxpool3d_pad], covering the classic
   overlapping 3x3 stride-2 pooling). *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
Require Import Ionia.Ops_Conv.
Require Import Ionia.Ops_Elementwise.
Require Import Ionia.Ops_PoolPad.
Require Import Ionia.Ops_Reduce.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Flatten4d (batch dimension preserved)                                       *)
(* -------------------------------------------------------------------------- *)

Definition Flatten4d {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel * m1 * m2} num)) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun x : fin (channel * m1 * m2) =>
    idx (idx (idx (idx input b)
                 (fst (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
            (snd (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
        (snd (idx_1d_to_2d x)))).

Definition Flatten4d_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel * m1 * m2} num))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun x : fin (channel * m1 * m2) =>
    idxAcc (idxAcc output b) x |:=
      idx (idx (idx (idx input b)
                   (fst (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
              (snd (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
          (snd (idx_1d_to_2d x)))).

Lemma A_Flatten4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel * m1 * m2} num))),
  A(output, Flatten4d input) = Flatten4d_comm input output.
Proof.
  intros. unfold Flatten4d, Flatten4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro x.
  rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool4d_pad (batched Maxpool3d_pad; general kernel/stride/padding)        *)
(* -------------------------------------------------------------------------- *)

Definition Maxpool4d_pad {batch filernum m1 m2 : nat}
  (kersize stride padding : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum}
        (ary '{((m1 - kersize + 2*padding)/stride + 1)}
        (ary '{((m2 - kersize + 2*padding)/stride + 1)} num)))) :=
  tlet pad := Padding4d padding input in
  mkvSeq (fun b : fin batch =>
    mkvSeq (fun num : fin filernum =>
      mkvSeq (fun i0 : fin ((m1 - kersize + 2*padding)/stride + 1) =>
        mkvSeq (fun j0 : fin ((m2 - kersize + 2*padding)/stride + 1) =>
          max (mkvSeq (fun i1 : fin kersize => max (mkvSeq (fun j1 : fin kersize =>
            safe_idx_nat
              (safe_idx_nat (idx (idx pad b) num)
                            (fin2nat i0 * stride + fin2nat i1))
              (fin2nat j0 * stride + fin2nat j1))))))))).

Definition Maxpool4d_pad_comm {batch filernum m1 m2 : nat}
  (kersize stride padding : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
        (ary '{((m1 - kersize + 2*padding)/stride + 1)}
        (ary '{((m2 - kersize + 2*padding)/stride + 1)} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun num oc => mkvSeql (fun i0 o0 =>
    mkvSeql (fun j0 o1 =>
      maxl (mkvSeq (fun i1 : fin kersize => max (mkvSeq (fun j1 : fin kersize =>
        safe_idx_nat
          (safe_idx_nat (idx (idx (Padding4d padding input) b) num)
                        (fin2nat i0 * stride + fin2nat i1))
          (fin2nat j0 * stride + fin2nat j1)))))
           (fun r => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_Maxpool4d_pad : forall (batch filernum m1 m2 kersize stride padding : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
        (ary '{((m1 - kersize + 2*padding)/stride + 1)}
        (ary '{((m2 - kersize + 2*padding)/stride + 1)} num))))),
  A(output, Maxpool4d_pad kersize stride padding input)
  = Maxpool4d_pad_comm kersize stride padding input output.
Proof.
  intros. unfold Maxpool4d_pad, Maxpool4d_pad_comm, let_binding. cbv beta.
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
(* AlexNet layer sizes (symbolic in the input height/width)                    *)
(* -------------------------------------------------------------------------- *)

Definition c1o (m:nat) : nat := (m - 11 + 2 * 2) / 4 + 1.
Definition p1o (m:nat) : nat := (c1o m - 3 + 2 * 0) / 2 + 1.
Definition c2o (m:nat) : nat := (p1o m - 5 + 2 * 2) / 1 + 1.
Definition p2o (m:nat) : nat := (c2o m - 3 + 2 * 0) / 2 + 1.
Definition c3o (m:nat) : nat := (p2o m - 3 + 2 * 1) / 1 + 1.
Definition c4o (m:nat) : nat := (c3o m - 3 + 2 * 1) / 1 + 1.
Definition c5o (m:nat) : nat := (c4o m - 3 + 2 * 1) / 1 + 1.
Definition p5o (m:nat) : nat := (c5o m - 3 + 2 * 0) / 2 + 1.

(* -------------------------------------------------------------------------- *)
(* Functional AlexNet (R-version expression)                                   *)
(* -------------------------------------------------------------------------- *)

Definition AlexNet {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (c1_w : exp (ary '{64} (ary '{channel} (ary '{11} (ary '{11} num)))))
  (c1_b : exp (ary '{64} num))
  (c2_w : exp (ary '{192} (ary '{64} (ary '{5} (ary '{5} num)))))
  (c2_b : exp (ary '{192} num))
  (c3_w : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
  (c3_b : exp (ary '{384} num))
  (c4_w : exp (ary '{256} (ary '{384} (ary '{3} (ary '{3} num)))))
  (c4_b : exp (ary '{256} num))
  (c5_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c5_b : exp (ary '{256} num))
  (f1_w : exp (ary '{4096} (ary '{256 * p5o m1 * p5o m2} num)))
  (f1_b : exp (ary '{4096} num))
  (f2_w : exp (ary '{4096} (ary '{4096} num)))
  (f2_b : exp (ary '{4096} num))
  (f3_w : exp (ary '{1000} (ary '{4096} num)))
  (f3_b : exp (ary '{1000} num))
  : exp (ary '{batch} (ary '{1000} num)) :=
  let l1 := ReLU4d (Conv4d 2 4 c1_b c1_w input) in
  let l2 := Maxpool4d_pad 3 2 0 l1 in
  let l3 := ReLU4d (Conv4d 2 1 c2_b c2_w l2) in
  let l4 := Maxpool4d_pad 3 2 0 l3 in
  let l5 := ReLU4d (Conv4d 1 1 c3_b c3_w l4) in
  let l6 := ReLU4d (Conv4d 1 1 c4_b c4_w l5) in
  let l7 := ReLU4d (Conv4d 1 1 c5_b c5_w l6) in
  let l8 := Maxpool4d_pad 3 2 0 l7 in
  let l9 := Flatten4d l8 in
  let l10 := ReLU2d (Linear2d f1_w f1_b l9) in
  let l11 := ReLU2d (Linear2d f2_w f2_b l10) in
  Softmax2d (Linear2d f3_w f3_b l11).

(* -------------------------------------------------------------------------- *)
(* Imperative AlexNet (combinators; buffers l1..l11 + output)                  *)
(* -------------------------------------------------------------------------- *)

Definition alexnet_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (c1_w : exp (ary '{64} (ary '{channel} (ary '{11} (ary '{11} num)))))
  (c1_b : exp (ary '{64} num))
  (c2_w : exp (ary '{192} (ary '{64} (ary '{5} (ary '{5} num)))))
  (c2_b : exp (ary '{192} num))
  (c3_w : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
  (c3_b : exp (ary '{384} num))
  (c4_w : exp (ary '{256} (ary '{384} (ary '{3} (ary '{3} num)))))
  (c4_b : exp (ary '{256} num))
  (c5_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c5_b : exp (ary '{256} num))
  (f1_w : exp (ary '{4096} (ary '{256 * p5o m1 * p5o m2} num)))
  (f1_b : exp (ary '{4096} num))
  (f2_w : exp (ary '{4096} (ary '{4096} num)))
  (f2_b : exp (ary '{4096} num))
  (f3_w : exp (ary '{1000} (ary '{4096} num)))
  (f3_b : exp (ary '{1000} num))
  (output : acc (ary '{batch} (ary '{1000} num)))
  : comm :=
  new (fun l1 =>
    seq (ReLU4d_comm (Conv4d 2 4 c1_b c1_w input) l1)
      (new (fun l2 =>
        seq (bind_read l1 (fun e => Maxpool4d_pad_comm 3 2 0 e l2))
          (new (fun l3 =>
            seq (bind_read l2 (fun e => ReLU4d_comm (Conv4d 2 1 c2_b c2_w e) l3))
              (new (fun l4 =>
                seq (bind_read l3 (fun e => Maxpool4d_pad_comm 3 2 0 e l4))
                  (new (fun l5 =>
                    seq (bind_read l4 (fun e => ReLU4d_comm (Conv4d 1 1 c3_b c3_w e) l5))
                      (new (fun l6 =>
                        seq (bind_read l5 (fun e => ReLU4d_comm (Conv4d 1 1 c4_b c4_w e) l6))
                          (new (fun l7 =>
                            seq (bind_read l6 (fun e => ReLU4d_comm (Conv4d 1 1 c5_b c5_w e) l7))
                              (new (fun l8 =>
                                seq (bind_read l7 (fun e => Maxpool4d_pad_comm 3 2 0 e l8))
                                  (new (fun l9 =>
                                    seq (bind_read l8 (fun e => Flatten4d_comm e l9))
                                      (new (fun l10 =>
                                        seq (bind_read l9 (fun e =>
                                              ReLU2d_comm (Linear2d f1_w f1_b e) l10))
                                          (new (fun l11 =>
                                            seq (bind_read l10 (fun e =>
                                                  ReLU2d_comm (Linear2d f2_w f2_b e) l11))
                                              (bind_read l11 (fun e =>
                                                Softmax2d_comm (Linear2d f3_w f3_b e) output)))
                                            (acc' (Var "l11")))
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

(* -------------------------------------------------------------------------- *)
(* End-to-end AlexNet statement                                                *)
(* -------------------------------------------------------------------------- *)

(* Intermediate accumulator paths used by [alexnet_comm]. *)
Section Freshness.
  Context {batch channel m1 m2 : nat}.

  Definition a1_acc : acc (ary '{batch} (ary '{64} (ary '{c1o m1} (ary '{c1o m2} num))))
    := acc' (Var "l1").
  Definition a2_acc : acc (ary '{batch} (ary '{64} (ary '{p1o m1} (ary '{p1o m2} num))))
    := acc' (Var "l2").
  Definition a3_acc : acc (ary '{batch} (ary '{192} (ary '{c2o m1} (ary '{c2o m2} num))))
    := acc' (Var "l3").
  Definition a4_acc : acc (ary '{batch} (ary '{192} (ary '{p2o m1} (ary '{p2o m2} num))))
    := acc' (Var "l4").
  Definition a5_acc : acc (ary '{batch} (ary '{384} (ary '{c3o m1} (ary '{c3o m2} num))))
    := acc' (Var "l5").
  Definition a6_acc : acc (ary '{batch} (ary '{256} (ary '{c4o m1} (ary '{c4o m2} num))))
    := acc' (Var "l6").
  Definition a7_acc : acc (ary '{batch} (ary '{256} (ary '{c5o m1} (ary '{c5o m2} num))))
    := acc' (Var "l7").
  Definition a8_acc : acc (ary '{batch} (ary '{256} (ary '{p5o m1} (ary '{p5o m2} num))))
    := acc' (Var "l8").
  Definition a9_acc : acc (ary '{batch} (ary '{256 * p5o m1 * p5o m2} num))
    := acc' (Var "l9").
  Definition a10_acc : acc (ary '{batch} (ary '{4096} num)) := acc' (Var "l10").
  Definition a11_acc : acc (ary '{batch} (ary '{4096} num)) := acc' (Var "l11").

  (* Freshness: all temporary buffers are undefined in the incoming environment
     and their paths do not overlap the final output accumulator. *)
  Definition alexnet_fresh
    (output : acc (ary '{batch} (ary '{1000} num))) (rho : env) : Prop :=
    StructUndefined a1_acc rho /\
    StructUndefined a2_acc rho /\
    StructUndefined a3_acc rho /\
    StructUndefined a4_acc rho /\
    StructUndefined a5_acc rho /\
    StructUndefined a6_acc rho /\
    StructUndefined a7_acc rho /\
    StructUndefined a8_acc rho /\
    StructUndefined a9_acc rho /\
    StructUndefined a10_acc rho /\
    StructUndefined a11_acc rho /\
    (forall p, in_acc p output -> ~ in_acc p a1_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a2_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a3_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a4_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a5_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a6_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a7_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a8_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a9_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a10_acc) /\
    (forall p, in_acc p output -> ~ in_acc p a11_acc).
End Freshness.

(* Direct imperative program: every [bind_read] is replaced by the functional
   value of the previous layer (DPIA-normal form of [alexnet_comm]). *)
Definition alexnet_comm_direct {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (c1_w : exp (ary '{64} (ary '{channel} (ary '{11} (ary '{11} num)))))
  (c1_b : exp (ary '{64} num))
  (c2_w : exp (ary '{192} (ary '{64} (ary '{5} (ary '{5} num)))))
  (c2_b : exp (ary '{192} num))
  (c3_w : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
  (c3_b : exp (ary '{384} num))
  (c4_w : exp (ary '{256} (ary '{384} (ary '{3} (ary '{3} num)))))
  (c4_b : exp (ary '{256} num))
  (c5_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c5_b : exp (ary '{256} num))
  (f1_w : exp (ary '{4096} (ary '{256 * p5o m1 * p5o m2} num)))
  (f1_b : exp (ary '{4096} num))
  (f2_w : exp (ary '{4096} (ary '{4096} num)))
  (f2_b : exp (ary '{4096} num))
  (f3_w : exp (ary '{1000} (ary '{4096} num)))
  (f3_b : exp (ary '{1000} num))
  (output : acc (ary '{batch} (ary '{1000} num)))
  : comm :=
  let l1_e := ReLU4d (Conv4d 2 4 c1_b c1_w input) in
  let l2_e := Maxpool4d_pad 3 2 0 l1_e in
  let l3_e := ReLU4d (Conv4d 2 1 c2_b c2_w l2_e) in
  let l4_e := Maxpool4d_pad 3 2 0 l3_e in
  let l5_e := ReLU4d (Conv4d 1 1 c3_b c3_w l4_e) in
  let l6_e := ReLU4d (Conv4d 1 1 c4_b c4_w l5_e) in
  let l7_e := ReLU4d (Conv4d 1 1 c5_b c5_w l6_e) in
  let l8_e := Maxpool4d_pad 3 2 0 l7_e in
  let l9_e := Flatten4d l8_e in
  let l10_e := ReLU2d (Linear2d f1_w f1_b l9_e) in
  let l11_e := ReLU2d (Linear2d f2_w f2_b l10_e) in
  let out_e := Softmax2d (Linear2d f3_w f3_b l11_e) in
  new (fun l1a =>
    seq (A(l1a, l1_e))
      (new (fun l2a =>
        seq (A(l2a, l2_e))
          (new (fun l3a =>
            seq (A(l3a, l3_e))
              (new (fun l4a =>
                seq (A(l4a, l4_e))
                  (new (fun l5a =>
                    seq (A(l5a, l5_e))
                      (new (fun l6a =>
                        seq (A(l6a, l6_e))
                          (new (fun l7a =>
                            seq (A(l7a, l7_e))
                              (new (fun l8a =>
                                seq (A(l8a, l8_e))
                                  (new (fun l9a =>
                                    seq (A(l9a, l9_e))
                                      (new (fun l10a =>
                                        seq (A(l10a, l10_e))
                                          (new (fun l11a =>
                                            seq (A(l11a, l11_e))
                                              (A(output, out_e)))
                                            (acc' (Var "l11")))
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

Lemma A_AlexNet_direct :
  forall (batch channel m1 m2 : nat)
    (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
    (c1_w : exp (ary '{64} (ary '{channel} (ary '{11} (ary '{11} num)))))
    (c1_b : exp (ary '{64} num))
    (c2_w : exp (ary '{192} (ary '{64} (ary '{5} (ary '{5} num)))))
    (c2_b : exp (ary '{192} num))
    (c3_w : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
    (c3_b : exp (ary '{384} num))
    (c4_w : exp (ary '{256} (ary '{384} (ary '{3} (ary '{3} num)))))
    (c4_b : exp (ary '{256} num))
    (c5_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c5_b : exp (ary '{256} num))
    (f1_w : exp (ary '{4096} (ary '{256 * p5o m1 * p5o m2} num)))
    (f1_b : exp (ary '{4096} num))
    (f2_w : exp (ary '{4096} (ary '{4096} num)))
    (f2_b : exp (ary '{4096} num))
    (f3_w : exp (ary '{1000} (ary '{4096} num)))
    (f3_b : exp (ary '{1000} num))
    (output : acc (ary '{batch} (ary '{1000} num)))
    (rho : env) (p : path),
  in_acc p output ->
  @alexnet_fresh batch m1 m2 output rho ->
  alexnet_comm_direct input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b
    f1_w f1_b f2_w f2_b f3_w f3_b output rho p =
  A(output, AlexNet input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b
    f1_w f1_b f2_w f2_b f3_w f3_b) rho p.
Proof.
  intros. unfold alexnet_comm_direct, AlexNet, new, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* The original [alexnet_comm] and the direct form are equal as commands. *)
Lemma alexnet_comm_eq_direct :
  forall (batch channel m1 m2 : nat)
    (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
    (c1_w : exp (ary '{64} (ary '{channel} (ary '{11} (ary '{11} num)))))
    (c1_b : exp (ary '{64} num))
    (c2_w : exp (ary '{192} (ary '{64} (ary '{5} (ary '{5} num)))))
    (c2_b : exp (ary '{192} num))
    (c3_w : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
    (c3_b : exp (ary '{384} num))
    (c4_w : exp (ary '{256} (ary '{384} (ary '{3} (ary '{3} num)))))
    (c4_b : exp (ary '{256} num))
    (c5_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c5_b : exp (ary '{256} num))
    (f1_w : exp (ary '{4096} (ary '{256 * p5o m1 * p5o m2} num)))
    (f1_b : exp (ary '{4096} num))
    (f2_w : exp (ary '{4096} (ary '{4096} num)))
    (f2_b : exp (ary '{4096} num))
    (f3_w : exp (ary '{1000} (ary '{4096} num)))
    (f3_b : exp (ary '{1000} num))
    (output : acc (ary '{batch} (ary '{1000} num))),
  alexnet_comm input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b
    f1_w f1_b f2_w f2_b f3_w f3_b output =
  alexnet_comm_direct input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b
    f1_w f1_b f2_w f2_b f3_w f3_b output.
Proof.
  intros.
  unfold alexnet_comm, alexnet_comm_direct, new.
  cbv zeta beta.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d_pad.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d_pad.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d_pad.
  rewrite bind_read_replace_seq.
  rewrite <- A_Flatten4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU2d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU2d.
  rewrite bind_read_replace.
  rewrite <- A_Softmax2d.
  all: try lia.
  reflexivity.
Qed.

Theorem A_AlexNet :
  forall (batch channel m1 m2 : nat)
    (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
    (c1_w : exp (ary '{64} (ary '{channel} (ary '{11} (ary '{11} num)))))
    (c1_b : exp (ary '{64} num))
    (c2_w : exp (ary '{192} (ary '{64} (ary '{5} (ary '{5} num)))))
    (c2_b : exp (ary '{192} num))
    (c3_w : exp (ary '{384} (ary '{192} (ary '{3} (ary '{3} num)))))
    (c3_b : exp (ary '{384} num))
    (c4_w : exp (ary '{256} (ary '{384} (ary '{3} (ary '{3} num)))))
    (c4_b : exp (ary '{256} num))
    (c5_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c5_b : exp (ary '{256} num))
    (f1_w : exp (ary '{4096} (ary '{256 * p5o m1 * p5o m2} num)))
    (f1_b : exp (ary '{4096} num))
    (f2_w : exp (ary '{4096} (ary '{4096} num)))
    (f2_b : exp (ary '{4096} num))
    (f3_w : exp (ary '{1000} (ary '{4096} num)))
    (f3_b : exp (ary '{1000} num))
    (output : acc (ary '{batch} (ary '{1000} num)))
    (rho : env) (p : path),
  in_acc p output ->
  @alexnet_fresh batch m1 m2 output rho ->
  alexnet_comm input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b
    f1_w f1_b f2_w f2_b f3_w f3_b output rho p =
  A(output, AlexNet input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b
    f1_w f1_b f2_w f2_b f3_w f3_b) rho p.
Proof.
  intros. rewrite alexnet_comm_eq_direct. apply A_AlexNet_direct; assumption.
Qed.
