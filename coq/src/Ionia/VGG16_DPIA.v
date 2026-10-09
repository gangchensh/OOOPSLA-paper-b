(* DPIA-style end-to-end Leibniz correctness proof for VGG16 (route A).

   Structure: classic VGG16 in 4d batched form
     conv3x3(s1,p1) x13 with channels 64-64-POOL-128-128-POOL-256-256-256-POOL
       -512-512-512-POOL-512-512-512-POOL (2x2 stride-2 max pooling)
     flatten - fc1(4096)-relu - fc2(4096)-relu - fc3(1000) - softmax

   Every conv block is fused with its ReLU into a single buffer, exactly as in
   [AlexNet_DPIA.v]; all operator equalities are reused as lemmas (rewrite
   only, no unfold of operator bodies in the network-level proofs).  Feature
   map sizes stay symbolic in the input height/width; channel counts are
   concrete naturals. *)

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
Require Import Ionia.AlexNet_DPIA.
From Stdlib Require Import Lia.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* VGG16 layer sizes (symbolic in the input height/width)                      *)
(* -------------------------------------------------------------------------- *)

(* conv3x3, stride 1, padding 1: output size formula of [Conv4d]. *)
Definition vco (m : nat) : nat := (m - 3 + 2 * 1) / 1 + 1.
(* 2x2 max pooling, stride 2: output size formula of [Maxpool4d]. *)
Definition vpo (m : nat) : nat := m / 2.

Definition s01 (m : nat) : nat := vco m.
Definition s02 (m : nat) : nat := vco (s01 m).
Definition s03 (m : nat) : nat := vpo (s02 m).
Definition s04 (m : nat) : nat := vco (s03 m).
Definition s05 (m : nat) : nat := vco (s04 m).
Definition s06 (m : nat) : nat := vpo (s05 m).
Definition s07 (m : nat) : nat := vco (s06 m).
Definition s08 (m : nat) : nat := vco (s07 m).
Definition s09 (m : nat) : nat := vco (s08 m).
Definition s10 (m : nat) : nat := vpo (s09 m).
Definition s11 (m : nat) : nat := vco (s10 m).
Definition s12 (m : nat) : nat := vco (s11 m).
Definition s13 (m : nat) : nat := vco (s12 m).
Definition s14 (m : nat) : nat := vpo (s13 m).
Definition s15 (m : nat) : nat := vco (s14 m).
Definition s16 (m : nat) : nat := vco (s15 m).
Definition s17 (m : nat) : nat := vco (s16 m).
Definition s18 (m : nat) : nat := vpo (s17 m).

(* -------------------------------------------------------------------------- *)
(* Functional VGG16 (R-version expression)                                     *)
(* -------------------------------------------------------------------------- *)

Definition VGG16 {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (c1_w : exp (ary '{64} (ary '{channel} (ary '{3} (ary '{3} num)))))
  (c1_b : exp (ary '{64} num))
  (c2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
  (c2_b : exp (ary '{64} num))
  (c3_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
  (c3_b : exp (ary '{128} num))
  (c4_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
  (c4_b : exp (ary '{128} num))
  (c5_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
  (c5_b : exp (ary '{256} num))
  (c6_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c6_b : exp (ary '{256} num))
  (c7_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c7_b : exp (ary '{256} num))
  (c8_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c8_b : exp (ary '{512} num))
  (c9_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c9_b : exp (ary '{512} num))
  (c10_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c10_b : exp (ary '{512} num))
  (c11_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c11_b : exp (ary '{512} num))
  (c12_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c12_b : exp (ary '{512} num))
  (c13_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c13_b : exp (ary '{512} num))
  (f1_w : exp (ary '{4096} (ary '{512 * s18 m1 * s18 m2} num)))
  (f1_b : exp (ary '{4096} num))
  (f2_w : exp (ary '{4096} (ary '{4096} num)))
  (f2_b : exp (ary '{4096} num))
  (f3_w : exp (ary '{1000} (ary '{4096} num)))
  (f3_b : exp (ary '{1000} num))
  : exp (ary '{batch} (ary '{1000} num)) :=
  let l1 := ReLU4d (Conv4d 1 1 c1_b c1_w input) in
  let l2 := ReLU4d (Conv4d 1 1 c2_b c2_w l1) in
  let l3 := Maxpool4d 2 l2 in
  let l4 := ReLU4d (Conv4d 1 1 c3_b c3_w l3) in
  let l5 := ReLU4d (Conv4d 1 1 c4_b c4_w l4) in
  let l6 := Maxpool4d 2 l5 in
  let l7 := ReLU4d (Conv4d 1 1 c5_b c5_w l6) in
  let l8 := ReLU4d (Conv4d 1 1 c6_b c6_w l7) in
  let l9 := ReLU4d (Conv4d 1 1 c7_b c7_w l8) in
  let l10 := Maxpool4d 2 l9 in
  let l11 := ReLU4d (Conv4d 1 1 c8_b c8_w l10) in
  let l12 := ReLU4d (Conv4d 1 1 c9_b c9_w l11) in
  let l13 := ReLU4d (Conv4d 1 1 c10_b c10_w l12) in
  let l14 := Maxpool4d 2 l13 in
  let l15 := ReLU4d (Conv4d 1 1 c11_b c11_w l14) in
  let l16 := ReLU4d (Conv4d 1 1 c12_b c12_w l15) in
  let l17 := ReLU4d (Conv4d 1 1 c13_b c13_w l16) in
  let l18 := Maxpool4d 2 l17 in
  let l19 := Flatten4d l18 in
  let l20 := ReLU2d (Linear2d f1_w f1_b l19) in
  let l21 := ReLU2d (Linear2d f2_w f2_b l20) in
  Softmax2d (Linear2d f3_w f3_b l21).

(* -------------------------------------------------------------------------- *)
(* Imperative VGG16 (combinators; buffers l1..l21 + output)                    *)
(* -------------------------------------------------------------------------- *)

Definition vgg16_comm {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (c1_w : exp (ary '{64} (ary '{channel} (ary '{3} (ary '{3} num)))))
  (c1_b : exp (ary '{64} num))
  (c2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
  (c2_b : exp (ary '{64} num))
  (c3_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
  (c3_b : exp (ary '{128} num))
  (c4_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
  (c4_b : exp (ary '{128} num))
  (c5_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
  (c5_b : exp (ary '{256} num))
  (c6_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c6_b : exp (ary '{256} num))
  (c7_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c7_b : exp (ary '{256} num))
  (c8_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c8_b : exp (ary '{512} num))
  (c9_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c9_b : exp (ary '{512} num))
  (c10_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c10_b : exp (ary '{512} num))
  (c11_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c11_b : exp (ary '{512} num))
  (c12_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c12_b : exp (ary '{512} num))
  (c13_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c13_b : exp (ary '{512} num))
  (f1_w : exp (ary '{4096} (ary '{512 * s18 m1 * s18 m2} num)))
  (f1_b : exp (ary '{4096} num))
  (f2_w : exp (ary '{4096} (ary '{4096} num)))
  (f2_b : exp (ary '{4096} num))
  (f3_w : exp (ary '{1000} (ary '{4096} num)))
  (f3_b : exp (ary '{1000} num))
  (output : acc (ary '{batch} (ary '{1000} num)))
  : comm :=
  new (fun l1 =>
    seq (ReLU4d_comm (Conv4d 1 1 c1_b c1_w input) l1)
      (new (fun l2 =>
        seq (bind_read l1 (fun e => ReLU4d_comm (Conv4d 1 1 c2_b c2_w e) l2))
        (new (fun l3 =>
          seq (bind_read l2 (fun e => Maxpool4d_comm 2 e l3))
          (new (fun l4 =>
            seq (bind_read l3 (fun e => ReLU4d_comm (Conv4d 1 1 c3_b c3_w e) l4))
            (new (fun l5 =>
              seq (bind_read l4 (fun e => ReLU4d_comm (Conv4d 1 1 c4_b c4_w e) l5))
              (new (fun l6 =>
                seq (bind_read l5 (fun e => Maxpool4d_comm 2 e l6))
                (new (fun l7 =>
                  seq (bind_read l6 (fun e => ReLU4d_comm (Conv4d 1 1 c5_b c5_w e) l7))
                  (new (fun l8 =>
                    seq (bind_read l7 (fun e => ReLU4d_comm (Conv4d 1 1 c6_b c6_w e) l8))
                    (new (fun l9 =>
                      seq (bind_read l8 (fun e => ReLU4d_comm (Conv4d 1 1 c7_b c7_w e) l9))
                      (new (fun l10 =>
                        seq (bind_read l9 (fun e => Maxpool4d_comm 2 e l10))
                        (new (fun l11 =>
                          seq (bind_read l10 (fun e => ReLU4d_comm (Conv4d 1 1 c8_b c8_w e) l11))
                          (new (fun l12 =>
                            seq (bind_read l11 (fun e => ReLU4d_comm (Conv4d 1 1 c9_b c9_w e) l12))
                            (new (fun l13 =>
                              seq (bind_read l12 (fun e => ReLU4d_comm (Conv4d 1 1 c10_b c10_w e) l13))
                              (new (fun l14 =>
                                seq (bind_read l13 (fun e => Maxpool4d_comm 2 e l14))
                                (new (fun l15 =>
                                  seq (bind_read l14 (fun e => ReLU4d_comm (Conv4d 1 1 c11_b c11_w e) l15))
                                  (new (fun l16 =>
                                    seq (bind_read l15 (fun e => ReLU4d_comm (Conv4d 1 1 c12_b c12_w e) l16))
                                    (new (fun l17 =>
                                      seq (bind_read l16 (fun e => ReLU4d_comm (Conv4d 1 1 c13_b c13_w e) l17))
                                      (new (fun l18 =>
                                        seq (bind_read l17 (fun e => Maxpool4d_comm 2 e l18))
                                        (new (fun l19 =>
                                          seq (bind_read l18 (fun e => Flatten4d_comm e l19))
                                          (new (fun l20 =>
                                            seq (bind_read l19 (fun e => ReLU2d_comm (Linear2d f1_w f1_b e) l20))
                                            (new (fun l21 =>
                                              seq (bind_read l20 (fun e => ReLU2d_comm (Linear2d f2_w f2_b e) l21))
                                                (bind_read l21 (fun e => Softmax2d_comm (Linear2d f3_w f3_b e) output))
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

(* -------------------------------------------------------------------------- *)
(* End-to-end VGG16 statement                                                  *)
(* -------------------------------------------------------------------------- *)

(* Intermediate accumulator paths used by [vgg16_comm]. *)
Section Freshness.
  Context {batch channel m1 m2 : nat}.

  Definition v1_acc : acc (ary '{batch} (ary '{64} (ary '{s01 m1} (ary '{s01 m2} num))))
    := acc' (Var "l1").
  Definition v2_acc : acc (ary '{batch} (ary '{64} (ary '{s02 m1} (ary '{s02 m2} num))))
    := acc' (Var "l2").
  Definition v3_acc : acc (ary '{batch} (ary '{64} (ary '{s03 m1} (ary '{s03 m2} num))))
    := acc' (Var "l3").
  Definition v4_acc : acc (ary '{batch} (ary '{128} (ary '{s04 m1} (ary '{s04 m2} num))))
    := acc' (Var "l4").
  Definition v5_acc : acc (ary '{batch} (ary '{128} (ary '{s05 m1} (ary '{s05 m2} num))))
    := acc' (Var "l5").
  Definition v6_acc : acc (ary '{batch} (ary '{128} (ary '{s06 m1} (ary '{s06 m2} num))))
    := acc' (Var "l6").
  Definition v7_acc : acc (ary '{batch} (ary '{256} (ary '{s07 m1} (ary '{s07 m2} num))))
    := acc' (Var "l7").
  Definition v8_acc : acc (ary '{batch} (ary '{256} (ary '{s08 m1} (ary '{s08 m2} num))))
    := acc' (Var "l8").
  Definition v9_acc : acc (ary '{batch} (ary '{256} (ary '{s09 m1} (ary '{s09 m2} num))))
    := acc' (Var "l9").
  Definition v10_acc : acc (ary '{batch} (ary '{256} (ary '{s10 m1} (ary '{s10 m2} num))))
    := acc' (Var "l10").
  Definition v11_acc : acc (ary '{batch} (ary '{512} (ary '{s11 m1} (ary '{s11 m2} num))))
    := acc' (Var "l11").
  Definition v12_acc : acc (ary '{batch} (ary '{512} (ary '{s12 m1} (ary '{s12 m2} num))))
    := acc' (Var "l12").
  Definition v13_acc : acc (ary '{batch} (ary '{512} (ary '{s13 m1} (ary '{s13 m2} num))))
    := acc' (Var "l13").
  Definition v14_acc : acc (ary '{batch} (ary '{512} (ary '{s14 m1} (ary '{s14 m2} num))))
    := acc' (Var "l14").
  Definition v15_acc : acc (ary '{batch} (ary '{512} (ary '{s15 m1} (ary '{s15 m2} num))))
    := acc' (Var "l15").
  Definition v16_acc : acc (ary '{batch} (ary '{512} (ary '{s16 m1} (ary '{s16 m2} num))))
    := acc' (Var "l16").
  Definition v17_acc : acc (ary '{batch} (ary '{512} (ary '{s17 m1} (ary '{s17 m2} num))))
    := acc' (Var "l17").
  Definition v18_acc : acc (ary '{batch} (ary '{512} (ary '{s18 m1} (ary '{s18 m2} num))))
    := acc' (Var "l18").
  Definition v19_acc : acc (ary '{batch} (ary '{512 * s18 m1 * s18 m2} num))
    := acc' (Var "l19").
  Definition v20_acc : acc (ary '{batch} (ary '{4096} num))
    := acc' (Var "l20").
  Definition v21_acc : acc (ary '{batch} (ary '{4096} num))
    := acc' (Var "l21").

  (* Freshness: all temporary buffers are undefined in the incoming environment
     and their paths do not overlap the final output accumulator. *)
  Definition vgg16_fresh
    (output : acc (ary '{batch} (ary '{1000} num))) (rho : env) : Prop :=
    StructUndefined v1_acc rho
    /\
    StructUndefined v2_acc rho
    /\
    StructUndefined v3_acc rho
    /\
    StructUndefined v4_acc rho
    /\
    StructUndefined v5_acc rho
    /\
    StructUndefined v6_acc rho
    /\
    StructUndefined v7_acc rho
    /\
    StructUndefined v8_acc rho
    /\
    StructUndefined v9_acc rho
    /\
    StructUndefined v10_acc rho
    /\
    StructUndefined v11_acc rho
    /\
    StructUndefined v12_acc rho
    /\
    StructUndefined v13_acc rho
    /\
    StructUndefined v14_acc rho
    /\
    StructUndefined v15_acc rho
    /\
    StructUndefined v16_acc rho
    /\
    StructUndefined v17_acc rho
    /\
    StructUndefined v18_acc rho
    /\
    StructUndefined v19_acc rho
    /\
    StructUndefined v20_acc rho
    /\
    StructUndefined v21_acc rho
    /\
    (forall p, in_acc p output -> ~ in_acc p v1_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v2_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v3_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v4_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v5_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v6_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v7_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v8_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v9_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v10_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v11_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v12_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v13_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v14_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v15_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v16_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v17_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v18_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v19_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v20_acc)
    /\
    (forall p, in_acc p output -> ~ in_acc p v21_acc).
End Freshness.

(* Direct imperative program: every [bind_read] is replaced by the functional
   value of the previous layer (DPIA-normal form of [vgg16_comm]). *)
Definition vgg16_comm_direct {batch channel m1 m2 : nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (c1_w : exp (ary '{64} (ary '{channel} (ary '{3} (ary '{3} num)))))
  (c1_b : exp (ary '{64} num))
  (c2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
  (c2_b : exp (ary '{64} num))
  (c3_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
  (c3_b : exp (ary '{128} num))
  (c4_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
  (c4_b : exp (ary '{128} num))
  (c5_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
  (c5_b : exp (ary '{256} num))
  (c6_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c6_b : exp (ary '{256} num))
  (c7_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c7_b : exp (ary '{256} num))
  (c8_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
  (c8_b : exp (ary '{512} num))
  (c9_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c9_b : exp (ary '{512} num))
  (c10_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c10_b : exp (ary '{512} num))
  (c11_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c11_b : exp (ary '{512} num))
  (c12_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c12_b : exp (ary '{512} num))
  (c13_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
  (c13_b : exp (ary '{512} num))
  (f1_w : exp (ary '{4096} (ary '{512 * s18 m1 * s18 m2} num)))
  (f1_b : exp (ary '{4096} num))
  (f2_w : exp (ary '{4096} (ary '{4096} num)))
  (f2_b : exp (ary '{4096} num))
  (f3_w : exp (ary '{1000} (ary '{4096} num)))
  (f3_b : exp (ary '{1000} num))
  (output : acc (ary '{batch} (ary '{1000} num)))
  : comm :=
  let l1_e := ReLU4d (Conv4d 1 1 c1_b c1_w input) in
  let l2_e := ReLU4d (Conv4d 1 1 c2_b c2_w l1_e) in
  let l3_e := Maxpool4d 2 l2_e in
  let l4_e := ReLU4d (Conv4d 1 1 c3_b c3_w l3_e) in
  let l5_e := ReLU4d (Conv4d 1 1 c4_b c4_w l4_e) in
  let l6_e := Maxpool4d 2 l5_e in
  let l7_e := ReLU4d (Conv4d 1 1 c5_b c5_w l6_e) in
  let l8_e := ReLU4d (Conv4d 1 1 c6_b c6_w l7_e) in
  let l9_e := ReLU4d (Conv4d 1 1 c7_b c7_w l8_e) in
  let l10_e := Maxpool4d 2 l9_e in
  let l11_e := ReLU4d (Conv4d 1 1 c8_b c8_w l10_e) in
  let l12_e := ReLU4d (Conv4d 1 1 c9_b c9_w l11_e) in
  let l13_e := ReLU4d (Conv4d 1 1 c10_b c10_w l12_e) in
  let l14_e := Maxpool4d 2 l13_e in
  let l15_e := ReLU4d (Conv4d 1 1 c11_b c11_w l14_e) in
  let l16_e := ReLU4d (Conv4d 1 1 c12_b c12_w l15_e) in
  let l17_e := ReLU4d (Conv4d 1 1 c13_b c13_w l16_e) in
  let l18_e := Maxpool4d 2 l17_e in
  let l19_e := Flatten4d l18_e in
  let l20_e := ReLU2d (Linear2d f1_w f1_b l19_e) in
  let l21_e := ReLU2d (Linear2d f2_w f2_b l20_e) in
  let out_e := Softmax2d (Linear2d f3_w f3_b l21_e) in
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
                          (new (fun l12a =>
                            seq (A(l12a, l12_e))
                            (new (fun l13a =>
                              seq (A(l13a, l13_e))
                              (new (fun l14a =>
                                seq (A(l14a, l14_e))
                                (new (fun l15a =>
                                  seq (A(l15a, l15_e))
                                  (new (fun l16a =>
                                    seq (A(l16a, l16_e))
                                    (new (fun l17a =>
                                      seq (A(l17a, l17_e))
                                      (new (fun l18a =>
                                        seq (A(l18a, l18_e))
                                        (new (fun l19a =>
                                          seq (A(l19a, l19_e))
                                          (new (fun l20a =>
                                            seq (A(l20a, l20_e))
                                            (new (fun l21a =>
                                              seq (A(l21a, l21_e))
                                                (A(output, out_e))
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

Lemma A_VGG16_direct :
  forall (batch channel m1 m2 : nat)
    (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
    (c1_w : exp (ary '{64} (ary '{channel} (ary '{3} (ary '{3} num)))))
    (c1_b : exp (ary '{64} num))
    (c2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
    (c2_b : exp (ary '{64} num))
    (c3_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
    (c3_b : exp (ary '{128} num))
    (c4_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
    (c4_b : exp (ary '{128} num))
    (c5_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
    (c5_b : exp (ary '{256} num))
    (c6_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c6_b : exp (ary '{256} num))
    (c7_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c7_b : exp (ary '{256} num))
    (c8_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c8_b : exp (ary '{512} num))
    (c9_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c9_b : exp (ary '{512} num))
    (c10_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c10_b : exp (ary '{512} num))
    (c11_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c11_b : exp (ary '{512} num))
    (c12_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c12_b : exp (ary '{512} num))
    (c13_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c13_b : exp (ary '{512} num))
    (f1_w : exp (ary '{4096} (ary '{512 * s18 m1 * s18 m2} num)))
    (f1_b : exp (ary '{4096} num))
    (f2_w : exp (ary '{4096} (ary '{4096} num)))
    (f2_b : exp (ary '{4096} num))
    (f3_w : exp (ary '{1000} (ary '{4096} num)))
    (f3_b : exp (ary '{1000} num))
    (output : acc (ary '{batch} (ary '{1000} num)))
    (rho : env) (p : path),
  in_acc p output ->
  @vgg16_fresh batch m1 m2 output rho ->
  vgg16_comm_direct input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b c6_w c6_b c7_w c7_b c8_w c8_b c9_w c9_b c10_w c10_b c11_w c11_b c12_w c12_b c13_w c13_b f1_w f1_b f2_w f2_b f3_w f3_b output rho p =
  A(output, VGG16 input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b c6_w c6_b c7_w c7_b c8_w c8_b c9_w c9_b c10_w c10_b c11_w c11_b c12_w c12_b c13_w c13_b f1_w f1_b f2_w f2_b f3_w f3_b) rho p.
Proof.
  intros. unfold vgg16_comm_direct, VGG16, new, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* The original [vgg16_comm] and the direct form are equal as commands. *)
Lemma vgg16_comm_eq_direct :
  forall (batch channel m1 m2 : nat)
    (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
    (c1_w : exp (ary '{64} (ary '{channel} (ary '{3} (ary '{3} num)))))
    (c1_b : exp (ary '{64} num))
    (c2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
    (c2_b : exp (ary '{64} num))
    (c3_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
    (c3_b : exp (ary '{128} num))
    (c4_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
    (c4_b : exp (ary '{128} num))
    (c5_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
    (c5_b : exp (ary '{256} num))
    (c6_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c6_b : exp (ary '{256} num))
    (c7_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c7_b : exp (ary '{256} num))
    (c8_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c8_b : exp (ary '{512} num))
    (c9_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c9_b : exp (ary '{512} num))
    (c10_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c10_b : exp (ary '{512} num))
    (c11_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c11_b : exp (ary '{512} num))
    (c12_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c12_b : exp (ary '{512} num))
    (c13_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c13_b : exp (ary '{512} num))
    (f1_w : exp (ary '{4096} (ary '{512 * s18 m1 * s18 m2} num)))
    (f1_b : exp (ary '{4096} num))
    (f2_w : exp (ary '{4096} (ary '{4096} num)))
    (f2_b : exp (ary '{4096} num))
    (f3_w : exp (ary '{1000} (ary '{4096} num)))
    (f3_b : exp (ary '{1000} num))
    (output : acc (ary '{batch} (ary '{1000} num))),
  vgg16_comm input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b c6_w c6_b c7_w c7_b c8_w c8_b c9_w c9_b c10_w c10_b c11_w c11_b c12_w c12_b c13_w c13_b f1_w f1_b f2_w f2_b f3_w f3_b output =
  vgg16_comm_direct input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b c6_w c6_b c7_w c7_b c8_w c8_b c9_w c9_b c10_w c10_b c11_w c11_b c12_w c12_b c13_w c13_b f1_w f1_b f2_w f2_b f3_w f3_b output.
Proof.
  intros.
  unfold vgg16_comm, vgg16_comm_direct, new.
  cbv zeta beta.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU4d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool4d.
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

Theorem A_VGG16 :
  forall (batch channel m1 m2 : nat)
    (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
    (c1_w : exp (ary '{64} (ary '{channel} (ary '{3} (ary '{3} num)))))
    (c1_b : exp (ary '{64} num))
    (c2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))))
    (c2_b : exp (ary '{64} num))
    (c3_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))))
    (c3_b : exp (ary '{128} num))
    (c4_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))))
    (c4_b : exp (ary '{128} num))
    (c5_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))))
    (c5_b : exp (ary '{256} num))
    (c6_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c6_b : exp (ary '{256} num))
    (c7_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c7_b : exp (ary '{256} num))
    (c8_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))))
    (c8_b : exp (ary '{512} num))
    (c9_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c9_b : exp (ary '{512} num))
    (c10_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c10_b : exp (ary '{512} num))
    (c11_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c11_b : exp (ary '{512} num))
    (c12_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c12_b : exp (ary '{512} num))
    (c13_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))))
    (c13_b : exp (ary '{512} num))
    (f1_w : exp (ary '{4096} (ary '{512 * s18 m1 * s18 m2} num)))
    (f1_b : exp (ary '{4096} num))
    (f2_w : exp (ary '{4096} (ary '{4096} num)))
    (f2_b : exp (ary '{4096} num))
    (f3_w : exp (ary '{1000} (ary '{4096} num)))
    (f3_b : exp (ary '{1000} num))
    (output : acc (ary '{batch} (ary '{1000} num)))
    (rho : env) (p : path),
  in_acc p output ->
  @vgg16_fresh batch m1 m2 output rho ->
  vgg16_comm input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b c6_w c6_b c7_w c7_b c8_w c8_b c9_w c9_b c10_w c10_b c11_w c11_b c12_w c12_b c13_w c13_b f1_w f1_b f2_w f2_b f3_w f3_b output rho p =
  A(output, VGG16 input c1_w c1_b c2_w c2_b c3_w c3_b c4_w c4_b c5_w c5_b c6_w c6_b c7_w c7_b c8_w c8_b c9_w c9_b c10_w c10_b c11_w c11_b c12_w c12_b c13_w c13_b f1_w f1_b f2_w f2_b f3_w f3_b) rho p.
Proof.
  intros. rewrite vgg16_comm_eq_direct. apply A_VGG16_direct; assumption.
Qed.
