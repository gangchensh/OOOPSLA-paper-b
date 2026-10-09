(* DPIA-style Leibniz equivalence proofs for R-based convolution-family
   operators (Conv2d, Conv4d, and the three ResNet/AlexNet Conv4d
   specializations).

   The functional definitions are direct translations of the operators in
   Ionia.CNN_OP (Conv2d at line 283, Conv4d at line 299, and the
   p1_k3_s2 / p0_k1_s2 / p3_k7_s2 specializations at lines 331/338/348)
   into the Proof_CodeGen R-model, with comparisons staying in Coq [bool].
   Each operator comes in three parts: a functional definition, an
   imperative counterpart ([*_comm], built from the mkvSeql + suml
   combinators of Ionia.DPIA_Rules), and a Leibniz equality [A_<op>]
   relating the two.

   Unlike Ionia.CNN_OP, which materializes the padding with [Padding2d]
   before sliding the window, the padding is inlined here through
   [pad_idx2d]: the window coordinate [i0 * s + i1] is compared against
   the padding offset [p] with Coq bool boundary tests
   ([Nat.leb_spec0] / [Nat.ltb_spec0]) and out-of-range positions read
   as [zero].  This keeps the file self-contained (no dependency on the
   padding operators of Ops_PoolPad.v) and — because the bounds are
   decided at runtime by bools — requires no fin/nat index-bound lemmas
   at all, unlike the [conv_flat_*_bound] family needed by [A_Conv3d]
   in Ionia.LeNet5_DPIA. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen]: it defines its own
   [num] constructor (Ring_polynom.PExpr) that would otherwise shadow the
   [data] constructor. *)
From Stdlib Require Import Reals.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Safe 2D read with zero padding                                              *)
(* -------------------------------------------------------------------------- *)

(* Runtime-safe 2D read with padding offset [p]: the window coordinate
   [x] addresses the unpadded image at [x - p]; positions with [x < p]
   (left/top padding) or [x - p >= m] (right/bottom padding) read as
   [zero].  All boundary tests are Coq bools via [Nat.leb_spec0] and
   [Nat.ltb_spec0]. *)
Definition pad_idx2d {m1 m2 : nat} (p : nat)
  (img : exp (ary '{m1} (ary '{m2} num))) (x y : nat) : exp num :=
  match Nat.leb_spec0 p x with
  | ReflectT _ _ =>
      match Nat.ltb_spec0 (x - p) m1 with
      | ReflectT _ Hx =>
          match Nat.leb_spec0 p y with
          | ReflectT _ _ =>
              match Nat.ltb_spec0 (y - p) m2 with
              | ReflectT _ Hy => idx (idx img (nat2fin Hx)) (nat2fin Hy)
              | ReflectF _ _ => zero
              end
          | ReflectF _ _ => zero
          end
      | ReflectF _ _ => zero
      end
  | ReflectF _ _ => zero
  end.

(* -------------------------------------------------------------------------- *)
(* Conv2d (padding p, stride s, no bias — mirrors Ionia.CNN_OP Conv2d)        *)
(* -------------------------------------------------------------------------- *)

Definition Conv2dCell {m1 m2 n1 n2 : nat} (p s : nat)
  (w : exp (ary '{n1} (ary '{n2} num)))
  (input : exp (ary '{m1} (ary '{m2} num)))
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  : exp num :=
  sum (mkvSeq (fun i1 : fin n1 =>
    sum (mkvSeq (fun j1 : fin n2 =>
      mul (pad_idx2d p input (fin2nat i0 * s + fin2nat i1)
                             (fin2nat j0 * s + fin2nat j1))
          (idx (idx w i1) j1))))).

Definition Conv2d {m1 m2 n1 n2 : nat} (p s : nat)
  (w : exp (ary '{n1} (ary '{n2} num)))
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{((m1 - n1 + 2 * p) / s + 1)}
         (ary '{((m2 - n2 + 2 * p) / s + 1)} num)) :=
  mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
    mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
      Conv2dCell p s w input i0 j0)).

Definition Conv2dCell_comm {m1 m2 n1 n2 : nat} (p s : nat)
  (w : exp (ary '{n1} (ary '{n2} num)))
  (input : exp (ary '{m1} (ary '{m2} num)))
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num)
  : comm :=
  suml (mkvSeq (fun i1 : fin n1 =>
    sum (mkvSeq (fun j1 : fin n2 =>
      mul (pad_idx2d p input (fin2nat i0 * s + fin2nat i1)
                             (fin2nat j0 * s + fin2nat j1))
          (idx (idx w i1) j1)))))
       (fun r : exp num => output_cell |:= r)
       output_cell.

Definition Conv2d_comm {m1 m2 n1 n2 : nat} (p s : nat)
  (w : exp (ary '{n1} (ary '{n2} num)))
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))
  : comm :=
  mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
    Conv2dCell_comm p s w input i0 j0 o1) o0) output.

Lemma A_Conv2d : forall (m1 m2 n1 n2 p s : nat)
  (w : exp (ary '{n1} (ary '{n2} num)))
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))),
  A(output, Conv2d p s w input) = Conv2d_comm p s w input output.
Proof.
  intros. unfold Conv2d, Conv2d_comm, Conv2dCell, Conv2dCell_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv4d (batch dimension, with bias — mirrors Ionia.CNN_OP Conv4d)          *)
(* -------------------------------------------------------------------------- *)

Definition Conv4dCell {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch)
  (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  : exp num :=
  add (sum (mkvSeq (fun c : fin channel =>
        sum (mkvSeq (fun i1 : fin n1 =>
          sum (mkvSeq (fun j1 : fin n2 =>
            mul (pad_idx2d p (idx (idx input b) c)
                           (fin2nat i0 * s + fin2nat i1)
                           (fin2nat j0 * s + fin2nat j1))
                (idx (idx (idx (idx w cout) c) i1) j1))))))))
      (idx bias cout).

Definition Conv4d {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum}
        (ary '{((m1 - n1 + 2 * p) / s + 1)}
         (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin filernum =>
    mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
      mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
        Conv4dCell p s bias w input b num i0 j0)))).

Definition Conv4dCell_comm {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch)
  (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num)
  : comm :=
  suml (mkvSeq (fun c : fin channel =>
    sum (mkvSeq (fun i1 : fin n1 =>
      sum (mkvSeq (fun j1 : fin n2 =>
        mul (pad_idx2d p (idx (idx input b) c)
                       (fin2nat i0 * s + fin2nat i1)
                       (fin2nat j0 * s + fin2nat j1))
            (idx (idx (idx (idx w cout) c) i1) j1)))))))
       (fun r : exp num => output_cell |:= add r (idx bias cout))
       output_cell.

Definition Conv4d_comm {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun num oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      Conv4dCell_comm p s bias w input b num i0 j0 o1) o0) oc) ob) output.

Lemma A_Conv4d : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  A(output, Conv4d p s bias w input) = Conv4d_comm p s bias w input output.
Proof.
  intros. unfold Conv4d, Conv4d_comm, Conv4dCell, Conv4dCell_comm.
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
(* Specialized Conv4d variants (direct instances of Conv4d)                   *)
(* -------------------------------------------------------------------------- *)

Definition Conv4d_p1_k3_s2 {batch inch outch m : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias : exp (ary '{outch} num))
  : exp (ary '{batch} (ary '{outch}
        (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num)))) :=
  @Conv4d batch m m 3 3 inch outch 1 2 bias w input.

Definition Conv4d_p1_k3_s2_comm {batch inch outch m : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias : exp (ary '{outch} num))
  (output : acc (ary '{batch} (ary '{outch}
                (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num)))))
  : comm :=
  @Conv4d_comm batch m m 3 3 inch outch 1 2 bias w input output.

Lemma A_Conv4d_p1_k3_s2 : forall (batch inch outch m : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias : exp (ary '{outch} num))
  (output : acc (ary '{batch} (ary '{outch}
                (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num))))),
  A(output, Conv4d_p1_k3_s2 input w bias) =
  Conv4d_p1_k3_s2_comm input w bias output.
Proof.
  intros. unfold Conv4d_p1_k3_s2, Conv4d_p1_k3_s2_comm.
  apply A_Conv4d.
Qed.

Definition Conv4d_p0_k1_s2 {batch inch outch m : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias : exp (ary '{outch} num))
  : exp (ary '{batch} (ary '{outch}
        (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num)))) :=
  @Conv4d batch m m 1 1 inch outch 0 2 bias w input.

Definition Conv4d_p0_k1_s2_comm {batch inch outch m : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias : exp (ary '{outch} num))
  (output : acc (ary '{batch} (ary '{outch}
                (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num)))))
  : comm :=
  @Conv4d_comm batch m m 1 1 inch outch 0 2 bias w input output.

Lemma A_Conv4d_p0_k1_s2 : forall (batch inch outch m : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias : exp (ary '{outch} num))
  (output : acc (ary '{batch} (ary '{outch}
                (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num))))),
  A(output, Conv4d_p0_k1_s2 input w bias) =
  Conv4d_p0_k1_s2_comm input w bias output.
Proof.
  intros. unfold Conv4d_p0_k1_s2, Conv4d_p0_k1_s2_comm.
  exact (A_Conv4d batch m m 1 1 inch outch 0 2 bias w input output).
Qed.

(* 7x7 convolution with padding=3, stride=2, for the ImageNet ResNet stem. *)
Definition Conv4d_p3_k7_s2 {batch inch outch m : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{7} (ary '{7} num)))))
  (bias : exp (ary '{outch} num))
  : exp (ary '{batch} (ary '{outch}
        (ary '{((m - 7 + 2 * 3) / 2 + 1)} (ary '{((m - 7 + 2 * 3) / 2 + 1)} num)))) :=
  @Conv4d batch m m 7 7 inch outch 3 2 bias w input.

Definition Conv4d_p3_k7_s2_comm {batch inch outch m : nat}
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{7} (ary '{7} num)))))
  (bias : exp (ary '{outch} num))
  (output : acc (ary '{batch} (ary '{outch}
                (ary '{((m - 7 + 2 * 3) / 2 + 1)} (ary '{((m - 7 + 2 * 3) / 2 + 1)} num)))))
  : comm :=
  @Conv4d_comm batch m m 7 7 inch outch 3 2 bias w input output.

Lemma A_Conv4d_p3_k7_s2 : forall (batch inch outch m : nat)
  (input : exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w : exp (ary '{outch} (ary '{inch} (ary '{7} (ary '{7} num)))))
  (bias : exp (ary '{outch} num))
  (output : acc (ary '{batch} (ary '{outch}
                (ary '{((m - 7 + 2 * 3) / 2 + 1)} (ary '{((m - 7 + 2 * 3) / 2 + 1)} num))))),
  A(output, Conv4d_p3_k7_s2 input w bias) =
  Conv4d_p3_k7_s2_comm input w bias output.
Proof.
  intros. unfold Conv4d_p3_k7_s2, Conv4d_p3_k7_s2_comm.
  apply A_Conv4d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Conv2d.
Print Assumptions A_Conv4d.
Print Assumptions A_Conv4d_p1_k3_s2.
Print Assumptions A_Conv4d_p0_k1_s2.
Print Assumptions A_Conv4d_p3_k7_s2.
