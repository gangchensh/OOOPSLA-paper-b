(* DPIA-style Leibniz equivalence proofs for the R-based grouped-convolution
   operator GConv4d (general version plus the two 3x3 specializations used by
   the ResNeXt50 bottleneck blocks).

   Functional semantics: output channel [cout] belongs to the group
   [gi = fin2nat cout / (filernum / g)] and reduces only over the
   [channel / g] input channels of that group:

     out[b, cout, i, j] = bias[cout] + Σ_{c' < channel/g} Σ_{di,dj}
         w[cout, c', di, dj]
       * in[b, gi * (channel/g) + c', i*s + di - p, j*s + dj - p]

   Following the [pad_idx2d] philosophy of Ionia.Ops_Conv, the group base
   index [gi * (channel/g) + c'] is checked at runtime by a Coq bool
   ([Nat.ltb_spec0]) through [gch_read]: in-range positions read the
   corresponding input channel, out-of-range read [zero].  Under the usual
   divisibility conditions ([0 < g], [filernum = g * (filernum / g)],
   [channel = g * (channel / g)] — all satisfied by the ResNeXt50 instances,
   where g = 32 and channel ∈ {64,128,256,512}) the check always succeeds and
   the operator is exactly grouped convolution.  Because the bounds are
   decided at runtime by bools, no fin/nat index-bound lemmas are needed at
   all, exactly as for [pad_idx2d].

   Each operator comes in three parts: a functional definition, an imperative
   counterpart ([*_comm], built from the mkvSeql + suml combinators of
   Ionia.DPIA_Rules), and a Leibniz equality [A_<op>] relating the two. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen]: it defines its own
   [num] constructor (Ring_polynom.PExpr) that would otherwise shadow the
   [data] constructor. *)
From Stdlib Require Import Reals.
Import Proof_CodeGen.
Require Import Ionia.Ops_Conv.
(* [half] is reused from Ionia.ResNet18_DPIA (compiled). *)
Require Import Ionia.ResNet18_DPIA.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Safe group-channel read                                                     *)
(* -------------------------------------------------------------------------- *)

(* Runtime-safe channel read for grouped convolution: channel [gc] of the
   (b-selected) input tensor [img], read through [pad_idx2d] at window
   coordinates [x],[y] with padding offset [p].  If [gc] is out of range
   (only possible when the divisibility conditions above fail), the read is
   [zero].  The boundary test is a Coq bool via [Nat.ltb_spec0]. *)
Definition gch_read {channel m1 m2 : nat} (p : nat)
  (img : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (gc x y : nat) : exp num :=
  match Nat.ltb_spec0 gc channel with
  | ReflectT _ Hc => pad_idx2d p (idx img (nat2fin Hc)) x y
  | ReflectF _ _ => zero
  end.

(* -------------------------------------------------------------------------- *)
(* GConv4d (batch dimension, g groups, with bias — grouped version of Conv4d) *)
(* -------------------------------------------------------------------------- *)

Definition GConv4dCell {batch m1 m2 n1 n2 channel filernum g : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel / g} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch)
  (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  : exp num :=
  add (sum (mkvSeq (fun c : fin (channel / g) =>
        sum (mkvSeq (fun i1 : fin n1 =>
          sum (mkvSeq (fun j1 : fin n2 =>
            mul (gch_read p (idx input b)
                   ((fin2nat cout / (filernum / g)) * (channel / g) + fin2nat c)
                   (fin2nat i0 * s + fin2nat i1)
                   (fin2nat j0 * s + fin2nat j1))
                (idx (idx (idx (idx w cout) c) i1) j1))))))))
      (idx bias cout).

Definition GConv4d {batch m1 m2 n1 n2 channel filernum g : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel / g} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum}
        (ary '{((m1 - n1 + 2 * p) / s + 1)}
         (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin filernum =>
    mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
      mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
        GConv4dCell p s bias w input b num i0 j0)))).

Definition GConv4dCell_comm {batch m1 m2 n1 n2 channel filernum g : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel / g} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch)
  (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num)
  : comm :=
  suml (mkvSeq (fun c : fin (channel / g) =>
    sum (mkvSeq (fun i1 : fin n1 =>
      sum (mkvSeq (fun j1 : fin n2 =>
        mul (gch_read p (idx input b)
               ((fin2nat cout / (filernum / g)) * (channel / g) + fin2nat c)
               (fin2nat i0 * s + fin2nat i1)
               (fin2nat j0 * s + fin2nat j1))
            (idx (idx (idx (idx w cout) c) i1) j1)))))))
       (fun r : exp num => output_cell |:= add r (idx bias cout))
       output_cell.

Definition GConv4d_comm {batch m1 m2 n1 n2 channel filernum g : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel / g} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun num oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      GConv4dCell_comm p s bias w input b num i0 j0 o1) o0) oc) ob) output.

Lemma A_GConv4d : forall (batch m1 m2 n1 n2 channel filernum g p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel / g} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  A(output, GConv4d p s bias w input) = GConv4d_comm p s bias w input output.
Proof.
  intros. unfold GConv4d, GConv4d_comm, GConv4dCell, GConv4dCell_comm.
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
(* GConv4d_3x3_s1 : grouped same-size 3x3 convolution, padding 1, stride 1     *)
(* (mirrors Conv4d_3x3_s1 of Ionia.ResNet18_DPIA with a group reduction)       *)
(* -------------------------------------------------------------------------- *)

Definition GConv4d_3x3_s1 {batch inch outch g m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch / g} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin m1 => mkvSeq (fun j0 : fin m2 =>
      add (sum (mkvSeq (fun c : fin (inch / g) =>
            sum (mkvSeq (fun i1 : fin 3 =>
              sum (mkvSeq (fun j1 : fin 3 =>
                mul (gch_read 1 (idx input b)
                       ((fin2nat num / (outch / g)) * (inch / g) + fin2nat c)
                       (fin2nat i0 + fin2nat i1)
                       (fin2nat j0 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition GConv4d_3x3_s1_comm {batch inch outch g m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch / g} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin (inch / g) =>
             sum (mkvSeq (fun i1 : fin 3 =>
               sum (mkvSeq (fun j1 : fin 3 =>
                 mul (gch_read 1 (idx input b)
                        ((fin2nat cout / (outch / g)) * (inch / g) + fin2nat c)
                        (fin2nat i0 + fin2nat i1)
                        (fin2nat j0 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_GConv4d_3x3_s1 : forall (batch inch outch g m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch / g} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{m1} (ary '{m2} num))))),
  A(output, GConv4d_3x3_s1 bias w input) = GConv4d_3x3_s1_comm bias w input output.
Proof.
  intros. unfold GConv4d_3x3_s1, GConv4d_3x3_s1_comm.
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
(* GConv4d_3x3_s2 : grouped 3x3 convolution, padding 1, stride 2, half output  *)
(* (mirrors Conv4d_3x3_s2 of Ionia.ResNet18_DPIA with a group reduction)       *)
(* -------------------------------------------------------------------------- *)

Definition GConv4d_3x3_s2 {batch inch outch g m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch / g} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin outch =>
    mkvSeq (fun i0 : fin (half m1) => mkvSeq (fun j0 : fin (half m2) =>
      add (sum (mkvSeq (fun c : fin (inch / g) =>
            sum (mkvSeq (fun i1 : fin 3 =>
              sum (mkvSeq (fun j1 : fin 3 =>
                mul (gch_read 1 (idx input b)
                       ((fin2nat num / (outch / g)) * (inch / g) + fin2nat c)
                       (fin2nat i0 * 2 + fin2nat i1)
                       (fin2nat j0 * 2 + fin2nat j1))
                    (idx (idx (idx (idx w num) c) i1) j1))))))))
          (idx bias num))))).

Definition GConv4d_3x3_s2_comm {batch inch outch g m1 m2 : nat}
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch / g} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      suml (mkvSeq (fun c : fin (inch / g) =>
             sum (mkvSeq (fun i1 : fin 3 =>
               sum (mkvSeq (fun j1 : fin 3 =>
                 mul (gch_read 1 (idx input b)
                        ((fin2nat cout / (outch / g)) * (inch / g) + fin2nat c)
                        (fin2nat i0 * 2 + fin2nat i1)
                        (fin2nat j0 * 2 + fin2nat j1))
                     (idx (idx (idx (idx w cout) c) i1) j1)))))))
           (fun r : exp num => o1 |:= add r (idx bias cout))
           o1) o0) oc) ob) output.

Lemma A_GConv4d_3x3_s2 : forall (batch inch outch g m1 m2 : nat)
  (bias : exp (ary '{outch} num))
  (w : exp (ary '{outch} (ary '{inch / g} (ary '{3} (ary '{3} num)))))
  (input : exp (ary '{batch} (ary '{inch} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{outch} (ary '{half m1} (ary '{half m2} num))))),
  A(output, GConv4d_3x3_s2 bias w input) = GConv4d_3x3_s2_comm bias w input output.
Proof.
  intros. unfold GConv4d_3x3_s2, GConv4d_3x3_s2_comm.
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
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_GConv4d.
Print Assumptions A_GConv4d_3x3_s1.
Print Assumptions A_GConv4d_3x3_s2.
