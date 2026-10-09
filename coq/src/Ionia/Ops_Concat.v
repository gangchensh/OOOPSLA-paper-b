(* DPIA-style Leibniz equivalence proofs for R-based concatenation-family
   and depthwise-convolution operators (Concat4d, Concat4d4, ChannelScale4d,
   DWConv4d).

   Concat4d is a direct translation of the operator in Ionia.CNN_OP
   (Concat4d at line 667) into the Proof_CodeGen R-model: the channel index
   [c : fin (c1 + c2)] is split at runtime by the Coq bool boundary test
   [Nat.ltb_spec0], and the two branches read [x] at [c] resp. [y] at
   [c - c1]; the bounds needed by [nat2fin] are discharged by the generic
   subtraction lemma [concat_split_lt] together with [fin_proof].
   Concat4d4 is the four-branch generalization used by GoogLeNet-style
   inception blocks, reusing the same lemma on cumulative channel sums.

   DWConv4d (depthwise convolution) follows the Conv2d/Conv4d template of
   Ionia.Ops_Conv: the padding is inlined through [pad_idx2d] (imported
   from Ionia.Ops_Conv), so no fin/nat index-bound lemmas are needed; the
   reduction runs over the k x k kernel only (no channel reduction, no
   bias).

   ChannelScale4d is the SE-style per-channel scaling out[b,c,i,j] =
   x[b,c,i,j] * s[c], an instance of the pointwise template of
   Ionia.Ops_Elementwise.

   Each operator comes in three parts: a functional definition ([mkvSeq] +
   Coq [bool] branches + [idx]), an imperative counterpart ([*_comm]),
   and a Leibniz equality [A_<op>] closed with [Qed]. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* [pad_idx2d] is reused from Ionia.Ops_Conv (compiled). *)
Require Import Ionia.Ops_Conv.
(* Reals must be imported before [Import Proof_CodeGen]: it defines its own
   [num] constructor (Ring_polynom.PExpr) that would otherwise shadow the
   [data] constructor. *)
From Stdlib Require Import Reals Arith Lia.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Index-splitting bound for channel concatenation                             *)
(* -------------------------------------------------------------------------- *)

(* If the flat channel index [v] lies in the slice [c1, c1 + c2), then
   [v - c1] is a valid index into the second tensor.  Used for every
   non-first branch of Concat4d/Concat4d4 with the cumulative channel sums
   as [c1] (mirrors [fin_ge_sub_lt] in Ionia.CNN_OP, phrased on plain nats
   so a single lemma serves all branches). *)
Lemma concat_split_lt : forall (v c1 c2 : nat),
  ~ v < c1 -> v < c1 + c2 -> v - c1 < c2.
Proof. intros. lia. Qed.
(* Keep all three nat parameters explicit so call sites can pass the
   cumulative channel sums positionally. *)
Arguments concat_split_lt v c1 c2 _ _ : clear implicits.

(* -------------------------------------------------------------------------- *)
(* Concat4d (channel concatenation of two 4d tensors)                          *)
(* -------------------------------------------------------------------------- *)

Definition Concat4dCell {batch c1 c2 m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (c : fin (c1 + c2)) (i : fin m1) (j : fin m2)
  : exp num :=
  match Nat.ltb_spec0 (fin2nat c) c1 with
  | ReflectT _ Hlt => idx (idx (idx (idx x b) (nat2fin Hlt)) i) j
  | ReflectF _ Hge =>
      idx (idx (idx (idx y b)
        (nat2fin (concat_split_lt (fin2nat c) c1 c2 Hge (fin_proof c)))) i) j
  end.

Definition Concat4d {batch c1 c2 m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{(c1 + c2)} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin (c1 + c2) =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      Concat4dCell x y b c i j)))).

Definition Concat4d_comm {batch c1 c2 m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{(c1 + c2)} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin (c1 + c2) =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        Concat4dCell x y b c i j)))).

Lemma A_Concat4d : forall (batch c1 c2 m1 m2 : nat)
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{(c1 + c2)} (ary '{m1} (ary '{m2} num))))),
  A(output, Concat4d x y) = Concat4d_comm x y output.
Proof.
  intros. unfold Concat4d, Concat4d_comm.
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
(* Concat4d4 (four-way channel concatenation, GoogLeNet inception blocks)      *)
(* -------------------------------------------------------------------------- *)

Definition Concat4d4Cell {batch c1 c2 c3 c4 m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (z : exp (ary '{batch} (ary '{c3} (ary '{m1} (ary '{m2} num)))))
  (w : exp (ary '{batch} (ary '{c4} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (c : fin (c1 + c2 + c3 + c4)) (i : fin m1) (j : fin m2)
  : exp num :=
  match Nat.ltb_spec0 (fin2nat c) c1 with
  | ReflectT _ H1 => idx (idx (idx (idx x b) (nat2fin H1)) i) j
  | ReflectF _ H1 =>
      match Nat.ltb_spec0 (fin2nat c) (c1 + c2) with
      | ReflectT _ H2 =>
          idx (idx (idx (idx y b)
            (nat2fin (concat_split_lt (fin2nat c) c1 c2 H1 H2))) i) j
      | ReflectF _ H2 =>
          match Nat.ltb_spec0 (fin2nat c) (c1 + c2 + c3) with
          | ReflectT _ H3 =>
              idx (idx (idx (idx z b)
                (nat2fin (concat_split_lt (fin2nat c) (c1 + c2) c3
                                          H2 H3))) i) j
          | ReflectF _ H3 =>
              idx (idx (idx (idx w b)
                (nat2fin (concat_split_lt (fin2nat c) (c1 + c2 + c3) c4
                                          H3 (fin_proof c)))) i) j
          end
      end
  end.

Definition Concat4d4 {batch c1 c2 c3 c4 m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (z : exp (ary '{batch} (ary '{c3} (ary '{m1} (ary '{m2} num)))))
  (w : exp (ary '{batch} (ary '{c4} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{(c1 + c2 + c3 + c4)} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin (c1 + c2 + c3 + c4) =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      Concat4d4Cell x y z w b c i j)))).

Definition Concat4d4_comm {batch c1 c2 c3 c4 m1 m2 : nat}
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (z : exp (ary '{batch} (ary '{c3} (ary '{m1} (ary '{m2} num)))))
  (w : exp (ary '{batch} (ary '{c4} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{(c1 + c2 + c3 + c4)}
                         (ary '{m1} (ary '{m2} num)))))
  : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin (c1 + c2 + c3 + c4) =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        Concat4d4Cell x y z w b c i j)))).

Lemma A_Concat4d4 : forall (batch c1 c2 c3 c4 m1 m2 : nat)
  (x : exp (ary '{batch} (ary '{c1} (ary '{m1} (ary '{m2} num)))))
  (y : exp (ary '{batch} (ary '{c2} (ary '{m1} (ary '{m2} num)))))
  (z : exp (ary '{batch} (ary '{c3} (ary '{m1} (ary '{m2} num)))))
  (w : exp (ary '{batch} (ary '{c4} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{(c1 + c2 + c3 + c4)}
                         (ary '{m1} (ary '{m2} num))))),
  A(output, Concat4d4 x y z w) = Concat4d4_comm x y z w output.
Proof.
  intros. unfold Concat4d4, Concat4d4_comm.
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
(* ChannelScale4d (SE-style per-channel scaling: out[b,c,i,j] = x*s[c])        *)
(* -------------------------------------------------------------------------- *)

Definition ChannelScale4d {batch channel m1 m2 : nat}
  (s : exp (ary '{channel} num))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin m2 =>
      mul (idx (idx (idx (idx input b) c) i) j) (idx s c))))).

Definition ChannelScale4d_comm {batch channel m1 m2 : nat}
  (s : exp (ary '{channel} num))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin channel =>
    seqfor (fun i : fin m1 => seqfor (fun j : fin m2 =>
      idxAcc (idxAcc (idxAcc (idxAcc output b) c) i) j |:=
        mul (idx (idx (idx (idx input b) c) i) j) (idx s c))))).

Lemma A_ChannelScale4d : forall (batch channel m1 m2 : nat)
  (s : exp (ary '{channel} num))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))),
  A(output, ChannelScale4d s input) = ChannelScale4d_comm s input output.
Proof.
  intros. unfold ChannelScale4d, ChannelScale4d_comm.
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
(* DWConv4d (depthwise convolution: per-channel k x k reduction, no bias)      *)
(* -------------------------------------------------------------------------- *)

Definition DWConv4dCell {batch m1 m2 n1 n2 channel : nat} (p s : nat)
  (w : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (c : fin channel)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  : exp num :=
  sum (mkvSeq (fun di : fin n1 => sum (mkvSeq (fun dj : fin n2 =>
    mul (idx (idx (idx w c) di) dj)
        (pad_idx2d p (idx (idx input b) c)
                   (fin2nat i0 * s + fin2nat di)
                   (fin2nat j0 * s + fin2nat dj)))))).

Definition DWConv4d {batch m1 m2 n1 n2 channel : nat} (p s : nat)
  (w : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel}
        (ary '{((m1 - n1 + 2 * p) / s + 1)}
         (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    mkvSeq (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
      mkvSeq (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
        DWConv4dCell p s w input b c i0 j0)))).

Definition DWConv4dCell_comm {batch m1 m2 n1 n2 channel : nat} (p s : nat)
  (w : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch) (c : fin channel)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num)
  : comm :=
  suml (mkvSeq (fun di : fin n1 => sum (mkvSeq (fun dj : fin n2 =>
    mul (idx (idx (idx w c) di) dj)
        (pad_idx2d p (idx (idx input b) c)
                   (fin2nat i0 * s + fin2nat di)
                   (fin2nat j0 * s + fin2nat dj))))))
       (fun r : exp num => output_cell |:= r)
       output_cell.

Definition DWConv4d_comm {batch m1 m2 n1 n2 channel : nat} (p s : nat)
  (w : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun c oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      DWConv4dCell_comm p s w input b c i0 j0 o1) o0) oc) ob) output.

Lemma A_DWConv4d : forall (batch m1 m2 n1 n2 channel p s : nat)
  (w : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  A(output, DWConv4d p s w input) = DWConv4d_comm p s w input output.
Proof.
  intros. unfold DWConv4d, DWConv4d_comm, DWConv4dCell, DWConv4dCell_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_sum_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Concat4d.
Print Assumptions A_Concat4d4.
Print Assumptions A_ChannelScale4d.
Print Assumptions A_DWConv4d.
