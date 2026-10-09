(* R-based functional CNN operators for the LeNet-5 DPIA proof.

   These definitions mirror the operators in ForCNN5/CNN_OP.v and
   Zonia/Zonia/CNN/operation.v, but use the Proof_CodeGen model where
   [exp num = R] and comparisons return [bool].  This makes them
   compatible with the Leibniz A/C rules in Ionia.DPIA_Rules.

   We use the explicit [idx]/[idxAcc] functions instead of the [|[ ]]/[|{ }]
   notations throughout this file.  The [match] construct used for safe
   padding in [Ionia.LeNet5_Utils] registers ["|"] as a keyword, which
   interferes with those notations during later parsing. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.LeNet5_Utils.
Require Import Ionia.Ops_Conv.
From Stdlib Require Import Lia.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* ReLU                                                                      *)
(* -------------------------------------------------------------------------- *)

Definition ReLU1d {n:nat} (input : exp (ary '{n} num)) : exp (ary '{n} num) :=
  mkvSeq (fun i : fin n => if leExp (idx input i) zero then zero else idx input i).

Definition ReLU2d {m1 m2:nat} (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i0 : fin m1 => mkvSeq (fun i1 : fin m2 =>
    if leExp (idx (idx input i0) i1) zero then zero else idx (idx input i0) i1)).

Definition ReLU3d {filernum m1 m2:nat}
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun num : fin filernum => mkvSeq (fun i0 : fin m1 => mkvSeq (fun i1 : fin m2 =>
    if leExp (idx (idx (idx input num) i0) i1) zero
      then zero
      else idx (idx (idx input num) i0) i1))).

(* -------------------------------------------------------------------------- *)
(* Flatten3d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Flatten3d {channel m1 m2 : nat}
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{channel * m1 * m2} num) :=
  mkvSeq (fun x : fin (channel * m1 * m2) =>
    idx (idx (idx input
                 (fst (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
            (snd (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
        (snd (idx_1d_to_2d x))).

(* -------------------------------------------------------------------------- *)
(* Linear1d                                                                   *)
(* -------------------------------------------------------------------------- *)

Definition Linear1d {m outnum : nat}
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{m} num))
  : exp (ary '{outnum} num) :=
  mkvSeq (fun out : fin outnum =>
    add (sum (mkvSeq (fun i : fin m => mul (idx input i) (idx (idx w out) i))))
        (idx bias out)).

(* -------------------------------------------------------------------------- *)
(* Maxpool3d (2x2 non-overlapping windows)                                    *)
(* -------------------------------------------------------------------------- *)

Lemma maxpool_index_lt : forall (m : nat) (i0 : fin (m / 2)) (di : fin 2),
  2 * fin2nat i0 + fin2nat di < m.
Proof.
  intros. destruct i0 as [i0 Hi0], di as [di Hdi]. simpl in *.
  assert (2 * S i0 <= m).
  { transitivity (2 * (m / 2)).
    - apply Nat.mul_le_mono_nonneg_l. lia. exact Hi0.
    - apply Nat.mul_div_le. lia. }
  lia.
Qed.

Definition Maxpool3d {channel m : nat}
  (input : exp (ary '{channel} (ary '{m} (ary '{m} num))))
  : exp (ary '{channel} (ary '{(m/2)} (ary '{(m/2)} num))) :=
  mkvSeq (fun c : fin channel => mkvSeq (fun i0 : fin (m/2) => mkvSeq (fun j0 : fin (m/2) =>
    max (mkvSeq (fun x : fin 4 =>
      idx (idx (idx input c)
               (nat2fin (maxpool_index_lt m i0 (fst (@idx_1d_to_2d 2 2 x)))))
          (nat2fin (maxpool_index_lt m j0 (snd (@idx_1d_to_2d 2 2 x))))))))).

(* -------------------------------------------------------------------------- *)
(* Softmax1d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Softmax1d {n:nat} (input : exp (ary '{n} num)) : exp (ary '{n} num) :=
  let denom := sum (mkvSeq (fun j : fin n => pExp (idx input j))) in
  mkvSeq (fun i : fin n => div (pExp (idx input i)) denom).

(* -------------------------------------------------------------------------- *)
(* Conv3d                                                                     *)
(* -------------------------------------------------------------------------- *)

(* Padding is inlined via [pad_idx2d] from Ionia.Ops_Conv (zero padding with
   Coq bool boundary tests), aligning the route-A semantics with route B's
   [Padding2d] and the standard convolution definition.  The earlier version
   used [safe_idx2d] on the nat-truncated coordinates [i0 + di - p], which
   clamped top/left out-of-bounds positions to index 0 (reading the edge
   value) instead of yielding zero. *)
Definition Conv3dCell {h w ic oc k p : nat} (Hk : k > 0)
  (kernel : exp (ary '{oc} (ary '{ic} (ary '{k} (ary '{k} num)))))
  (bias : exp (ary '{oc} num))
  (input : exp (ary '{ic} (ary '{h} (ary '{w} num))))
  (cout : fin oc)
  (i0 : fin (h + 2 * p - k + 1))
  (j0 : fin (w + 2 * p - k + 1))
  : exp num :=
  add (sum (mkvSeq (fun flat : fin (ic * k * k) =>
    mul (pad_idx2d p (idx input (nat2fin (conv_flat_c_bound flat Hk)))
                    (fin2nat i0 + Nat.div (Nat.modulo (fin2nat flat) (k * k)) k)
                    (fin2nat j0 + Nat.modulo (fin2nat flat) k))
        (idx (idx (idx (idx kernel cout)
                       (nat2fin (conv_flat_c_bound flat Hk)))
                  (nat2fin (conv_flat_di_bound flat Hk)))
             (nat2fin (conv_flat_dj_bound flat Hk))))))
      (idx bias cout).

Definition Conv3d {h w ic oc k p : nat} (Hk : k > 0)
  (kernel : exp (ary '{oc} (ary '{ic} (ary '{k} (ary '{k} num)))))
  (bias : exp (ary '{oc} num))
  (input : exp (ary '{ic} (ary '{h} (ary '{w} num))))
  : exp (ary '{oc} (ary '{(h + 2 * p - k + 1)} (ary '{(w + 2 * p - k + 1)} num))) :=
  mkvSeq (fun cout : fin oc =>
    mkvSeq (fun i0 : fin (h + 2 * p - k + 1) =>
      mkvSeq (fun j0 : fin (w + 2 * p - k + 1) =>
        Conv3dCell Hk kernel bias input cout i0 j0))).

(* -------------------------------------------------------------------------- *)
(* Full LeNet-5 (1×28×28 input, standard layer sizes)                         *)
(* -------------------------------------------------------------------------- *)

Definition H5 : 5 > 0 := Nat.lt_0_succ 4.

Definition LeNet5
  (input : exp (ary '{1} (ary '{28} (ary '{28} num))))
  (c1_w : exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))))
  (c1_b : exp (ary '{6} num))
  (c3_w : exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (c3_b : exp (ary '{16} num))
  (f5_w : exp (ary '{120} (ary '{400} num)))
  (f5_b : exp (ary '{120} num))
  (f6_w : exp (ary '{84} (ary '{120} num)))
  (f6_b : exp (ary '{84} num))
  (out_w : exp (ary '{10} (ary '{84} num)))
  (out_b : exp (ary '{10} num))
  : exp (ary '{10} num) :=
  let l1 := ReLU3d (Conv3d (p:=2) H5 c1_w c1_b input) in
  let l2 := Maxpool3d l1 in
  let l3 := ReLU3d (Conv3d (p:=0) H5 c3_w c3_b l2) in
  let l4 := Maxpool3d l3 in
  let l5 := Flatten3d l4 in
  let l6 := ReLU1d (Linear1d f5_w f5_b l5) in
  let l7 := ReLU1d (Linear1d f6_w f6_b l6) in
  Softmax1d (Linear1d out_w out_b l7).
