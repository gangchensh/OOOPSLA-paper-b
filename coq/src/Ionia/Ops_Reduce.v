(* DPIA-style Leibniz equivalence proofs for R-based reduction-family
   operators (average pooling, global average pooling, softmax).

   The functional definitions are direct translations of the operators in
   Ionia.CNN_OP (Avgpool2d/3d/4d, GlobalAvgPool4d, Softmax2d/3d) into the
   Proof_CodeGen R-model: [div_n x n] is written as the R-division
   [div x (INR n)] (the two are convertible) so that the reflexivity rules
   [A_div_post] / [C_sum_post_acc] apply directly, and comparisons stay in
   Coq [bool].  Each operator comes in three parts: a functional
   definition, an imperative counterpart ([*_comm], built from the
   mkvSeql + suml combinators of Ionia.DPIA_Rules), and a Leibniz equality
   [A_<op>] relating the two. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen]: it defines its own
   [num] constructor (Ring_polynom.PExpr) that would otherwise shadow the
   [data] constructor. *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Window index bound (mirrors [fin_mul_add_lt_div] in Ionia.CNN_OP)          *)
(* -------------------------------------------------------------------------- *)

Lemma avgpool_index_lt : forall m k (i : fin (m / k)) (j : fin k),
  fin2nat i * k + fin2nat j < m.
Proof.
  intros m k i j.
  destruct k.
  - exfalso. assert (H_lt : fin2nat j < 0) by apply (fin_proof j). lia.
  - assert (Hi : fin2nat i < m / S k) by apply (fin_proof i).
    assert (Hj : fin2nat j < S k) by apply (fin_proof j).
    assert (H_le : S k * (m / S k) <= m).
    { pose proof (Nat.div_mod_eq m (S k)) as H_eq. lia. }
    assert (H_ik : fin2nat i * S k <= (m / S k - 1) * S k).
    { apply Nat.mul_le_mono_r. lia. }
    assert (H_le2 : (m / S k - 1) * S k + S k <= m / S k * S k).
    { destruct (m / S k). lia. simpl. lia. }
    lia.
Qed.
Arguments avgpool_index_lt m k i j : clear implicits.

(* -------------------------------------------------------------------------- *)
(* Avgpool2d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Avgpool2d {m1 m2:nat} (k:nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{(m1/k)} (ary '{(m2/k)} num)) :=
  mkvSeq (fun i0 : fin (m1/k) => mkvSeq (fun i1 : fin (m2/k) =>
    div (sum (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
      idx (idx input (nat2fin (avgpool_index_lt m1 k i0 j0)))
              (nat2fin (avgpool_index_lt m2 k i1 j1)))))))
        (INR (k * k)))).

Definition Avgpool2d_comm {m1 m2:nat} (k:nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{(m1/k)} (ary '{(m2/k)} num))) : comm :=
  mkvSeql (fun i0 o0 => mkvSeql (fun i1 o1 =>
    suml (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
      idx (idx input (nat2fin (avgpool_index_lt m1 k i0 j0)))
              (nat2fin (avgpool_index_lt m2 k i1 j1))))))
         (fun r => o1 |:= div r (INR (k * k)))
         o1) o0) output.

Lemma A_Avgpool2d : forall (m1 m2 k : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{(m1/k)} (ary '{(m2/k)} num))),
  A(output, Avgpool2d k input) = Avgpool2d_comm k input output.
Proof.
  intros. unfold Avgpool2d, Avgpool2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i1.
  rewrite A_div_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Avgpool3d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Avgpool3d {filernum m1 m2:nat} (k:nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))) :=
  mkvSeq (fun num : fin filernum => mkvSeq (fun i0 : fin (m1/k) =>
    mkvSeq (fun i1 : fin (m2/k) =>
      div (sum (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
        idx (idx (idx input num)
                 (nat2fin (avgpool_index_lt m1 k i0 j0)))
                (nat2fin (avgpool_index_lt m2 k i1 j1)))))))
          (INR (k * k))))).

Definition Avgpool3d_comm {filernum m1 m2:nat} (k:nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))) : comm :=
  mkvSeql (fun num oc => mkvSeql (fun i0 o0 => mkvSeql (fun i1 o1 =>
    suml (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
      idx (idx (idx input num)
               (nat2fin (avgpool_index_lt m1 k i0 j0)))
              (nat2fin (avgpool_index_lt m2 k i1 j1))))))
         (fun r => o1 |:= div r (INR (k * k)))
         o1) o0) oc) output.

Lemma A_Avgpool3d : forall (filernum m1 m2 k : nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))),
  A(output, Avgpool3d k input) = Avgpool3d_comm k input output.
Proof.
  intros. unfold Avgpool3d, Avgpool3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i1.
  rewrite A_div_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Avgpool4d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Avgpool4d {batch filernum m1 m2:nat} (k:nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin filernum =>
    mkvSeq (fun i0 : fin (m1/k) => mkvSeq (fun i1 : fin (m2/k) =>
      div (sum (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
        idx (idx (idx (idx input b) num)
                 (nat2fin (avgpool_index_lt m1 k i0 j0)))
                (nat2fin (avgpool_index_lt m2 k i1 j1)))))))
          (INR (k * k)))))).

Definition Avgpool4d_comm {batch filernum m1 m2:nat} (k:nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun num oc => mkvSeql (fun i0 o0 =>
    mkvSeql (fun i1 o1 =>
      suml (mkvSeq (fun j0 : fin k => sum (mkvSeq (fun j1 : fin k =>
        idx (idx (idx (idx input b) num)
                 (nat2fin (avgpool_index_lt m1 k i0 j0)))
                (nat2fin (avgpool_index_lt m2 k i1 j1))))))
           (fun r => o1 |:= div r (INR (k * k)))
           o1) o0) oc) ob) output.

Lemma A_Avgpool4d : forall (batch filernum m1 m2 k : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))),
  A(output, Avgpool4d k input) = Avgpool4d_comm k input output.
Proof.
  intros. unfold Avgpool4d, Avgpool4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i1.
  rewrite A_div_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* GlobalAvgPool4d                                                            *)
(* -------------------------------------------------------------------------- *)

Definition GlobalAvgPool4d {batch channel m1 m2:nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} num)) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun c : fin channel =>
    div (sum (mkvSeq (fun i : fin m1 => sum (mkvSeq (fun j : fin m2 =>
      idx (idx (idx (idx input b) c) i) j)))))
        (INR (m1 * m2)))).

Definition GlobalAvgPool4d_comm {batch channel m1 m2:nat}
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} num))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun c oc =>
    suml (mkvSeq (fun i : fin m1 => sum (mkvSeq (fun j : fin m2 =>
      idx (idx (idx (idx input b) c) i) j))))
         (fun r => oc |:= div r (INR (m1 * m2)))
         oc) ob) output.

Lemma A_GlobalAvgPool4d : forall (batch channel m1 m2 : nat)
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{channel} num))),
  A(output, GlobalAvgPool4d input) = GlobalAvgPool4d_comm input output.
Proof.
  intros. unfold GlobalAvgPool4d, GlobalAvgPool4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite A_div_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Softmax2d (batch of 1d softaxes)                                           *)
(* -------------------------------------------------------------------------- *)

Definition Softmax2d {batch m:nat}
  (input : exp (ary '{batch} (ary '{m} num)))
  : exp (ary '{batch} (ary '{m} num)) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun j : fin m =>
    div (pExp (idx (idx input b) j))
        (sum (mkvSeq (fun i : fin m => pExp (idx (idx input b) i)))))).

Definition Softmax2d_comm {batch m:nat}
  (input : exp (ary '{batch} (ary '{m} num)))
  (output : acc (ary '{batch} (ary '{m} num))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun j oj =>
    oj |:= div (pExp (idx (idx input b) j))
               (sum (mkvSeq (fun i : fin m => pExp (idx (idx input b) i)))))
    ob) output.

Lemma A_Softmax2d : forall (batch m : nat)
  (input : exp (ary '{batch} (ary '{m} num)))
  (output : acc (ary '{batch} (ary '{m} num))),
  A(output, Softmax2d input) = Softmax2d_comm input output.
Proof.
  intros. unfold Softmax2d, Softmax2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_div_post. simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Softmax3d (single denominator over the whole 3d tensor)                    *)
(* -------------------------------------------------------------------------- *)

Definition Softmax3d {filernum m1 m2:nat}
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i1 : fin filernum => mkvSeq (fun j1 : fin m1 =>
    mkvSeq (fun k1 : fin m2 =>
      div (pExp (idx (idx (idx input i1) j1) k1))
          (sum (mkvSeq (fun i0 : fin filernum =>
             sum (mkvSeq (fun j0 : fin m1 =>
               sum (mkvSeq (fun k0 : fin m2 =>
                 pExp (idx (idx (idx input i0) j0) k0))))))))))).

Definition Softmax3d_comm {filernum m1 m2:nat}
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))) : comm :=
  mkvSeql (fun i1 oi => mkvSeql (fun j1 oj => mkvSeql (fun k1 ok =>
    ok |:= div (pExp (idx (idx (idx input i1) j1) k1))
               (sum (mkvSeq (fun i0 : fin filernum =>
                  sum (mkvSeq (fun j0 : fin m1 =>
                    sum (mkvSeq (fun k0 : fin m2 =>
                      pExp (idx (idx (idx input i0) j0) k0)))))))) )
    oj) oi) output.

Lemma A_Softmax3d : forall (filernum m1 m2 : nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))),
  A(output, Softmax3d input) = Softmax3d_comm input output.
Proof.
  intros. unfold Softmax3d, Softmax3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i1.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j1.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro k1.
  rewrite A_div_post. simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Avgpool2d.
Print Assumptions A_Avgpool3d.
Print Assumptions A_Avgpool4d.
Print Assumptions A_GlobalAvgPool4d.
Print Assumptions A_Softmax2d.
Print Assumptions A_Softmax3d.
