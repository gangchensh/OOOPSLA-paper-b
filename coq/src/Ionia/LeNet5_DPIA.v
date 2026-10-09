(* DPIA-style Leibniz equivalence proofs for R-based LeNet-5 operators.

   All array accesses are written with the explicit [idx]/[idxAcc] functions,
   because the [match ... with | ReflectT ...] construct in
   [Ionia.LeNet5_Utils] makes the [|] token a keyword and breaks the
   [|[ ]]/[|{ }] notations in later parsing. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.LeNet5_Imperative.
From Stdlib Require Import Lia.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* ReLU equivalences                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma A_ReLU1d : forall (n:nat) (input : exp (ary '{n} num)) (output : acc (ary '{n} num)),
  A(output, ReLU1d input) = ReLU1d_comm input output.
Proof.
  intros. unfold ReLU1d, ReLU1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

Lemma A_ReLU2d : forall (m1 m2:nat) (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))),
  A(output, ReLU2d input) = ReLU2d_comm input output.
Proof.
  intros. unfold ReLU2d, ReLU2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i1.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

Lemma A_ReLU3d : forall (filernum m1 m2:nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))),
  A(output, ReLU3d input) = ReLU3d_comm input output.
Proof.
  intros. unfold ReLU3d, ReLU3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro num.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i1.
  rewrite Aif1. rewrite A_num. rewrite A_num.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Flatten3d equivalence                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma A_Flatten3d : forall (channel m1 m2 : nat)
  (Hchannel : channel > 0) (Hm1 : m1 > 0) (Hm2 : m2 > 0)
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{channel * m1 * m2} num)),
  A(output, Flatten3d input) = Flatten3d_comm input output.
Proof.
  intros. unfold Flatten3d, Flatten3d_comm, A.
  rewrite assign_ary.
  apply seqfor_extensionality. intro x.
  simpl. rewrite idx_mkvSeq.
  2: {
    apply Nat.mul_pos_pos.
    - apply Nat.mul_pos_pos; assumption.
    - assumption.
  }
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Linear1d equivalence                                                       *)
(* -------------------------------------------------------------------------- *)

Lemma A_Linear1d : forall (m outnum : nat)
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{m} num))
  (output : acc (ary '{outnum} num)),
  A(output, Linear1d w bias input) = Linear1d_comm w bias input output.
Proof.
  intros. unfold Linear1d, Linear1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro out.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool3d equivalence                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma A_Maxpool3d : forall (channel m : nat)
  (input : exp (ary '{channel} (ary '{m} (ary '{m} num))))
  (output : acc (ary '{channel} (ary '{(m/2)} (ary '{(m/2)} num)))),
  A(output, Maxpool3d input) = Maxpool3d_comm input output.
Proof.
  intros. unfold Maxpool3d, Maxpool3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_max_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Softmax1d equivalence                                                      *)
(* -------------------------------------------------------------------------- *)

Lemma A_Softmax1d : forall (n:nat)
  (input : exp (ary '{n} num))
  (output : acc (ary '{n} num)),
  A(output, Softmax1d input) = Softmax1d_comm input output.
Proof.
  intros. unfold Softmax1d, Softmax1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite A_div_post. simpl. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Conv3d equivalence                                                         *)
(* -------------------------------------------------------------------------- *)

Lemma A_Conv3d : forall (h w ic oc k p : nat) (Hk : k > 0)
  (kernel : exp (ary '{oc} (ary '{ic} (ary '{k} (ary '{k} num)))))
  (bias : exp (ary '{oc} num))
  (input : exp (ary '{ic} (ary '{h} (ary '{w} num))))
  (output : acc (ary '{oc} (ary '{(h + 2 * p - k + 1)} (ary '{(w + 2 * p - k + 1)} num)))),
  A(output, Conv3d Hk kernel bias input) = Conv3d_comm Hk kernel bias input output.
Proof.
  intros. unfold Conv3d, Conv3d_comm, Conv3dCell, Conv3dCell_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro cout.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* End-to-end LeNet-5 statement                                               *)
(* -------------------------------------------------------------------------- *)

From Stdlib Require Import String.
Open Scope string_scope.

(* Intermediate accumulator paths used by [lenet5_comm]. *)
Definition l1_acc : acc (ary '{6} (ary '{28} (ary '{28} num))) := acc' (Var "l1").
Definition l2_acc : acc (ary '{6} (ary '{14} (ary '{14} num))) := acc' (Var "l2").
Definition l3_acc : acc (ary '{16} (ary '{10} (ary '{10} num))) := acc' (Var "l3").
Definition l4_acc : acc (ary '{16} (ary '{5} (ary '{5} num))) := acc' (Var "l4").
Definition l5_acc : acc (ary '{400} num) := acc' (Var "l5").
Definition l6_acc : acc (ary '{120} num) := acc' (Var "l6").
Definition l7_acc : acc (ary '{84} num) := acc' (Var "l7").

(* Freshness: all temporary buffers are undefined in the incoming environment
   and their paths do not overlap the final output accumulator. *)
Definition lenet5_fresh
  (output : acc (ary '{10} num)) (rho : env) : Prop :=
  StructUndefined l1_acc rho /\
  StructUndefined l2_acc rho /\
  StructUndefined l3_acc rho /\
  StructUndefined l4_acc rho /\
  StructUndefined l5_acc rho /\
  StructUndefined l6_acc rho /\
  StructUndefined l7_acc rho /\
  (forall p, in_acc p output -> ~ in_acc p l1_acc) /\
  (forall p, in_acc p output -> ~ in_acc p l2_acc) /\
  (forall p, in_acc p output -> ~ in_acc p l3_acc) /\
  (forall p, in_acc p output -> ~ in_acc p l4_acc) /\
  (forall p, in_acc p output -> ~ in_acc p l5_acc) /\
  (forall p, in_acc p output -> ~ in_acc p l6_acc) /\
  (forall p, in_acc p output -> ~ in_acc p l7_acc).

(* Direct imperative program: every [bind_read] is replaced by the functional
   value of the previous layer.  This is the canonical DPIA-normal form of
   [lenet5_comm]. *)
Definition lenet5_comm_direct
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
  (output : acc (ary '{10} num))
  : comm :=
  let l1_e := ReLU3d (Conv3d (p:=2) H5 c1_w c1_b input) in
  let l2_e := Maxpool3d l1_e in
  let l3_e := ReLU3d (Conv3d (p:=0) H5 c3_w c3_b l2_e) in
  let l4_e := Maxpool3d l3_e in
  let l5_e := Flatten3d l4_e in
  let l6_e := ReLU1d (Linear1d f5_w f5_b l5_e) in
  let l7_e := ReLU1d (Linear1d f6_w f6_b l6_e) in
  let out_e := Softmax1d (Linear1d out_w out_b l7_e) in
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
                              (A(output, out_e)))
                            (acc' (Var "l7")))
                          ) (acc' (Var "l6")))
                      ) (acc' (Var "l5")))
                  ) (acc' (Var "l4")))
              ) (acc' (Var "l3")))
          ) (acc' (Var "l2")))
      ) (acc' (Var "l1")).

(* The direct form collapses to [A(output, LeNet5 ...)] when the output path
   is observed, because every temporary is fresh and disjoint from [output]. *)

Lemma A_LeNet5_direct :
  forall (input : exp (ary '{1} (ary '{28} (ary '{28} num))))
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
    (output : acc (ary '{10} num))
    (rho : env) (p : path),
  in_acc p output ->
  lenet5_fresh output rho ->
  lenet5_comm_direct input c1_w c1_b c3_w c3_b f5_w f5_b f6_w f6_b out_w out_b output rho p =
  A(output, LeNet5 input c1_w c1_b c3_w c3_b f5_w f5_b f6_w f6_b out_w out_b) rho p.
Proof.
  intros. unfold lenet5_comm_direct, LeNet5, new, A. cbv zeta beta.
  etransitivity.
  - apply assign_pure_independent with (rho2 := rho). apply H.
  - reflexivity.
Qed.

(* The original [lenet5_comm] and the direct form are equal as commands. *)

(* Helper: after assigning [e] to [acc' p], a subsequent [bind_read (acc' p)]
   can be replaced by the direct value [e]. *)
Lemma bind_read_replace :
  forall (d_in : data) (p : path) (e : exp d_in)
    (k : exp d_in -> comm),
  seq (A(acc' p, e)) (bind_read (acc' p) k) =
  seq (A(acc' p, e)) (k e).
Proof.
  intros. unfold seq, bind_read, A.
  fun_ext.
  rewrite read_exp_assign. reflexivity.
Qed.

(* Variant when the [bind_read] is followed by a continuation [c]. *)
Lemma bind_read_replace_seq :
  forall (d_in : data) (p : path) (e : exp d_in)
    (k : exp d_in -> comm) (c : comm),
  seq (A(acc' p, e)) (seq (bind_read (acc' p) k) c) =
  seq (A(acc' p, e)) (seq (k e) c).
Proof.
  intros. unfold seq, bind_read, A.
  fun_ext.
  rewrite read_exp_assign. reflexivity.
Qed.

Lemma lenet5_comm_eq_direct :
  forall (input : exp (ary '{1} (ary '{28} (ary '{28} num))))
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
    (output : acc (ary '{10} num)),
  lenet5_comm input c1_w c1_b c3_w c3_b f5_w f5_b f6_w f6_b out_w out_b output =
  lenet5_comm_direct input c1_w c1_b c3_w c3_b f5_w f5_b f6_w f6_b out_w out_b output.
Proof.
  intros.
  unfold lenet5_comm, lenet5_comm_direct, new.
  cbv zeta beta.
  rewrite <- A_ReLU3d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool3d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU3d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Maxpool3d.
  rewrite bind_read_replace_seq.
  rewrite <- A_Flatten3d with (channel := 16) (m1 := 5) (m2 := 5).
  all: try lia.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU1d.
  rewrite bind_read_replace_seq.
  rewrite <- A_ReLU1d.
  rewrite bind_read_replace.
  rewrite <- A_Softmax1d.
  all: try lia.
  reflexivity.
Qed.

Theorem A_LeNet5 :
  forall (input : exp (ary '{1} (ary '{28} (ary '{28} num))))
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
    (output : acc (ary '{10} num))
    (rho : env) (p : path),
  in_acc p output ->
  lenet5_fresh output rho ->
  lenet5_comm input c1_w c1_b c3_w c3_b f5_w f5_b f6_w f6_b out_w out_b output rho p =
  A(output, LeNet5 input c1_w c1_b c3_w c3_b f5_w f5_b f6_w f6_b out_w out_b) rho p.
Proof.
  intros. rewrite lenet5_comm_eq_direct. apply A_LeNet5_direct; assumption.
Qed.
