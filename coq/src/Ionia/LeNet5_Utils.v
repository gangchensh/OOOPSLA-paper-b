(* Utility lemmas and safe indexing for the LeNet-5 DPIA proof. *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
From Stdlib Require Import Lia.

Set Implicit Arguments.

(* Runtime-safe 2D indexing with zero padding for out-of-bound positions. *)
Definition safe_idx2d {h w : nat} (img : exp (ary '{h} (ary '{w} num))) (i j : nat)
  : exp num :=
  match Nat.ltb_spec0 i h with
  | ReflectT _ Hi =>
      match Nat.ltb_spec0 j w with
      | ReflectT _ Hj => img|[nat2fin Hi]|[nat2fin Hj]
      | ReflectF _ _ => zero
      end
  | ReflectF _ _ => zero
  end.

Lemma conv_flat_c_bound : forall (ic k : nat) (flat : fin (ic * k * k)) (Hk : k > 0),
  Nat.div (fin2nat flat) (k * k) < ic.
Proof.
  intros. destruct flat as [f Hf]. simpl.
  apply Nat.div_lt_upper_bound. nia.
  rewrite Nat.mul_comm. nia.
Qed.

Lemma conv_flat_di_bound : forall (ic k : nat) (flat : fin (ic * k * k)) (Hk : k > 0),
  Nat.div (Nat.modulo (fin2nat flat) (k * k)) k < k.
Proof.
  intros. destruct flat as [f Hf]. simpl.
  apply Nat.div_lt_upper_bound. lia.
  apply Nat.mod_upper_bound. nia.
Qed.

Lemma conv_flat_dj_bound : forall (ic k : nat) (flat : fin (ic * k * k)) (Hk : k > 0),
  Nat.modulo (fin2nat flat) k < k.
Proof.
  intros. destruct flat as [f Hf]. simpl.
  apply Nat.mod_upper_bound. lia.
Qed.

(* Make the input-channel parameter implicit so that the convolution
   indexing lemmas can be used in the form [nat2fin (conv_flat_*_bound flat Hk)]. *)
Arguments conv_flat_c_bound {ic} [k] flat Hk.
Arguments conv_flat_di_bound {ic} [k] flat Hk.
Arguments conv_flat_dj_bound {ic} [k] flat Hk.
