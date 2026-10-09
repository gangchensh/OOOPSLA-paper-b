(* Route-A migration of the pooling / padding / linear operator family from
   Ionia.CNN_OP (Padding2d/3d/4d at lines 250-281, Maxpool2d/4d at 363-381,
   Maxpool3d_pad at 391-398, Linear2d/3d at 415-427) to the R-based
   Proof_CodeGen model, together with their DPIA Leibniz correctness proofs.

   Each operator comes as a triple:
   - a functional definition ([mkvSeq] + [idx], comparisons in Coq [bool]),
   - an imperative counterpart ([*_comm], built from [mkvSeql] / [maxl] /
     [suml] / [If]),
   - a Leibniz equality [A_<op>] proved by the rewrite rules of
     Ionia.DPIA_Rules (all closed with [Qed]).

   Proof shapes:
   - Maxpool2d/4d, Maxpool3d_pad: nested [AmkvSeq] + [A_max_acc]
     (mirror of [A_Maxpool3d] in Ionia.LeNet5_DPIA);
   - Linear2d/3d: nested [AmkvSeq] + [A_add_post] + [C_sum_post_acc]
     (mirror of [A_Linear1d]);
   - Padding2d/3d/4d: nested [AmkvSeq] + the bespoke cell rule [A_pad],
     which turns the proof-carrying [Nat.ltb_spec0] cell expression into the
     boolean [If] cascade of the imperative code (bounds are discharged by
     [Nat.ltb_lt] / [Nat.ltb_ge] / [Nat.leb_le] / [Nat.leb_gt]).

   All array accesses use the explicit [idx]/[idxAcc] functions, because the
   [match ... with | ReflectT ...] construct in the padding cell registers
   ["|"] as a keyword and breaks the [|[ ]]/[|{ }] notations during later
   parsing (cf. Ionia.LeNet5_Functional). *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_Reduce). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* Reuse the window index bound of the reduction family. *)
Require Import Ionia.Ops_Reduce.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Maxpool2d (k x k non-overlapping windows)                                  *)
(* -------------------------------------------------------------------------- *)

Definition Maxpool2d {m1 m2:nat} (k:nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{(m1/k)} (ary '{(m2/k)} num)) :=
  mkvSeq (fun i0 : fin (m1/k) => mkvSeq (fun j0 : fin (m2/k) =>
    max (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
      idx (idx input (nat2fin (avgpool_index_lt m1 k i0 i1)))
              (nat2fin (avgpool_index_lt m2 k j0 j1)))))))).

Definition Maxpool2d_comm {m1 m2:nat} (k:nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{(m1/k)} (ary '{(m2/k)} num))) : comm :=
  mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
    maxl (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
      idx (idx input (nat2fin (avgpool_index_lt m1 k i0 i1)))
              (nat2fin (avgpool_index_lt m2 k j0 j1))))))
         (fun r => o1 |:= r)
         o1) o0) output.

Lemma A_Maxpool2d : forall (m1 m2 k : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{(m1/k)} (ary '{(m2/k)} num))),
  A(output, Maxpool2d k input) = Maxpool2d_comm k input output.
Proof.
  intros. unfold Maxpool2d, Maxpool2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j0.
  rewrite A_max_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool4d (batch + channel dimensions)                                     *)
(* -------------------------------------------------------------------------- *)

Definition Maxpool4d {batch filernum m1 m2:nat} (k:nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun num : fin filernum =>
    mkvSeq (fun i0 : fin (m1/k) => mkvSeq (fun j0 : fin (m2/k) =>
      max (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
        idx (idx (idx (idx input b) num)
                 (nat2fin (avgpool_index_lt m1 k i0 i1)))
                (nat2fin (avgpool_index_lt m2 k j0 j1)))))))))).

Definition Maxpool4d_comm {batch filernum m1 m2:nat} (k:nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun num oc => mkvSeql (fun i0 o0 =>
    mkvSeql (fun j0 o1 =>
      maxl (mkvSeq (fun i1 : fin k => max (mkvSeq (fun j1 : fin k =>
        idx (idx (idx (idx input b) num)
                 (nat2fin (avgpool_index_lt m1 k i0 i1)))
                (nat2fin (avgpool_index_lt m2 k j0 j1))))))
           (fun r => o1 |:= r)
           o1) o0) oc) ob) output.

Lemma A_Maxpool4d : forall (batch filernum m1 m2 k : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))),
  A(output, Maxpool4d k input) = Maxpool4d_comm k input output.
Proof.
  intros. unfold Maxpool4d, Maxpool4d_comm.
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
(* Padding2d (zero padding of width p on both sides of each axis)             *)
(* -------------------------------------------------------------------------- *)

(* Index bound for the unpadded position: [p <= i < p + n] implies
   [i - p < n].  The lower bound is given in the [~ i < p] shape produced by
   the [ReflectF] branch of [Nat.ltb_spec0].  (Route-B counterpart:
   [offset_proof_concise] in CNN_OP.) *)
Lemma pad_offset_lt : forall (i p n : nat), i < p + n -> ~ i < p -> i - p < n.
Proof. intros. lia. Qed.
Arguments pad_offset_lt i p n _ _ : clear implicits.

(* Proof-carrying padding cell: out-of-range positions map to [zero]. *)
Definition pad_expr {n1 n2 : nat}
  (e : exp (ary '{n1} (ary '{n2} num))) (p i j : nat) : exp num :=
  match Nat.ltb_spec0 i p with
  | ReflectT _ _ => zero
  | ReflectF _ H_ge_i =>
    match Nat.ltb_spec0 i (p + n1) with
    | ReflectT _ H_lt_i =>
      match Nat.ltb_spec0 j p with
      | ReflectT _ _ => zero
      | ReflectF _ H_ge_j =>
        match Nat.ltb_spec0 j (p + n2) with
        | ReflectT _ H_lt_j =>
          idx (idx e (nat2fin (pad_offset_lt i p n1 H_lt_i H_ge_i)))
              (nat2fin (pad_offset_lt j p n2 H_lt_j H_ge_j))
        | ReflectF _ _ => zero
        end
      end
    | ReflectF _ _ => zero
    end
  end.

(* Imperative padding cell: the same case split as a cascade of boolean
   [If] commands.  In the innermost (in-bounds) branch the assigned
   expression is [pad_expr] itself, which the case analysis of [A_pad]
   unfolds to the plain in-bounds read. *)
Definition pad_comm {n1 n2 : nat}
  (e : exp (ary '{n1} (ary '{n2} num))) (p i j : nat) (o : acc num) : comm :=
  If (Nat.ltb i p) (o |:= zero)
  (If (Nat.leb (p + n1) i) (o |:= zero)
  (If (Nat.ltb j p) (o |:= zero)
  (If (Nat.leb (p + n2) j) (o |:= zero)
     (o |:= pad_expr e p i j)))).

Lemma A_pad : forall {n1 n2 : nat}
  (e : exp (ary '{n1} (ary '{n2} num))) (p i j : nat) (o : acc num),
  A(o, pad_expr e p i j) = pad_comm e p i j o.
Proof.
  intros n1 n2 e p i j o. unfold pad_comm, pad_expr.
  (* Each [destruct] of a [Nat.ltb_spec0] also substitutes the corresponding
     [Nat.ltb] boolean in [pad_comm]; only the [Nat.leb] conditions need an
     explicit rewrite. *)
  destruct (Nat.ltb_spec0 i p) as [H_i | H_i].
  - (* i < p *)
    reflexivity.
  - (* ~ i < p *)
    destruct (Nat.ltb_spec0 i (p + n1)) as [H_i' | H_i'].
    + (* i < p + n1 *)
      rewrite (proj2 (Nat.leb_gt (p + n1) i) H_i').
      destruct (Nat.ltb_spec0 j p) as [H_j | H_j].
      * (* j < p *)
        reflexivity.
      * (* ~ j < p *)
        destruct (Nat.ltb_spec0 j (p + n2)) as [H_j' | H_j'].
        -- (* j < p + n2: in-bounds read *)
           rewrite (proj2 (Nat.leb_gt (p + n2) j) H_j'). reflexivity.
        -- (* ~ j < p + n2 *)
           assert (Hge_j' : p + n2 <= j) by lia.
           rewrite (proj2 (Nat.leb_le (p + n2) j) Hge_j'). reflexivity.
    + (* ~ i < p + n1 *)
      assert (Hge_i' : p + n1 <= i) by lia.
      rewrite (proj2 (Nat.leb_le (p + n1) i) Hge_i'). reflexivity.
Qed.

Definition Padding2d {n1 n2 : nat} (p : nat)
  (e : exp (ary '{n1} (ary '{n2} num)))
  : exp (ary '{(2*p+n1)} (ary '{(2*p+n2)} num)) :=
  mkvSeq (fun i : fin (2*p+n1) => mkvSeq (fun j : fin (2*p+n2) =>
    pad_expr e p (fin2nat i) (fin2nat j))).

Definition Padding2d_comm {n1 n2 : nat} (p : nat)
  (e : exp (ary '{n1} (ary '{n2} num)))
  (output : acc (ary '{(2*p+n1)} (ary '{(2*p+n2)} num))) : comm :=
  mkvSeql (fun i o0 => mkvSeql (fun j o1 =>
    pad_comm e p (fin2nat i) (fin2nat j) o1) o0) output.

Lemma A_Padding2d : forall (n1 n2 p : nat)
  (e : exp (ary '{n1} (ary '{n2} num)))
  (output : acc (ary '{(2*p+n1)} (ary '{(2*p+n2)} num))),
  A(output, Padding2d p e) = Padding2d_comm p e output.
Proof.
  intros. unfold Padding2d, Padding2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  apply A_pad.
Qed.

(* -------------------------------------------------------------------------- *)
(* Padding3d (channel dimension preserved)                                    *)
(* -------------------------------------------------------------------------- *)

Definition Padding3d {channel n1 n2 : nat} (p : nat)
  (e : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  : exp (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num))) :=
  mkvSeq (fun c : fin channel => Padding2d p (idx e c)).

Definition Padding3d_comm {channel n1 n2 : nat} (p : nat)
  (e : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (output : acc (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num)))) : comm :=
  mkvSeql (fun c oc => Padding2d_comm p (idx e c) oc) output.

Lemma A_Padding3d : forall (channel n1 n2 p : nat)
  (e : exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (output : acc (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num)))),
  A(output, Padding3d p e) = Padding3d_comm p e output.
Proof.
  intros. unfold Padding3d, Padding3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  apply A_Padding2d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Padding4d (batch + channel dimensions preserved)                           *)
(* -------------------------------------------------------------------------- *)

Definition Padding4d {batch channel n1 n2 : nat} (p : nat)
  (e : exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num)))) :=
  mkvSeq (fun b : fin batch => Padding3d p (idx e b)).

Definition Padding4d_comm {batch channel n1 n2 : nat} (p : nat)
  (e : exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num))))) : comm :=
  mkvSeql (fun b ob => Padding3d_comm p (idx e b) ob) output.

Lemma A_Padding4d : forall (batch channel n1 n2 p : nat)
  (e : exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (output : acc (ary '{batch} (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num))))),
  A(output, Padding4d p e) = Padding4d_comm p e output.
Proof.
  intros. unfold Padding4d, Padding4d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  apply A_Padding3d.
Qed.

(* -------------------------------------------------------------------------- *)
(* Maxpool3d_pad (padded input, general kernel/stride, R-model)               *)
(* -------------------------------------------------------------------------- *)

(* Runtime-safe indexing with [exp_default] for out-of-bound positions
   (R-model counterpart of [safe_idx_nat] in Ionia.CNN_Defs). *)
Definition safe_idx_nat {n:nat} {t:data} (e : exp (ary '{n} t)) (i : nat)
  : exp t :=
  match Nat.ltb_spec0 i n with
  | ReflectT _ H => idx e (nat2fin H)
  | ReflectF _ _ => exp_default t
  end.

Definition Maxpool3d_pad {filernum m1 m2 : nat} (kersize stride padding : nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{filernum}
        (ary '{((m1 - kersize + 2*padding)/stride + 1)}
        (ary '{((m2 - kersize + 2*padding)/stride + 1)} num))) :=
  tlet pad := Padding3d padding input in
  mkvSeq (fun num : fin filernum =>
    mkvSeq (fun i0 : fin ((m1 - kersize + 2*padding)/stride + 1) =>
      mkvSeq (fun j0 : fin ((m2 - kersize + 2*padding)/stride + 1) =>
        max (mkvSeq (fun i1 : fin kersize => max (mkvSeq (fun j1 : fin kersize =>
          safe_idx_nat
            (safe_idx_nat (idx pad num)
                          (fin2nat i0 * stride + fin2nat i1))
            (fin2nat j0 * stride + fin2nat j1)))))))).

Definition Maxpool3d_pad_comm {filernum m1 m2 : nat} (kersize stride padding : nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum}
        (ary '{((m1 - kersize + 2*padding)/stride + 1)}
        (ary '{((m2 - kersize + 2*padding)/stride + 1)} num)))) : comm :=
  mkvSeql (fun num oc => mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
    maxl (mkvSeq (fun i1 : fin kersize => max (mkvSeq (fun j1 : fin kersize =>
      safe_idx_nat
        (safe_idx_nat (idx (Padding3d padding input) num)
                      (fin2nat i0 * stride + fin2nat i1))
        (fin2nat j0 * stride + fin2nat j1)))))
         (fun r => o1 |:= r)
         o1) o0) oc) output.

Lemma A_Maxpool3d_pad : forall (filernum m1 m2 kersize stride padding : nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum}
        (ary '{((m1 - kersize + 2*padding)/stride + 1)}
        (ary '{((m2 - kersize + 2*padding)/stride + 1)} num)))),
  A(output, Maxpool3d_pad kersize stride padding input)
  = Maxpool3d_pad_comm kersize stride padding input output.
Proof.
  intros. unfold Maxpool3d_pad, Maxpool3d_pad_comm, let_binding. cbv beta.
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
(* Linear2d (batch of 1d linear layers)                                       *)
(* -------------------------------------------------------------------------- *)

Definition Linear2d {batch m outnum:nat}
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{batch} (ary '{m} num)))
  : exp (ary '{batch} (ary '{outnum} num)) :=
  mkvSeq (fun b : fin batch => mkvSeq (fun out : fin outnum =>
    add (sum (mkvSeq (fun i : fin m =>
      mul (idx (idx input b) i) (idx (idx w out) i))))
        (idx bias out))).

Definition Linear2d_comm {batch m outnum:nat}
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{batch} (ary '{m} num)))
  (output : acc (ary '{batch} (ary '{outnum} num))) : comm :=
  mkvSeql (fun b ob => mkvSeql (fun out oout =>
    suml (mkvSeq (fun i : fin m =>
      mul (idx (idx input b) i) (idx (idx w out) i)))
         (fun r => oout |:= add r (idx bias out))
         oout) ob) output.

Lemma A_Linear2d : forall (batch m outnum : nat)
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{batch} (ary '{m} num)))
  (output : acc (ary '{batch} (ary '{outnum} num))),
  A(output, Linear2d w bias input) = Linear2d_comm w bias input output.
Proof.
  intros. unfold Linear2d, Linear2d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro b.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro out.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Linear3d (per-position linear over the last axis)                          *)
(* -------------------------------------------------------------------------- *)

Definition Linear3d {c m1 m2 n : nat}
  (input : exp (ary '{c} (ary '{m1} (ary '{m2} num))))
  (w : exp (ary '{n} (ary '{m2} num)))
  (bias : exp (ary '{n} num))
  : exp (ary '{c} (ary '{m1} (ary '{n} num))) :=
  mkvSeq (fun o : fin c => mkvSeq (fun i : fin m1 => mkvSeq (fun j : fin n =>
    add (sum (mkvSeq (fun k : fin m2 =>
      mul (idx (idx (idx input o) i) k) (idx (idx w j) k))))
        (idx bias j)))).

Definition Linear3d_comm {c m1 m2 n : nat}
  (input : exp (ary '{c} (ary '{m1} (ary '{m2} num))))
  (w : exp (ary '{n} (ary '{m2} num)))
  (bias : exp (ary '{n} num))
  (output : acc (ary '{c} (ary '{m1} (ary '{n} num)))) : comm :=
  mkvSeql (fun o oc => mkvSeql (fun i oi => mkvSeql (fun j oj =>
    suml (mkvSeq (fun k : fin m2 =>
      mul (idx (idx (idx input o) i) k) (idx (idx w j) k)))
         (fun r => oj |:= add r (idx bias j))
         oj) oi) oc) output.

Lemma A_Linear3d : forall (c m1 m2 n : nat)
  (input : exp (ary '{c} (ary '{m1} (ary '{m2} num))))
  (w : exp (ary '{n} (ary '{m2} num)))
  (bias : exp (ary '{n} num))
  (output : acc (ary '{c} (ary '{m1} (ary '{n} num)))),
  A(output, Linear3d input w bias) = Linear3d_comm input w bias output.
Proof.
  intros. unfold Linear3d, Linear3d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro o.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro j.
  rewrite A_add_post.
  rewrite C_sum_post_acc.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_Maxpool2d.
Print Assumptions A_Maxpool4d.
Print Assumptions A_Padding2d.
Print Assumptions A_Padding3d.
Print Assumptions A_Padding4d.
Print Assumptions A_Maxpool3d_pad.
Print Assumptions A_Linear2d.
Print Assumptions A_Linear3d.
