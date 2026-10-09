(* TextCNN (Kim 2014) end-to-end DPIA proof — milestone N1b of the NLP/LLM
   extension plan (doc/NLP与LLM扩展开发规划_20260911.md), in the route-A
   R-based expression model.

   Pipeline (all sizes symbolic: sequence T, embedding de, filters F per
   kernel width, classes nc):

     three parallel Conv1d branches (kernel widths 3/4/5, bias, ReLU)
       -> max-over-time pooling per branch      (F features each)
       -> Concat1d3 of the three feature maps   ((F+F)+F features)
       -> Linear1d fully-connected layer        (nc logits)
       -> Softmax1d.

   New operators proved here (functional + imperative + A-rule, all Qed):
   - [TextConv1dCell] / [TextConv1dBranch]: 1d convolution over the
     embedding sequence, reusing [pad_idx2d] (Ionia.Ops_Conv) for the
     boundary-safe read — no fin bound lemmas needed; ReLU folded into the
     cell ([relu1]);
   - [MaxOverTime]: per-filter max over the time axis, via the [maxl]
     reduction skeleton ([A_max_acc]);
   - [Concat1d] / [Concat1d3]: 1d analogues of [Concat4d]/[Concat4d4]
     (Ionia.Ops_Concat), reusing [concat_split_lt].

   The end-to-end theorem [A_TextCNN] follows the GoogLeNet inception
   pattern (Ionia.GoogLeNet_DPIA): parallel branches bind their results
   with [bind_read] right after each branch completes, and the bound
   values are carried in the continuation closure to the concat.  The
   direct form assigns each opaque intermediate (tc_c3 .. tc_soft) to a
   fresh buffer; the final theorem observes the network at an output path
   under freshness of the temporaries. *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* [pad_idx2d] for the boundary-safe 1d window read. *)
Require Import Ionia.Ops_Conv.
(* [concat_split_lt] for the concat index split. *)
Require Import Ionia.Ops_Concat.
(* [bind_read] and the bind_read elimination lemmas; [Linear1d]/[Softmax1d]. *)
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Scalar ReLU                                                                 *)
(* -------------------------------------------------------------------------- *)

Definition relu1 (r : exp num) : exp num :=
  if leExp r zero then zero else r.

Lemma A_relu1 : forall (a : acc num) (e : exp num),
  A(a, relu1 e) = C(e, fun r => a |:= relu1 r).
Proof. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Conv1d branch: F filters of width k over a T x de embedding sequence        *)
(* (the window read reuses [pad_idx2d] with padding 0: in-range by            *)
(* construction, the guard never fires)                                        *)
(* -------------------------------------------------------------------------- *)

(* Single filter w (k x de), bias b, output position i:
   relu(b + sum_{j<k} sum_{dd<de} x[i+j, dd] * w[j, dd]). *)
Definition TextConv1dCell {T de k : nat}
  (w : exp (ary '{k} (ary '{de} num))) (b : exp num)
  (x : exp (ary '{T} (ary '{de} num)))
  (i : fin (T - k + 1)) : exp num :=
  let s : exp num := sum (mkvSeq (fun j : fin k =>
    sum (mkvSeq (fun dd : fin de =>
      mul (pad_idx2d 0 x (fin2nat i + fin2nat j) (fin2nat dd))
          (idx (idx w j) dd))))) in
  relu1 (add s b).

Definition TextConv1dCell_comm {T de k : nat}
  (w : exp (ary '{k} (ary '{de} num))) (b : exp num)
  (x : exp (ary '{T} (ary '{de} num)))
  (i : fin (T - k + 1)) (o : acc num) : comm :=
  suml (mkvSeq (fun j : fin k => sum (mkvSeq (fun dd : fin de =>
    mul (pad_idx2d 0 x (fin2nat i + fin2nat j) (fin2nat dd))
        (idx (idx w j) dd)))))
       (fun r : exp num => o |:= relu1 (add r b)) o.

Lemma A_TextConv1dCell : forall (T de k : nat)
  (w : exp (ary '{k} (ary '{de} num))) (b : exp num)
  (x : exp (ary '{T} (ary '{de} num)))
  (i : fin (T - k + 1)) (o : acc num),
  A(o, TextConv1dCell w b x i) = TextConv1dCell_comm w b x i o.
Proof.
  intros. unfold TextConv1dCell, TextConv1dCell_comm.
  (* abstract the summand array so the C-rule shape is syntactically clear *)
  assert (Hstep : forall (S0 : exp (ary '{k} num)) (b0 : exp num),
    A(o, relu1 (add (sum S0) b0)) = suml S0 (fun r : exp num => o |:= relu1 (add r b0)) o).
  { intros S0 b0.
    replace (A(o, relu1 (add (sum S0) b0)))
      with (C(sum S0, fun r : exp num => o |:= relu1 (add r b0))) by reflexivity.
    rewrite C_sum_post_acc. reflexivity. }
  apply Hstep.
Qed.

Definition TextConv1dBranch {T de k F : nat}
  (w : exp (ary '{F} (ary '{k} (ary '{de} num)))) (b : exp (ary '{F} num))
  (x : exp (ary '{T} (ary '{de} num)))
  : exp (ary '{F} (ary '{T - k + 1} num)) :=
  mkvSeq (fun f : fin F => mkvSeq (fun i : fin (T - k + 1) =>
    TextConv1dCell (idx w f) (idx b f) x i)).

Definition TextConv1dBranch_comm {T de k F : nat}
  (w : exp (ary '{F} (ary '{k} (ary '{de} num)))) (b : exp (ary '{F} num))
  (x : exp (ary '{T} (ary '{de} num)))
  (out : acc (ary '{F} (ary '{T - k + 1} num))) : comm :=
  mkvSeql (fun f of => mkvSeql (fun i oi =>
    TextConv1dCell_comm (idx w f) (idx b f) x i oi) of) out.

Lemma A_TextConv1dBranch : forall (T de k F : nat)
  (w : exp (ary '{F} (ary '{k} (ary '{de} num)))) (b : exp (ary '{F} num))
  (x : exp (ary '{T} (ary '{de} num)))
  (out : acc (ary '{F} (ary '{T - k + 1} num))),
  A(out, TextConv1dBranch w b x) = TextConv1dBranch_comm w b x out.
Proof.
  intros. unfold TextConv1dBranch, TextConv1dBranch_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro f.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro i.
  apply A_TextConv1dCell.
Qed.

(* -------------------------------------------------------------------------- *)
(* Max-over-time pooling: per-filter max over the time axis                    *)
(* -------------------------------------------------------------------------- *)

Definition MaxOverTime {F L : nat} (fm : exp (ary '{F} (ary '{L} num)))
  : exp (ary '{F} num) :=
  mkvSeq (fun f : fin F => max (idx fm f)).

Definition MaxOverTime_comm {F L : nat} (fm : exp (ary '{F} (ary '{L} num)))
  (out : acc (ary '{F} num)) : comm :=
  seqfor (fun f : fin F => maxl (idx fm f) (fun r => (out|{f}) |:= r) (out|{f})).

Lemma A_MaxOverTime : forall (F L : nat)
  (fm : exp (ary '{F} (ary '{L} num))) (out : acc (ary '{F} num)),
  A(out, MaxOverTime fm) = MaxOverTime_comm fm out.
Proof.
  intros. unfold MaxOverTime, MaxOverTime_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro f.
  rewrite A_max_acc. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Concat1d / Concat1d3 (1d analogues of Concat4d / Concat4d4)                 *)
(* -------------------------------------------------------------------------- *)

Definition Concat1dCell {c1 c2 : nat}
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num)) (c : fin (c1 + c2))
  : exp num :=
  match Nat.ltb_spec0 (fin2nat c) c1 with
  | ReflectT _ Hlt => idx x (nat2fin Hlt)
  | ReflectF _ Hge =>
      idx y (nat2fin (concat_split_lt (fin2nat c) c1 c2 Hge (fin_proof c)))
  end.

(* Index lemmas for the cell: below c1 read left, at/above c1 read right
   with offset.  (The [Nat.ltb_spec0] match is eliminated by destructing
   the spec after [set]; the hypotheses discharge the impossible branch.) *)
Lemma Concat1dCell_left : forall (c1 c2 : nat)
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num)) (i : fin c1) (c : fin (c1 + c2)),
  fin2nat c = fin2nat i ->
  Concat1dCell x y c = idx x i.
Proof.
  intros c1 c2 x y i c He. unfold Concat1dCell.
  set (s := Nat.ltb_spec0 (fin2nat c) c1).
  assert (Hs : fin2nat c < c1) by (pose proof (fin_proof i); lia).
  destruct s as [Hlt | Hge].
  - f_equal. apply fin2nat_inj. rewrite fin2nat_nat2fin. exact He.
  - exfalso. lia.
Qed.

Lemma Concat1dCell_right : forall (c1 c2 : nat)
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num)) (i : fin c2) (c : fin (c1 + c2)),
  fin2nat c = fin2nat i + c1 ->
  Concat1dCell x y c = idx y i.
Proof.
  intros c1 c2 x y i c He. unfold Concat1dCell.
  set (s := Nat.ltb_spec0 (fin2nat c) c1).
  assert (Hs : ~ fin2nat c < c1) by (pose proof (fin_proof i); lia).
  destruct s as [Hlt | Hge].
  - exfalso. lia.
  - f_equal. apply fin2nat_inj. rewrite fin2nat_nat2fin.
    pose proof (fin_proof i). lia.
Qed.

Definition Concat1d {c1 c2 : nat}
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num))
  : exp (ary '{(c1 + c2)} num) :=
  mkvSeq (Concat1dCell x y).

Definition Concat1d_comm {c1 c2 : nat}
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num))
  (output : acc (ary '{(c1 + c2)} num)) : comm :=
  seqfor (fun c : fin (c1 + c2) => (output|{c}) |:= Concat1dCell x y c).

Lemma A_Concat1d : forall (c1 c2 : nat)
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num))
  (output : acc (ary '{(c1 + c2)} num)),
  A(output, Concat1d x y) = Concat1d_comm x y output.
Proof.
  intros. unfold Concat1d, Concat1d_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro c.
  rewrite A_num. reflexivity.
Qed.

(* Three-way concat as nested two-way concat ((c1+c2)+c3). *)
Definition Concat1d3 {c1 c2 c3 : nat}
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num)) (z : exp (ary '{c3} num))
  : exp (ary '{(c1 + c2) + c3} num) :=
  Concat1d (Concat1d x y) z.

Definition Concat1d3_comm {c1 c2 c3 : nat}
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num)) (z : exp (ary '{c3} num))
  (output : acc (ary '{(c1 + c2) + c3} num)) : comm :=
  Concat1d_comm (Concat1d x y) z output.

Lemma A_Concat1d3 : forall (c1 c2 c3 : nat)
  (x : exp (ary '{c1} num)) (y : exp (ary '{c2} num)) (z : exp (ary '{c3} num))
  (output : acc (ary '{(c1 + c2) + c3} num)),
  A(output, Concat1d3 x y z) = Concat1d3_comm x y z output.
Proof.
  intros. unfold Concat1d3, Concat1d3_comm. apply A_Concat1d.
Qed.

(* -------------------------------------------------------------------------- *)
(* TextCNN network                                                             *)
(* -------------------------------------------------------------------------- *)

Section TextCNNNet.

  Context (T de F nc : nat).

  (* Conv branch parameters: F filters of width 3 / 4 / 5 (+ biases), the
     fully-connected layer over the (F+F)+F pooled features, and the input
     embedding sequence. *)
  Context (w3 : exp (ary '{F} (ary '{3} (ary '{de} num)))) (b3 : exp (ary '{F} num))
          (w4 : exp (ary '{F} (ary '{4} (ary '{de} num)))) (b4 : exp (ary '{F} num))
          (w5 : exp (ary '{F} (ary '{5} (ary '{de} num)))) (b5 : exp (ary '{F} num))
          (wfc : exp (ary '{nc} (ary '{(F + F) + F} num))) (bfc : exp (ary '{nc} num))
          (input : exp (ary '{T} (ary '{de} num))).

  (* ---------------- Functional network (opaque stage wrappers) ---------- *)

  Definition tc_c3 := @TextConv1dBranch T de 3 F w3 b3 input.
  Definition tc_m3 := MaxOverTime tc_c3.
  Definition tc_c4 := @TextConv1dBranch T de 4 F w4 b4 input.
  Definition tc_m4 := MaxOverTime tc_c4.
  Definition tc_c5 := @TextConv1dBranch T de 5 F w5 b5 input.
  Definition tc_m5 := MaxOverTime tc_c5.
  Definition tc_feat := Concat1d3 tc_m3 tc_m4 tc_m5.
  Definition tc_logit := Linear1d wfc bfc tc_feat.
  Definition tc_soft := Softmax1d tc_logit.

  Lemma tc_c3_body : tc_c3 = @TextConv1dBranch T de 3 F w3 b3 input.
  Proof. reflexivity. Qed.
  Lemma tc_m3_body : tc_m3 = MaxOverTime tc_c3. Proof. reflexivity. Qed.
  Lemma tc_c4_body : tc_c4 = @TextConv1dBranch T de 4 F w4 b4 input.
  Proof. reflexivity. Qed.
  Lemma tc_m4_body : tc_m4 = MaxOverTime tc_c4. Proof. reflexivity. Qed.
  Lemma tc_c5_body : tc_c5 = @TextConv1dBranch T de 5 F w5 b5 input.
  Proof. reflexivity. Qed.
  Lemma tc_m5_body : tc_m5 = MaxOverTime tc_c5. Proof. reflexivity. Qed.
  Lemma tc_feat_body : tc_feat = Concat1d3 tc_m3 tc_m4 tc_m5. Proof. reflexivity. Qed.
  Lemma tc_logit_body : tc_logit = Linear1d wfc bfc tc_feat. Proof. reflexivity. Qed.
  Lemma tc_soft_body : tc_soft = Softmax1d tc_logit. Proof. reflexivity. Qed.

  Opaque tc_c3 tc_m3 tc_c4 tc_m4 tc_c5 tc_m5 tc_feat tc_logit tc_soft.

  Definition TextCNN : exp (ary '{nc} num) := tc_soft.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  (* Parallel branches bind their results with [bind_read] right after each
     branch completes (the GoogLeNet inception pattern); the bound values
     o3/o4/o5 are carried in the continuation closure to the concat. *)
  Definition textcnn_comm (output : acc (ary '{nc} num)) : comm :=
new (fun tc3 => TextConv1dBranch_comm w3 b3 input tc3 ';
new (fun tm3 => bind_read tc3 (fun e3 => MaxOverTime_comm e3 tm3) ';
bind_read tm3 (fun o3 =>
new (fun tc4 => TextConv1dBranch_comm w4 b4 input tc4 ';
new (fun tm4 => bind_read tc4 (fun e4 => MaxOverTime_comm e4 tm4) ';
bind_read tm4 (fun o4 =>
new (fun tc5 => TextConv1dBranch_comm w5 b5 input tc5 ';
new (fun tm5 => bind_read tc5 (fun e5 => MaxOverTime_comm e5 tm5) ';
bind_read tm5 (fun o5 =>
new (fun tcf => Concat1d3_comm o3 o4 o5 tcf ';
new (fun tcl => bind_read tcf (fun ef => Linear1d_comm wfc bfc ef tcl) ';
bind_read tcl (fun el => Softmax1d_comm el output)
) (acc' (Var "tcl"))
) (acc' (Var "tcf"))
)) (acc' (Var "tm5"))
) (acc' (Var "tc5"))
)) (acc' (Var "tm4"))
) (acc' (Var "tc4"))
)) (acc' (Var "tm3"))
) (acc' (Var "tc3")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition textcnn_direct (output : acc (ary '{nc} num)) : comm :=
    A(acc' (Var "tc3"), tc_c3) ';
    A(acc' (Var "tm3"), tc_m3) ';
    A(acc' (Var "tc4"), tc_c4) ';
    A(acc' (Var "tm4"), tc_m4) ';
    A(acc' (Var "tc5"), tc_c5) ';
    A(acc' (Var "tm5"), tc_m5) ';
    A(acc' (Var "tcf"), tc_feat) ';
    A(acc' (Var "tcl"), tc_logit) ';
    A(output, tc_soft).

  (* ---------------- Freshness ------------------------------------------- *)

  (* All temporary buffers are undefined in the incoming environment and do
     not overlap the final output. *)
  Definition textcnn_fresh (output : acc (ary '{nc} num)) (rho : env) : Prop :=
    StructUndefined (acc' (Var "tc3") : acc (ary '{F} (ary '{T - 3 + 1} num))) rho /\
    StructUndefined (acc' (Var "tm3") : acc (ary '{F} num)) rho /\
    StructUndefined (acc' (Var "tc4") : acc (ary '{F} (ary '{T - 4 + 1} num))) rho /\
    StructUndefined (acc' (Var "tm4") : acc (ary '{F} num)) rho /\
    StructUndefined (acc' (Var "tc5") : acc (ary '{F} (ary '{T - 5 + 1} num))) rho /\
    StructUndefined (acc' (Var "tm5") : acc (ary '{F} num)) rho /\
    StructUndefined (acc' (Var "tcf") : acc (ary '{(F + F) + F} num)) rho /\
    StructUndefined (acc' (Var "tcl") : acc (ary '{nc} num)) rho /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tc3") : acc (ary '{F} (ary '{T - 3 + 1} num)))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tm3") : acc (ary '{F} num))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tc4") : acc (ary '{F} (ary '{T - 4 + 1} num)))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tm4") : acc (ary '{F} num))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tc5") : acc (ary '{F} (ary '{T - 5 + 1} num)))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tm5") : acc (ary '{F} num))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tcf") : acc (ary '{(F + F) + F} num))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "tcl") : acc (ary '{nc} num))).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma textcnn_comm_eq_direct :
    forall (output : acc (ary '{nc} num)),
    textcnn_comm output = textcnn_direct output.
  Proof.
    intros.
    unfold textcnn_comm, textcnn_direct, new.
    cbv beta.
    rewrite <- A_TextConv1dBranch.
    rewrite <- tc_c3_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_MaxOverTime.
    rewrite <- tc_m3_body.
    rewrite bind_read_replace.
    rewrite <- A_TextConv1dBranch.
    rewrite <- tc_c4_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_MaxOverTime.
    rewrite <- tc_m4_body.
    rewrite bind_read_replace.
    rewrite <- A_TextConv1dBranch.
    rewrite <- tc_c5_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_MaxOverTime.
    rewrite <- tc_m5_body.
    rewrite bind_read_replace.
    rewrite <- A_Concat1d3.
    rewrite <- tc_feat_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Linear1d.
    rewrite <- tc_logit_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax1d.
    rewrite <- tc_soft_body.
    reflexivity.
  Qed.

  Lemma A_TextCNN_direct :
    forall (output : acc (ary '{nc} num)) (rho : env) (p : path),
    in_acc p output ->
    textcnn_fresh output rho ->
    textcnn_direct output rho p = A(output, TextCNN) rho p.
  Proof.
    intros.
    unfold textcnn_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold TextCNN. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of TextCNN: under freshness of the
     temporary buffers, the imperative network observed at an output path
     computes the functional [TextCNN]. *)
  Theorem A_TextCNN :
    forall (output : acc (ary '{nc} num)) (rho : env) (p : path),
    in_acc p output ->
    textcnn_fresh output rho ->
    textcnn_comm output rho p = A(output, TextCNN) rho p.
  Proof.
    intros. rewrite textcnn_comm_eq_direct.
    apply A_TextCNN_direct; assumption.
  Qed.

End TextCNNNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: T = 8, de = 2, F = 2, nc = 3 (fin-8 scale)              *)
(* -------------------------------------------------------------------------- *)

Definition tc_i0_2 : fin 2 := @nat2fin 2 0 (ltac:(lia)).
Definition tc_i1_2 : fin 2 := @nat2fin 2 1 (ltac:(lia)).
Definition tc_i0_3 : fin 3 := @nat2fin 3 0 (ltac:(lia)).
Definition tc_i1_3 : fin 3 := @nat2fin 3 1 (ltac:(lia)).
Definition tc_i1_5 : fin 5 := @nat2fin 5 1 (ltac:(lia)).
Definition tc_i3_5 : fin 5 := @nat2fin 5 3 (ltac:(lia)).
Definition tc_i0_6 : fin 6 := @nat2fin 6 0 (ltac:(lia)).
Definition tc_i5_6 : fin 6 := @nat2fin 6 5 (ltac:(lia)).

Section Small_8_2_2_3.

  Context (w3s : exp (ary '{2} (ary '{3} (ary '{2} num)))) (b3s : exp (ary '{2} num))
          (w4s : exp (ary '{2} (ary '{4} (ary '{2} num)))) (b4s : exp (ary '{2} num))
          (w5s : exp (ary '{2} (ary '{5} (ary '{2} num)))) (b5s : exp (ary '{2} num))
          (wfcs : exp (ary '{3} (ary '{6} num))) (bfcs : exp (ary '{3} num))
          (inputs : exp (ary '{8} (ary '{2} num)))
          (outs : acc (ary '{3} num)).

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition TextCNN_8_2_2_3 : exp (ary '{3} num) :=
    @TextCNN 8 2 2 3 w3s b3s w4s b4s w5s b5s wfcs bfcs inputs.

  Definition textcnn_comm_8_2_2_3 : comm :=
    @textcnn_comm 8 2 2 3 w3s b3s w4s b4s w5s b5s wfcs bfcs inputs outs.

End Small_8_2_2_3.

(* [vm_compute]/conversion spot checks of the computable (structural) parts. *)

(* Conv1d branch entry (T=8, de=2, k=3: output length 8-3+1 = 6). *)
Example check_textconv_entry :
  forall (w : exp (ary '{2} (ary '{3} (ary '{2} num)))) (b : exp (ary '{2} num))
    (x : exp (ary '{8} (ary '{2} num))),
  idx (idx (@TextConv1dBranch 8 2 3 2 w b x) tc_i0_2) tc_i5_6 =
  TextConv1dCell (idx w tc_i0_2) (idx b tc_i0_2) x tc_i5_6.
Proof. reflexivity. Qed.

(* Max-over-time entry. *)
Example check_maxovertime_entry :
  forall (fm : exp (ary '{2} (ary '{5} num))),
  idx (MaxOverTime fm) tc_i1_2 = max (idx fm tc_i1_2).
Proof. reflexivity. Qed.

(* Concat1d: indices below c1 read the left vector, indices at/above c1
   read the right vector with offset.  (Nat.ltb_spec0 is an opaque lemma,
   so the checks case on it instead of computing through it.) *)
Example check_concat1d_left :
  forall (x : exp (ary '{2} num)) (y : exp (ary '{3} num)),
  idx (Concat1d x y) tc_i1_5 = idx x tc_i1_2.
Proof.
  intros. unfold Concat1d. rewrite idx_mkvSeq by lia.
  apply Concat1dCell_left. reflexivity.
Qed.

Example check_concat1d_right :
  forall (x : exp (ary '{2} num)) (y : exp (ary '{3} num)),
  idx (Concat1d x y) tc_i3_5 = idx y tc_i1_3.
Proof.
  intros. unfold Concat1d. rewrite idx_mkvSeq by lia.
  apply Concat1dCell_right. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions A_relu1.
Print Assumptions A_TextConv1dCell.
Print Assumptions A_TextConv1dBranch.
Print Assumptions A_MaxOverTime.
Print Assumptions A_Concat1d.
Print Assumptions A_Concat1d3.
Print Assumptions A_TextCNN.
