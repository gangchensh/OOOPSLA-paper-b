(* ========================================================================= *)
(* LeNet5_Par.v                                                              *)
(*                                                                           *)
(* OpenMP (M7) pilot: a parallel variant of the concrete imperative LeNet-5  *)
(* AST [CNN_Examples_LeNet5.lenet5_comm].  Only the OUTERMOST loop of each   *)
(* layer is turned from [seqfor] into [parfor]; every reduction inner loop   *)
(* (convolution window accumulation, Linear1d dot product, softmax sum,      *)
(* maxpool window scan) stays sequential because the accumulator dependency  *)
(* forbids parallelization.  Flatten3d is kept sequential: its outer index   *)
(* (channel c : fin 16) does not match the 1-D output acceptor shape         *)
(* (ary '{400} num) required by [parfor].                                    *)
(*                                                                           *)
(* Correctness: [DPIA_Rules.parfor_seqfor]                                   *)
(*   parfor a p = seqfor (fun i => p i (a|{i}))                              *)
(* (the AST-level Leibniz form of [AmkvPar]) gives a whole-net Leibniz       *)
(* equality [lenet5_par_comm = lenet5_comm], so every semantic property of   *)
(* the sequential net (in particular the route-A/route-B bridge of           *)
(* [Bridge_LeNet5]) transfers literally to the parallel net.                 *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

Require Import Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_Examples_Base_Ops.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.CNN_Examples_LeNet5.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

(* -------------------- Parallel layer variants -------------------- *)

(* Conv1: parallel over output channels (fin 6); window reduction sequential. *)
Definition lenet5_conv1_par_comm
  (input: exp (ary '{1} (ary '{32} (ary '{32} num))))
  (w: exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))))
  (bias: exp (ary '{6} num))
  (output: acc (ary '{6} (ary '{28} (ary '{28} num)))) : comm :=
  parfor output (fun num o =>
    seqfor (fun i0: fin 28 => seqfor (fun j0: fin 28 =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin 1 => seqfor (fun i1: fin 5 => seqfor (fun j1: fin 5 =>
          acc_a |:= add (mul input|[c]|[nat2fin (conv_idx_lt_32 i0 i1)]|[nat2fin (conv_idx_lt_32 j0 j1)]
                         w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        o|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))).

(* Conv2: parallel over output channels (fin 16); window reduction sequential. *)
Definition lenet5_conv2_par_comm
  (input: exp (ary '{6} (ary '{14} (ary '{14} num))))
  (w: exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (bias: exp (ary '{16} num))
  (output: acc (ary '{16} (ary '{10} (ary '{10} num)))) : comm :=
  parfor output (fun num o =>
    seqfor (fun i0: fin 10 => seqfor (fun j0: fin 10 =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin 6 => seqfor (fun i1: fin 5 => seqfor (fun j1: fin 5 =>
          acc_a |:= add (mul input|[c]|[nat2fin (conv_idx_lt_14 i0 i1)]|[nat2fin (conv_idx_lt_14 j0 j1)]
                         w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        o|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))).

(* ReLU3d: parallel over channels. *)
Definition ReLU3d_par_comm {filernum m1 m2}
  (input: exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output: acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))) : comm :=
  parfor output (fun num o => seqfor (fun i0 => seqfor (fun i1 =>
    If (leExp input|[num]|[i0]|[i1] zero)
      (o|{i0}|{i1} |:= zero, o|{i0}|{i1} |:= input|[num]|[i0]|[i1])))).

(* Pool1: parallel over channels; window max scan sequential. *)
Definition lenet5_pool1_par_comm
  (input: exp (ary '{6} (ary '{28} (ary '{28} num))))
  (output: acc (ary '{6} (ary '{14} (ary '{14} num)))) : comm :=
  parfor output (fun num o =>
    seqfor (fun i0: fin 14 => seqfor (fun j0: fin 14 =>
      new (fun tmp => let (w, v) := tmp in
        w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 28 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div 28 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
        seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
          If (gtExp input|[num]|[nat2fin (fin_mul_add_lt_div 28 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 28 2 j0 j1)] v)
          (w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 28 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 28 2 j0 j1)],
           w |:= v)
        )) ';
        o|{i0}|{j0} |:= v
      )
    ))).

(* Pool2: parallel over channels; window max scan sequential. *)
Definition lenet5_pool2_par_comm
  (input: exp (ary '{16} (ary '{10} (ary '{10} num))))
  (output: acc (ary '{16} (ary '{5} (ary '{5} num)))) : comm :=
  parfor output (fun num o =>
    seqfor (fun i0: fin 5 => seqfor (fun j0: fin 5 =>
      new (fun tmp => let (w, v) := tmp in
        w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 10 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div 10 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
        seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
          If (gtExp input|[num]|[nat2fin (fin_mul_add_lt_div 10 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 10 2 j0 j1)] v)
          (w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 10 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 10 2 j0 j1)],
           w |:= v)
        )) ';
        o|{i0}|{j0} |:= v
      )
    ))).

(* Linear1d: parallel over output units; dot-product reduction sequential. *)
Definition Linear1d_par_comm {m outnum}
  (w: exp (ary '{outnum} (ary '{m} num)))
  (b: exp (ary '{outnum} num)) (input: exp (ary '{m} num))
  (output: acc (ary '{outnum} num)) : comm :=
  parfor output (fun out o =>
    @loopacc num (fun tmp =>
      let w_acc := vwt tmp in
      let v := vrd tmp in
      (w_acc |:= zero) ';
      seqfor (fun i => w_acc |:= add (mul input|[i] w|[out]|[i]) v) ';
      o |:= add v b|[out])).

(* ReLU1d: parallel over elements. *)
Definition ReLU1d_par_comm {n:nat}
  (input: exp (ary '{n} num)) (output: acc (ary '{n} num)) : comm :=
  parfor output (fun i o =>
    If (leExp input|[i] zero) (o |:= zero, o |:= input|[i])).

(* Softmax1d: the sum reduction stays sequential; the division loop is
   parallel over elements. *)
Definition Softmax1d_par_comm {n}
  (input: exp (ary '{n} num)) (output: acc (ary '{n} num)) : comm :=
  @loopacc num (fun tmp =>
    let w := vwt tmp in
    let v := vrd tmp in
    (w |:= zero) ';
    seqfor (fun i => w |:= add (pExp (input|[i])) v) ';
    parfor output (fun j o => o |:= div (pExp (input|[j])) v)).

(* -------------------- The parallel whole-net AST -------------------- *)

Definition lenet5_par_comm : comm :=
  lenet5_conv1_par_comm lenet5_input lenet5_kc1 lenet5_bc1 (vwt "c1") ';
  @ReLU3d_par_comm 6 28 28 (vrd "c1") (vwt "r1") ';
  lenet5_pool1_par_comm (vrd "r1") (vwt "p1") ';
  lenet5_conv2_par_comm (vrd "p1") lenet5_kc2 lenet5_bc2 (vwt "c2") ';
  @ReLU3d_par_comm 16 10 10 (vrd "c2") (vwt "r2") ';
  lenet5_pool2_par_comm (vrd "r2") (vwt "p2") ';
  lenet5_flatten_comm (vrd "p2") (vwt "flat") ';
  Linear1d_par_comm lenet5_fc1_w lenet5_fc1_b (vrd "flat") (vwt "fc1") ';
  @ReLU1d_par_comm 120 (vrd "fc1") (vwt "fc1_relu") ';
  Linear1d_par_comm lenet5_fc2_w lenet5_fc2_b (vrd "fc1_relu") (vwt "fc2") ';
  @ReLU1d_par_comm 84 (vrd "fc2") (vwt "fc2_relu") ';
  Linear1d_par_comm lenet5_fc3_w lenet5_fc3_b (vrd "fc2_relu") (vwt "fc3") ';
  @Softmax1d_par_comm 10 (vrd "fc3") lenet5_output.

(* -------------------- Correctness: par = seq -------------------- *)

(* [CG.parfor] and [CG.seqfor] are different constructors, so the two nets
   are not Leibniz-equal; but [eval] maps both to the same [PCG.seqfor]
   (CNN_CodeGen_Semantics.v, eval_aux: CG.parfor n d a p is interpreted as
   PCG.seqfor (fun i => eval (p i (DE.idxAcc a i)))).  This is the CG-level
   counterpart of route A's [DPIA_Rules.AmkvPar] / [parfor_seqfor] (which
   are stated for [PCG.comm], where parfor is a derived snoc-fold).

   The equalities below hold by conversion, but are proved PER LAYER: a
   single whole-net [reflexivity] makes the conversion machinery iota-expand
   every concrete [PCG.seqfor] (millions of nodes) and does not terminate in
   practice.  At one constructor of depth, conversion only compares closures
   pointwise (all layer types are concrete, so the idxAcc/acc_default copies
   in DataExp vs CNN_CodeGen_Core reduce to the same acceptor values). *)

Lemma conv1_par_eval : forall input w bias output rho,
  eval (lenet5_conv1_par_comm input w bias output) rho =
  eval (lenet5_conv1_comm input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma conv2_par_eval : forall input w bias output rho,
  eval (lenet5_conv2_par_comm input w bias output) rho =
  eval (lenet5_conv2_comm input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu3d_par_eval : forall filernum m1 m2 input output rho,
  eval (@ReLU3d_par_comm filernum m1 m2 input output) rho =
  eval (@ReLU3d_comm filernum m1 m2 input output) rho.
Proof. intros. reflexivity. Qed.

Lemma pool1_par_eval : forall input output rho,
  eval (lenet5_pool1_par_comm input output) rho =
  eval (lenet5_pool1_comm input output) rho.
Proof. intros. reflexivity. Qed.

Lemma pool2_par_eval : forall input output rho,
  eval (lenet5_pool2_par_comm input output) rho =
  eval (lenet5_pool2_comm input output) rho.
Proof. intros. reflexivity. Qed.

Lemma linear1d_par_eval : forall m outnum w b input output rho,
  eval (@Linear1d_par_comm m outnum w b input output) rho =
  eval (@Linear1d_comm m outnum w b input output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu1d_par_eval : forall n input output rho,
  eval (@ReLU1d_par_comm n input output) rho =
  eval (@ReLU1d_comm n input output) rho.
Proof. intros. reflexivity. Qed.

Lemma softmax1d_par_eval : forall n input output rho,
  eval (@Softmax1d_par_comm n input output) rho =
  eval (@Softmax1d_comm n input output) rho.
Proof. intros. reflexivity. Qed.

(* Congruence of [eval] under sequential composition. *)
Lemma eval_seq_congr : forall c1 c1' c2 c2' rho,
  (forall r, eval c1 r = eval c1' r) ->
  (forall r, eval c2 r = eval c2' r) ->
  eval (c1 '; c2) rho = eval (c1' '; c2') rho.
Proof.
  intros c1 c1' c2 c2' rho H1 H2.
  unfold eval in *. rewrite !eval_seq_aux.
  unfold PCG.seq. rewrite H1, H2. reflexivity.
Qed.

(* The parallel net has the same denotation as the sequential net, hence the
   [Bridge_LeNet5] chain to route A ([LeNet5_DPIA.A_LeNet5]) applies to it. *)
Theorem lenet5_par_eval_eq : forall rho,
  eval lenet5_par_comm rho = eval lenet5_comm rho.
Proof.
  intros rho. unfold lenet5_par_comm, lenet5_comm.
  apply eval_seq_congr; [ intros r; apply conv1_par_eval |].
  intros r. apply eval_seq_congr; [ intros r0; apply relu3d_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply pool1_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply conv2_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply relu3d_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply pool2_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; reflexivity (* flatten: identical *) |].
  intros r5. apply eval_seq_congr; [ intros r6; apply linear1d_par_eval |].
  intros r6. apply eval_seq_congr; [ intros r7; apply relu1d_par_eval |].
  intros r7. apply eval_seq_congr; [ intros r8; apply linear1d_par_eval |].
  intros r8. apply eval_seq_congr; [ intros r9; apply relu1d_par_eval |].
  intros r9. apply eval_seq_congr; [ intros r10; apply linear1d_par_eval |].
  intros r10. apply softmax1d_par_eval.
Qed.

(* -------------------- Extraction for the streaming printer -------------------- *)

Extraction "lenet5_par_comm.ml" lenet5_par_comm.
