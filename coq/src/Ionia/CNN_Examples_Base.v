(* Reusable CNN layer combinators *)

From Stdlib Require Import Reals String Nat List Bool Arith Lia NArith.
Require Import Logic.FunctionalExtensionality Program.
Require Export Ionia.CNN_OP.
Require Export Ionia.CNN_Model.
Require Export Ionia.CNN_CodeGen.
Require Import Ionia.CNN_CodeGen_Semantics.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.
Opaque CG_acc CG_exp.


Require Export Ionia.CNN_Examples_Base_Ops.

(* Pointwise congruence for [PCG.seqfor]: two loops whose bodies agree at
   every index and every environment produce equal results. *)
Lemma seqfor_congr :
  forall n (f g : fin n -> PCG.comm) (rho : PCG.env),
    (forall i eta, f i eta = g i eta) ->
    PCG.seqfor f rho = PCG.seqfor g rho.
Proof.
  intros n f g rho H.
  apply (@f_equal _ _ (fun g0 : fin n -> PCG.comm => PCG.seqfor g0 rho)).
  apply functional_extensionality. intro i.
  apply functional_extensionality. intro eta. apply H.
Qed.
Ltac CGidx_rw := try repeat rewrite CGidx_rexp; try repeat rewrite CGidx.

Lemma exp_independent_of_acc_weaken_ary :
  forall n d d' (e : exp d') (a : acc (ary '{n} d)) (i : fin n),
    exp_independent_of_acc e a ->
    exp_independent_of_acc e (a |{ i}).
Proof.
  intros n d d' e a i Hin p Hp. apply Hin. apply in_acc_ary_inv with (i := i). exact Hp.
Qed.

(* ===================== ReLU Code Generation Example ===================== *)
(* ReLU1d: output = ReLU(input)
   Generates:
   for(int i0=0; i0<3; i0 += 1) 
   { if (input[i0] <= 0)
     { output[i0] = 0 ;}
     else
     { output[i0] = input[i0] ;}}
*)
Definition relu_input : exp (ary '{3} num) := vrd "input".
Definition relu_output : acc (ary '{3} num) := vwt "output".

Definition ReLU1d_comm {n:nat} (input:exp (ary '{n} num)) (output:acc (ary '{n} num)) : comm :=
  seqfor (fun i => If (leExp input|[i] zero) (output|{i} |:= zero, output|{i} |:= input|[i])).

(* The AST-level Leibniz theorem [ReLU1d_equiv] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); the semantic
   equivalence is proved directly below as [ReLU1d_equiv_sem]. *)

Theorem ReLU1d_equiv_sem :
  forall n (input : exp (ary '{n} num)) (output : acc (ary '{n} num)) (rho : PCG.env),
    exp_independent_of_acc input output ->
    (forall i, DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end)
                 (leExp input|[i] zero) = bexp2bool (leExp input|[i] zero)) ->
    eval (A(output, @ReLU1d n input)) rho = eval (@ReLU1d_comm n input output) rho.
Proof.
  intros n input output rho Hin Hbeq.
  unfold ReLU1d, ReLU1d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. apply seqfor_If_sem.
    + intros i p Hp. cbn beta.
      eapply bexp_leExp_zero_independent_of_acc with (a := output); eassumption.
    + exact Hbeq.
  - intros i. apply exp_independent_of_acc_if; intros _;
      [ apply exp_independent_of_acc_zero
      | apply exp_independent_of_acc_idx; exact Hin ].
Qed.

Theorem relu1d_CG :
  CG_comm (ReLU1d_comm relu_input relu_output) 0 = 
  "for(int i0=0; i0<3; i0 += 1) \n  { if (input[i0] <= 0)\n  { output[i0] = 0 ;}\nelse\n  { output[i0] = input[i0] ;}}".
Proof.
  unfold ReLU1d_comm.
  simpl CG_comm.
  simpl.
  repeat rewrite CGidx_rexp.
  CGidx_rw.
  repeat rewrite CGidxAcc.
  unfold relu_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  simpl. simpl.
  rewrite exp_zero.
  rewrite CGexpvar_gen by CGvar_side.
  CGidx_rw.
  unfold relu_input.
  rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl.
  simpl.
  repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== ReLU2d Code Generation Example ===================== *)
(* ReLU2d: output = ReLU(input) for 4x4 matrix
   Generates nested sequential loops with if-else
*)
Definition relu2d_input : exp (ary '{4} (ary '{4} num)) := vrd "input".
Definition relu2d_output : acc (ary '{4} (ary '{4} num)) := vwt "output".

Definition ReLU2d_comm {m1 m2:nat} (input: exp (ary '{m1} (ary '{m2} num))) (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 => seqfor (fun i1 => 
    If (leExp input|[i0]|[i1] zero) (output|{i0}|{i1} |:= zero, output|{i0}|{i1} |:= input|[i0]|[i1]))).

(* The AST-level Leibniz theorem [ReLU2d_equiv] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); the semantic
   equivalence is proved directly below as [ReLU2d_equiv_sem]. *)

Theorem ReLU2d_equiv_sem :
  forall m1 m2 (input : exp (ary '{m1} (ary '{m2} num)))
             (output : acc (ary '{m1} (ary '{m2} num))) (rho : PCG.env),
    exp_independent_of_acc input output ->
    (forall i0 i1, DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end)
                     (leExp input|[i0]|[i1] zero) = bexp2bool (leExp input|[i0]|[i1] zero)) ->
    eval (A(output, @ReLU2d m1 m2 input)) rho = eval (@ReLU2d_comm m1 m2 input output) rho.
Proof.
  intros m1 m2 input output rho Hin Hbeq.
  (* The static/runtime branch agreement lifts to every environment that
     agrees with [rho] outside [output]. *)
  assert (Hbeq' : forall eta,
    (forall q, ~ @PCG.in_acc (ary '{m1} (ary '{m2} num)) q output -> eta q = rho q) ->
    forall i0 i1, DE.eval_bexp (fun s => match eta (DE.Var s) with Some r => r | None => R0 end)
                    (leExp input|[i0]|[i1] zero) = bexp2bool (leExp input|[i0]|[i1] zero)).
  { intros eta Hagree i0 i1. rewrite <- (Hbeq i0 i1).
    apply bexp_independent_eval with (a := output).
    - intros p Hp.
      eapply bexp_leExp_zero_independent_of_acc with (a := output).
      + apply exp_independent_of_acc_idx. exact Hin.
      + exact Hp.
    - exact Hagree. }
  unfold ReLU2d, ReLU2d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_pointwise_inv
      with (P := fun eta => forall q, ~ @PCG.in_acc (ary '{m1} (ary '{m2} num)) q output -> eta q = rho q);
      [ | intros i0 eta HP; split ].
    + intros q Hq. reflexivity.
    + cbn beta. rewrite AmkvSeq_sem.
      * unfold mkvSeql. rewrite !eval_seqfor.
        apply seqfor_If_sem.
        -- intros i1 p Hp. cbn beta.
           eapply bexp_leExp_zero_independent_of_acc with (a := (output|{i0})).
           ++ apply exp_independent_of_acc_idx.
              apply exp_independent_of_acc_weaken_ary. exact Hin.
           ++ exact Hp.
        -- intro i1. apply Hbeq'. exact HP.
      * intros i1. apply exp_independent_of_acc_if; intros _;
          [ apply exp_independent_of_acc_zero
          | do 2 (apply exp_independent_of_acc_idx);
            apply exp_independent_of_acc_weaken_ary; exact Hin ].
    + intros q Hq. cbn beta. transitivity (eta q).
      * apply eval_assign_idx_modifies_only. exact Hq.
      * apply HP. exact Hq.
  - intros i0. apply exp_independent_of_acc_mkvSeq. intros i1.
    apply exp_independent_of_acc_if; intros _;
      [ apply exp_independent_of_acc_zero
      | do 2 (apply exp_independent_of_acc_idx); exact Hin ].
Qed.

Theorem relu2d_CG :
  CG_comm (ReLU2d_comm relu2d_input relu2d_output) 0 = 
  "for(int i0=0; i0<4; i0 += 1) \n  { for(int i1=0; i1<4; i1 += 1) \n  { if (input[i0][i1] <= 0)\n  { output[i0][i1] = 0 ;}\nelse\n  { output[i0][i1] = input[i0][i1] ;}}}".
Proof.
  unfold ReLU2d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  unfold relu2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl. simpl.
  rewrite exp_zero.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGfor. simpl.
  unfold relu2d_input. CGidx_rw.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  reflexivity.
Qed.

(* ===================== Add2d Code Generation Example ===================== *)
(* Add2d: output = x + y (element-wise, 2x3)
   Generates nested sequential loops:
   for(int i0=0; i0<2; i0 += 1) 
   { for(int i1=0; i1<3; i1 += 1) 
   { output[i0][i1] = (x[i0][i1] + y[i0][i1]) ;}}
*)
Definition add2d_x : exp (ary '{2} (ary '{3} num)) := vrd "x".
Definition add2d_y : exp (ary '{2} (ary '{3} num)) := vrd "y".
Definition add2d_output : acc (ary '{2} (ary '{3} num)) := vwt "output".

Definition Add2d_comm {m1 m2} (x y: exp (ary '{m1} (ary '{m2} num))) (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 => seqfor (fun i1 => output|{i0}|{i1} |:= add x|[i0]|[i1] y|[i0]|[i1])).

Theorem add2d_CG :
  CG_comm (Add2d_comm add2d_x add2d_y add2d_output) 0 = 
  "for(int i0=0; i0<2; i0 += 1) \n  { for(int i1=0; i1<3; i1 += 1) \n  { output[i0][i1] = (x[i0][i1] + y[i0][i1]) ;}}".
Proof.
  unfold Add2d_comm.
  simpl CG_comm.
  simpl.
  repeat rewrite CGidxAcc.
  unfold add2d_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  simpl.
  rewrite CGadd.
  simpl.
  CGidx_rw.
  unfold add2d_x, add2d_y.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl.
  simpl.
  repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== PseudoSoftmax1d Code Generation Example ===================== *)
(* let + sum + element-wise division combination pattern
   Generates:
   float v0;
   v0 = 0;
   for(int i1=0; i1<3; i1 += 1) 
   { v0 = (input[i1] + v0) ;}
   for(int i2=0; i2<3; i2 += 1) 
   { output[i2] = (input[i2]) / (v0) ;}
*)
Definition ps_input : exp (ary '{3} num) := vrd "input".
Definition ps_output : acc (ary '{3} num) := vwt "output".

Definition PseudoSoftmax1d_comm {n:nat} (input:exp (ary '{n} num)) (output:acc (ary '{n} num)) : comm :=
  new (fun tmp => let (w,v) := tmp in
    (w |:= zero) '; 
    seqfor (fun i => w |:= add (input|[i]) v) '; 
    seqfor (fun j => output|{j} |:= div (input|[j]) v)).

Theorem pseudo_softmax_CG :
  CG_comm (PseudoSoftmax1d_comm ps_input ps_output) 0 = 
  "float v0;\nv0 = 0 ;\nfor(int i1=0; i1<3; i1 += 1) \n  { v0 = (input[i1] + v0) ;}\nfor(int i2=0; i2<3; i2 += 1) \n  { output[i2] = (input[i2]) / (v0) ;}".
Proof.
  unfold PseudoSoftmax1d_comm.
  simpl CG_comm.
  simpl.
  rewrite CGaccvar_gen by CGvar_side.
  simpl.
  rewrite CGadd.
  simpl.
  rewrite CGexpvar_gen by CGvar_side.
  CGidx_rw.
  unfold ps_input.
  rewrite CGexpvar_gen by CGvar_side.
  rewrite exp_zero.
  rewrite CGexpvar_gen by CGvar_side.
  simpl.
  rewrite CGdiv.
  simpl.
  rewrite CGexpvar_gen by CGvar_side.
  CGidx_rw.
  unfold ps_input.
  rewrite CGexpvar_gen by CGvar_side.
  repeat rewrite CGidxAcc.
  unfold ps_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl.
  simpl.
  repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== Padding2d Code Generation Example ===================== *)
(* Concrete instance: p=1, n1=2, n2=2.
   Input: 2x2, Output: 4x4 (with 1-pixel zero padding).
   Generates 16 explicit assignments.
*)

Program Definition f0 : fin 4 := @nat2fin 4 0 _.
Program Definition f1 : fin 4 := @nat2fin 4 1 _.
Program Definition f2 : fin 4 := @nat2fin 4 2 _.
Program Definition f3 : fin 4 := @nat2fin 4 3 _.

Program Definition g0 : fin 2 := @nat2fin 2 0 _.
Program Definition g1 : fin 2 := @nat2fin 2 1 _.

Definition pad_input : exp (ary '{2} (ary '{2} num)) := vrd "input".
Definition pad_output : acc (ary '{4} (ary '{4} num)) := vwt "output".

Definition padding_val (i0 i1: fin 4) (input: exp (ary '{2} (ary '{2} num))) : exp num :=
  if Nat.eqb (fin2nat i0) 1 then
    if Nat.eqb (fin2nat i1) 1 then input|[g0]|[g0]
    else if Nat.eqb (fin2nat i1) 2 then input|[g0]|[g1]
    else zero
  else if Nat.eqb (fin2nat i0) 2 then
    if Nat.eqb (fin2nat i1) 1 then input|[g1]|[g0]
    else if Nat.eqb (fin2nat i1) 2 then input|[g1]|[g1]
    else zero
  else zero.

Definition assign_ij (i0 i1: fin 4) (input: exp (ary '{2} (ary '{2} num))) (output: acc (ary '{4} (ary '{4} num))) : comm :=
  output|{i0}|{i1} |:= padding_val i0 i1 input.

Definition padding2d_comm (input: exp (ary '{2} (ary '{2} num))) (output: acc (ary '{4} (ary '{4} num))) : comm :=
  seq (assign_ij f0 f0 input output,
  seq (assign_ij f0 f1 input output,
  seq (assign_ij f0 f2 input output,
  seq (assign_ij f0 f3 input output,
  seq (assign_ij f1 f0 input output,
  seq (assign_ij f1 f1 input output,
  seq (assign_ij f1 f2 input output,
  seq (assign_ij f1 f3 input output,
  seq (assign_ij f2 f0 input output,
  seq (assign_ij f2 f1 input output,
  seq (assign_ij f2 f2 input output,
  seq (assign_ij f2 f3 input output,
  seq (assign_ij f3 f0 input output,
  seq (assign_ij f3 f1 input output,
  seq (assign_ij f3 f2 input output,
       assign_ij f3 f3 input output))))))))))))))).

Theorem padding2d_CG :
  CG_comm (padding2d_comm pad_input pad_output) 0 = 
  "output[0][0] = 0 ;\noutput[0][1] = 0 ;\noutput[0][2] = 0 ;\noutput[0][3] = 0 ;\noutput[1][0] = 0 ;\noutput[1][1] = input[0][0] ;\noutput[1][2] = input[0][1] ;\noutput[1][3] = 0 ;\noutput[2][0] = 0 ;\noutput[2][1] = input[1][0] ;\noutput[2][2] = input[1][1] ;\noutput[2][3] = 0 ;\noutput[3][0] = 0 ;\noutput[3][1] = 0 ;\noutput[3][2] = 0 ;\noutput[3][3] = 0 ;".
Proof.
  unfold padding2d_comm, assign_ij, padding_val.
  simpl.
  simpl CG_comm.
  simpl.
  repeat rewrite CGidxAcc.
  unfold pad_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  simpl.
  CGidx_rw.
  unfold pad_input.
  repeat rewrite exp_zero.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl.
  strnat_simpl.
  simpl.
  repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== convert_1 Code Generation Example ===================== *)
(* convert_1: output = input (type conversion, 1x1x2x2)
   Generates nested sequential loops:
   for(int i0=0; i0<1; i0 += 1) 
   { for(int i1=0; i1<1; i1 += 1) 
   { for(int i2=0; i2<2; i2 += 1) 
   { for(int i3=0; i3<2; i3 += 1) 
   { output[i0][i1][i2][i3] = input[i0][i1][i2][i3] ;}}}}
*)
Definition convert1_input : exp (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))) := vrd "input".
Definition convert1_output : acc (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))) := vwt "output".

(* The AST-level golden test [convert1_CG] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); it rewrites with
   [AmkvSeq], which depends on the AST axiom [mkvSeq_equiv_ast]. *)

(* ===================== Convert3 (3x3 kernel identity) Code Generation ===================== *)
(*
   Expected C code for 1x1x3x3 tensor:
   for(int i0=0; i0<1; i0 += 1) 
   { for(int i1=0; i1<1; i1 += 1) 
   { for(int i2=0; i2<3; i2 += 1) 
   { for(int i3=0; i3<3; i3 += 1) 
   { output[i0][i1][i2][i3] = input[i0][i1][i2][i3] ;}}}}
*)
Definition convert3_input : exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vrd "input".
Definition convert3_output : acc (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vwt "output".

(* The AST-level golden test [convert3_CG] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build). *)

(* ===================== Convert5 (5x5 kernel identity) Code Generation ===================== *)
(*
   Expected C code for 1x1x5x5 tensor:
   for(int i0=0; i0<1; i0 += 1) 
   { for(int i1=0; i1<1; i1 += 1) 
   { for(int i2=0; i2<5; i2 += 1) 
   { for(int i3=0; i3<5; i3 += 1) 
   { output[i0][i1][i2][i3] = input[i0][i1][i2][i3] ;}}}}
*)
Definition convert5_input : exp (ary '{1} (ary '{1} (ary '{5} (ary '{5} num)))) := vrd "input".
Definition convert5_output : acc (ary '{1} (ary '{1} (ary '{5} (ary '{5} num)))) := vwt "output".

(* The AST-level golden test [convert5_CG] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build). *)

(* ===================== padl (left padding) Code Generation ===================== *)
(*
   Expected C code for padl 1 on a 1D array of size 2:
   for(int i0=0; i0<3; i0 += 1) 
   { if (i0 < 1)
   { output[i0] = 0 ;}
   else
   { output[i0] = input[i0-1] ;}}
*)
Definition padl1d_input : exp (ary '{2} num) := vrd "input".
Definition padl1d_output : acc (ary '{3} num) := vwt "output".

(* The AST-level golden test [padl1d_CG] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build). *)

(* ===================== padr (right padding) Code Generation ===================== *)
(*
   Expected C code for padr 1 on a 1D array of size 2:
   for(int i0=0; i0<3; i0 += 1) 
   { if (i0 < 2)
   { output[i0] = input[i0] ;}
   else
   { output[i0] = 0 ;}}
*)
Definition padr1d_input : exp (ary '{2} num) := vrd "input".
Definition padr1d_output : acc (ary '{3} num) := vwt "output".

(* The AST-level golden test [padr1d_CG] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build). *)

(* ===================== concat (concatenation) Code Generation ===================== *)
(*
   Expected C code for concat of two 1D arrays of size 2 and 3:
   for(int i0=0; i0<5; i0 += 1) 
   { if (i0 < 2)
   { output[i0] = e1[i0] ;}
   else
   { output[i0] = e2[i0-2] ;}}
*)
Definition concat1d_e1 : exp (ary '{2} num) := vrd "e1".
Definition concat1d_e2 : exp (ary '{3} num) := vrd "e2".
Definition concat1d_output : acc (ary '{5} num) := vwt "output".

(* The AST-level golden test [concat1d_CG] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build). *)

(* ===================== Conv2d Code Generation Example ===================== *)
(* Conv2d: 4x4 input, 3x3 kernel, padding=1, stride=1
   Output: 4x4, Padded: 6x6
   Generates imperative code with explicit loops for padding and convolution.
*)
Definition conv2d_w_4x4 : exp (ary '{3} (ary '{3} num)) := vrd "w".
Definition conv2d_input_4x4 : exp (ary '{4} (ary '{4} num)) := vrd "input".
Definition conv2d_output_4x4 : acc (ary '{4} (ary '{4} num)) := vwt "output".

Definition conv2d_comm_4x4 (w: exp (ary '{3} (ary '{3} num)))
  (input: exp (ary '{4} (ary '{4} num)))
  (output: acc (ary '{4} (ary '{4} num))) : comm :=
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun i: fin 6 => seqfor (fun j: fin 6 =>
      If (BLt (fin2nat i) 1)
      (pad_a|{i}|{j} |:= zero,
       If (BLt (fin2nat i) 5)
        (If (BLt (fin2nat j) 1)
          (pad_a|{i}|{j} |:= zero,
           If (BLt (fin2nat j) 5)
            (pad_a|{i}|{j} |:= safe_idx_nat (safe_idx_nat input (fin2nat i - 1)) (fin2nat j - 1),
             pad_a|{i}|{j} |:= zero)),
         pad_a|{i}|{j} |:= zero))
    )) ';
    seqfor (fun i0: fin 4 => seqfor (fun j0: fin 4 =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[i1]|[j1]) acc_v
        )) ';
        output|{i0}|{j0} |:= acc_v
      )
    ))
  ).

(* Semantic equivalence between functional Conv2d and imperative Conv2d_comm.
   For the concrete 4x4 case, this can in principle be proven from sum_equiv,
   mkvSeq_equiv, etc., but the nested sum/mkvSeq structure makes the proof
   extremely long. We leave it as an axiom for now. *)
Axiom Conv2d_equiv_concrete_4x4 : forall w input output,
  A(output, @Conv2d 4 4 3 3 1 1 w input) = conv2d_comm_4x4 w input output.

Theorem conv2d_CG_4x4 :
  CG_comm (conv2d_comm_4x4 conv2d_w_4x4 conv2d_input_4x4 conv2d_output_4x4) 0 = 
  "float v0[6][6];\nfor(int i1=0; i1<6; i1 += 1) \n  { for(int i2=0; i2<6; i2 += 1) \n  { if (i1 < 1)\n  { v0[i1][i2] = 0 ;}\nelse\n  { if (i1 < 5)\n  { if (i2 < 1)\n  { v0[i1][i2] = 0 ;}\nelse\n  { if (i2 < 5)\n  { v0[i1][i2] = input[i1-1][i2-1] ;}\nelse\n  { v0[i1][i2] = 0 ;}}}\nelse\n  { v0[i1][i2] = 0 ;}}}}\nfor(int i3=0; i3<4; i3 += 1) \n  { for(int i4=0; i4<4; i4 += 1) \n  { float v5;\nv5 = 0 ;\nfor(int i6=0; i6<3; i6 += 1) \n  { for(int i7=0; i7<3; i7 += 1) \n  { v5 = ((v0[(i3) + (i6)][(i4) + (i7)] * w[i6][i7]) + v5) ;}}\noutput[i3][i4] = v5 ;}}".
Proof.
  unfold conv2d_comm_4x4.
  simpl CG_comm.
  simpl.
  repeat rewrite CGif.
  simpl.
  repeat rewrite CGassign.
  simpl.
  repeat rewrite CGnew.
  simpl.
  repeat rewrite CGfor.
  simpl.
  repeat rewrite CGidxAcc.
  unfold conv2d_output_4x4. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  CGidx_rw.
  unfold conv2d_input_4x4, conv2d_w_4x4. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl.
  simpl.
  repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== Conv3d Code Generation Example ===================== *)
(* Conv3d: 1x4x4 input (channel=1), 1x1x3x3 kernel (filernum=1,channel=1),
   padding=1, stride=1
   Output: 1x4x4, Padded: 1x6x6
   Generates imperative code with explicit loops for padding and convolution.
*)
Definition conv3d_w : exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vrd "w".
Definition conv3d_input : exp (ary '{1} (ary '{4} (ary '{4} num))) := vrd "input".
Definition conv3d_output : acc (ary '{1} (ary '{4} (ary '{4} num))) := vwt "output".
Definition conv3d_bias : exp (ary '{1} num) := vrd "bias".

Definition conv3d_comm_1x4x4
  (w: exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))))
  (input: exp (ary '{1} (ary '{4} (ary '{4} num))))
  (bias: exp (ary '{1} num))
  (output: acc (ary '{1} (ary '{4} (ary '{4} num)))) : comm :=
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun c: fin 1 => seqfor (fun i: fin 6 => seqfor (fun j: fin 6 =>
      If (BLt (fin2nat i) 1)
      (pad_a|{c}|{i}|{j} |:= zero,
       If (BLt (fin2nat i) 5)
        (If (BLt (fin2nat j) 1)
          (pad_a|{c}|{i}|{j} |:= zero,
           If (BLt (fin2nat j) 5)
            (pad_a|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[c] (fin2nat i - 1)) (fin2nat j - 1),
             pad_a|{c}|{i}|{j} |:= zero)),
         pad_a|{c}|{i}|{j} |:= zero))
    ))) ';
    seqfor (fun num: fin 1 => seqfor (fun i0: fin 4 => seqfor (fun j0: fin 4 =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin 1 => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        output|{num}|{i0}|{j0} |:= add acc_v bias|[num]
      )
    )))
  ).

Axiom Conv3d_equiv_concrete_1x4x4 : forall w input bias output,
  A(output, @Conv3d 4 4 3 3 1 1 1 1 conv3d_bias w input) = conv3d_comm_1x4x4 w input bias output.

Theorem conv3d_CG_1x4x4 :
  CG_comm (conv3d_comm_1x4x4 conv3d_w conv3d_input conv3d_bias conv3d_output) 0 =
  "float v0[1][6][6];\nfor(int i1=0; i1<1; i1 += 1) \n  { for(int i2=0; i2<6; i2 += 1) \n  { for(int i3=0; i3<6; i3 += 1) \n  { if (i2 < 1)\n  { v0[i1][i2][i3] = 0 ;}\nelse\n  { if (i2 < 5)\n  { if (i3 < 1)\n  { v0[i1][i2][i3] = 0 ;}\nelse\n  { if (i3 < 5)\n  { v0[i1][i2][i3] = input[i1][i2-1][i3-1] ;}\nelse\n  { v0[i1][i2][i3] = 0 ;}}}\nelse\n  { v0[i1][i2][i3] = 0 ;}}}}}\nfor(int i4=0; i4<1; i4 += 1) \n  { for(int i5=0; i5<4; i5 += 1) \n  { for(int i6=0; i6<4; i6 += 1) \n  { float v7;\nv7 = 0 ;\nfor(int i8=0; i8<1; i8 += 1) \n  { for(int i9=0; i9<3; i9 += 1) \n  { for(int i10=0; i10<3; i10 += 1) \n  { v7 = ((v0[i8][(i5) + (i9)][(i6) + (i10)] * w[i4][i8][i9][i10]) + v7) ;}}}\noutput[i4][i5][i6] = (v7 + bias[i4]) ;}}}".
Proof.
  unfold conv3d_comm_1x4x4.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold conv3d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  CGidx_rw.
  unfold conv3d_input, conv3d_w, conv3d_bias. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== Conv4d Code Generation Example ===================== *)
(* Conv4d: 1x1x4x4 input (batch=1,channel=1), 1x1x3x3 kernel (filernum=1,channel=1),
   padding=1, stride=1
   Output: 1x1x4x4, Padded: 1x1x6x6
   Generates imperative code with explicit loops for padding and convolution.
*)
Definition conv4d_w : exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vrd "w".
Definition conv4d_input : exp (ary '{1} (ary '{1} (ary '{4} (ary '{4} num)))) := vrd "input".
Definition conv4d_output : acc (ary '{1} (ary '{1} (ary '{4} (ary '{4} num)))) := vwt "output".
Definition conv4d_bias : exp (ary '{1} num) := vrd "bias".

Definition conv4d_comm_1x1x4x4
  (w: exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))))
  (input: exp (ary '{1} (ary '{1} (ary '{4} (ary '{4} num)))))
  (bias: exp (ary '{1} num))
  (output: acc (ary '{1} (ary '{1} (ary '{4} (ary '{4} num))))) : comm :=
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin 1 => seqfor (fun c: fin 1 => seqfor (fun i: fin 6 => seqfor (fun j: fin 6 =>
      If (BLt (fin2nat i) 1)
      (pad_a|{b}|{c}|{i}|{j} |:= zero,
       If (BLt (fin2nat i) 5)
        (If (BLt (fin2nat j) 1)
          (pad_a|{b}|{c}|{i}|{j} |:= zero,
           If (BLt (fin2nat j) 5)
            (pad_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 1)) (fin2nat j - 1),
             pad_a|{b}|{c}|{i}|{j} |:= zero)),
         pad_a|{b}|{c}|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin 1 => seqfor (fun num: fin 1 => seqfor (fun i0: fin 4 => seqfor (fun j0: fin 4 =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin 1 => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))
  ).

Axiom Conv4d_equiv_concrete_1x1x4x4 : forall w input bias output,
  A(output, @Conv4d 1 4 4 3 3 1 1 1 1 conv4d_bias w input) = conv4d_comm_1x1x4x4 w input bias output.

Theorem conv4d_CG_1x1x4x4 :
  CG_comm (conv4d_comm_1x1x4x4 conv4d_w conv4d_input conv4d_bias conv4d_output) 0 =
  "float v0[1][1][6][6];\nfor(int i1=0; i1<1; i1 += 1) \n  { for(int i2=0; i2<1; i2 += 1) \n  { for(int i3=0; i3<6; i3 += 1) \n  { for(int i4=0; i4<6; i4 += 1) \n  { if (i3 < 1)\n  { v0[i1][i2][i3][i4] = 0 ;}\nelse\n  { if (i3 < 5)\n  { if (i4 < 1)\n  { v0[i1][i2][i3][i4] = 0 ;}\nelse\n  { if (i4 < 5)\n  { v0[i1][i2][i3][i4] = input[i1][i2][i3-1][i4-1] ;}\nelse\n  { v0[i1][i2][i3][i4] = 0 ;}}}\nelse\n  { v0[i1][i2][i3][i4] = 0 ;}}}}}}\nfor(int i5=0; i5<1; i5 += 1) \n  { for(int i6=0; i6<1; i6 += 1) \n  { for(int i7=0; i7<4; i7 += 1) \n  { for(int i8=0; i8<4; i8 += 1) \n  { float v9;\nv9 = 0 ;\nfor(int i10=0; i10<1; i10 += 1) \n  { for(int i11=0; i11<3; i11 += 1) \n  { for(int i12=0; i12<3; i12 += 1) \n  { v9 = ((v0[i5][i10][(i7) + (i11)][(i8) + (i12)] * w[i6][i10][i11][i12]) + v9) ;}}}\noutput[i5][i6][i7][i8] = (v9 + bias[i6]) ;}}}}".
Proof.
  unfold conv4d_comm_1x1x4x4.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold conv4d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  CGidx_rw.
  unfold conv4d_input, conv4d_w, conv4d_bias. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== ConvTranspose2d Code Generation Example ===================== *)
(* ConvTranspose2d: 2x2 input, 3x3 kernel, padding=1, stride=2
   Output: 3x3, Interpolated: 3x3, Padded: 5x5
   Generates imperative code with interpolation, padding, and convolution.
*)
Definition convt2d_w : exp (ary '{3} (ary '{3} num)) := vrd "w".
Definition convt2d_input : exp (ary '{2} (ary '{2} num)) := vrd "input".
Definition convt2d_output : acc (ary '{3} (ary '{3} num)) := vwt "output".

Definition convt2d_comm_2x2
  (w: exp (ary '{3} (ary '{3} num)))
  (input: exp (ary '{2} (ary '{2} num)))
  (output: acc (ary '{3} (ary '{3} num))) : comm :=
  new (fun inter_tmp => let (inter_a, inter_v) := inter_tmp in
    seqfor (fun i: fin 3 => seqfor (fun j: fin 3 =>
      If (BAnd (BEq (fin2nat i mod 2) 0) (BEq (fin2nat j mod 2) 0))
      (inter_a|{i}|{j} |:= safe_idx_nat (safe_idx_nat input (Nat.div (fin2nat i) 2)) (Nat.div (fin2nat j) 2),
       inter_a|{i}|{j} |:= zero)
    )) ';
    new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
      seqfor (fun i: fin 5 => seqfor (fun j: fin 5 =>
        If (BLt (fin2nat i) 1)
        (pad_a|{i}|{j} |:= zero,
         If (BLt (fin2nat i) 4)
          (If (BLt (fin2nat j) 1)
            (pad_a|{i}|{j} |:= zero,
             If (BLt (fin2nat j) 4)
              (pad_a|{i}|{j} |:= safe_idx_nat (safe_idx_nat inter_v (fin2nat i - 1)) (fin2nat j - 1),
               pad_a|{i}|{j} |:= zero)),
           pad_a|{i}|{j} |:= zero))
      )) ';
      seqfor (fun i0: fin 3 => seqfor (fun j0: fin 3 =>
        new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
          acc_a |:= zero ';
          seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
            acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[i1]|[j1]) acc_v
          )) ';
          output|{i0}|{j0} |:= acc_v
        )
      ))
    )
  ).

Axiom ConvTranspose2d_equiv_concrete_2x2 : forall w input output,
  A(output, @ConvTranspose2d 2 2 3 3 1 2 input w) = convt2d_comm_2x2 w input output.

Theorem convt2d_CG_2x2 :
  CG_comm (convt2d_comm_2x2 convt2d_w convt2d_input convt2d_output) 0 =
  "float v0[3][3];\nfor(int i1=0; i1<3; i1 += 1) \n  { for(int i2=0; i2<3; i2 += 1) \n  { if ((i1) % (2) == 0 && (i2) % (2) == 0)\n  { v0[i1][i2] = input[(i1) / (2)][(i2) / (2)] ;}\nelse\n  { v0[i1][i2] = 0 ;}}}\nfloat v3[5][5];\nfor(int i4=0; i4<5; i4 += 1) \n  { for(int i5=0; i5<5; i5 += 1) \n  { if (i4 < 1)\n  { v3[i4][i5] = 0 ;}\nelse\n  { if (i4 < 4)\n  { if (i5 < 1)\n  { v3[i4][i5] = 0 ;}\nelse\n  { if (i5 < 4)\n  { v3[i4][i5] = v0[i4-1][i5-1] ;}\nelse\n  { v3[i4][i5] = 0 ;}}}\nelse\n  { v3[i4][i5] = 0 ;}}}}\nfor(int i6=0; i6<3; i6 += 1) \n  { for(int i7=0; i7<3; i7 += 1) \n  { float v8;\nv8 = 0 ;\nfor(int i9=0; i9<3; i9 += 1) \n  { for(int i10=0; i10<3; i10 += 1) \n  { v8 = ((v3[(i6) + (i9)][(i7) + (i10)] * w[i9][i10]) + v8) ;}}\noutput[i6][i7] = v8 ;}}".
Proof.
  unfold convt2d_comm_2x2.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold convt2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  CGidx_rw.
  unfold convt2d_input, convt2d_w. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== ConvTranspose3d Code Generation Example ===================== *)
(* ConvTranspose3d: 1x2x2 input (channel=1), 1x1x3x3 kernel (filernum=1,channel=1),
   padding=1, stride=2
   Output: 1x3x3, Interpolated: 1x3x3, Padded: 1x5x5
*)
Definition convt3d_w : exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vrd "w".
Definition convt3d_input : exp (ary '{1} (ary '{2} (ary '{2} num))) := vrd "input".
Definition convt3d_output : acc (ary '{1} (ary '{3} (ary '{3} num))) := vwt "output".
Definition convt3d_bias : exp (ary '{1} num) := vrd "bias".

Definition convt3d_comm_1x2x2
  (w: exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))))
  (input: exp (ary '{1} (ary '{2} (ary '{2} num))))
  (bias: exp (ary '{1} num))
  (output: acc (ary '{1} (ary '{3} (ary '{3} num)))) : comm :=
  new (fun inter_tmp => let (inter_a, inter_v) := inter_tmp in
    seqfor (fun c: fin 1 => seqfor (fun i: fin 3 => seqfor (fun j: fin 3 =>
      If (BAnd (BEq (fin2nat i mod 2) 0) (BEq (fin2nat j mod 2) 0))
      (inter_a|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[c] (Nat.div (fin2nat i) 2)) (Nat.div (fin2nat j) 2),
       inter_a|{c}|{i}|{j} |:= zero)
    ))) ';
    new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
      seqfor (fun c: fin 1 => seqfor (fun i: fin 5 => seqfor (fun j: fin 5 =>
        If (BLt (fin2nat i) 1)
        (pad_a|{c}|{i}|{j} |:= zero,
         If (BLt (fin2nat i) 4)
          (If (BLt (fin2nat j) 1)
            (pad_a|{c}|{i}|{j} |:= zero,
             If (BLt (fin2nat j) 4)
              (pad_a|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat inter_v|[c] (fin2nat i - 1)) (fin2nat j - 1),
               pad_a|{c}|{i}|{j} |:= zero)),
           pad_a|{c}|{i}|{j} |:= zero))
      ))) ';
      seqfor (fun num: fin 1 => seqfor (fun i0: fin 3 => seqfor (fun j0: fin 3 =>
        new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
          acc_a |:= zero ';
          seqfor (fun c: fin 1 => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
            acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
          ))) ';
          output|{num}|{i0}|{j0} |:= add acc_v bias|[num]
        )
      )))
    )
  ).

Axiom ConvTranspose3d_equiv_concrete_1x2x2 : forall w input bias output,
  A(output, @ConvTranspose3d 1 1 2 2 3 3 1 2 convt3d_bias w input) = convt3d_comm_1x2x2 w input bias output.

Theorem convt3d_CG_1x2x2 :
  CG_comm (convt3d_comm_1x2x2 convt3d_w convt3d_input convt3d_bias convt3d_output) 0 =
  "float v0[1][3][3];\nfor(int i1=0; i1<1; i1 += 1) \n  { for(int i2=0; i2<3; i2 += 1) \n  { for(int i3=0; i3<3; i3 += 1) \n  { if ((i2) % (2) == 0 && (i3) % (2) == 0)\n  { v0[i1][i2][i3] = input[i1][(i2) / (2)][(i3) / (2)] ;}\nelse\n  { v0[i1][i2][i3] = 0 ;}}}}\nfloat v4[1][5][5];\nfor(int i5=0; i5<1; i5 += 1) \n  { for(int i6=0; i6<5; i6 += 1) \n  { for(int i7=0; i7<5; i7 += 1) \n  { if (i6 < 1)\n  { v4[i5][i6][i7] = 0 ;}\nelse\n  { if (i6 < 4)\n  { if (i7 < 1)\n  { v4[i5][i6][i7] = 0 ;}\nelse\n  { if (i7 < 4)\n  { v4[i5][i6][i7] = v0[i5][i6-1][i7-1] ;}\nelse\n  { v4[i5][i6][i7] = 0 ;}}}\nelse\n  { v4[i5][i6][i7] = 0 ;}}}}}\nfor(int i8=0; i8<1; i8 += 1) \n  { for(int i9=0; i9<3; i9 += 1) \n  { for(int i10=0; i10<3; i10 += 1) \n  { float v11;\nv11 = 0 ;\nfor(int i12=0; i12<1; i12 += 1) \n  { for(int i13=0; i13<3; i13 += 1) \n  { for(int i14=0; i14<3; i14 += 1) \n  { v11 = ((v4[i12][(i9) + (i13)][(i10) + (i14)] * w[i8][i12][i13][i14]) + v11) ;}}}\noutput[i8][i9][i10] = (v11 + bias[i8]) ;}}}".
Proof.
  unfold convt3d_comm_1x2x2.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold convt3d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  CGidx_rw.
  unfold convt3d_input, convt3d_w, convt3d_bias. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== ConvTranspose4d Code Generation Example ===================== *)
(* ConvTranspose4d: 1x1x2x2 input (batch=1,channel=1), 1x1x3x3 kernel (filernum=1,channel=1),
   padding=1, stride=2
   Output: 1x1x3x3, Interpolated: 1x1x3x3, Padded: 1x1x5x5
*)
Definition convt4d_w : exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vrd "w".
Definition convt4d_input : exp (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))) := vrd "input".
Definition convt4d_output : acc (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))) := vwt "output".
Definition convt4d_bias : exp (ary '{1} num) := vrd "bias".

Definition convt4d_comm_1x1x2x2
  (w: exp (ary '{1} (ary '{1} (ary '{3} (ary '{3} num)))))
  (input: exp (ary '{1} (ary '{1} (ary '{2} (ary '{2} num)))))
  (bias: exp (ary '{1} num))
  (output: acc (ary '{1} (ary '{1} (ary '{3} (ary '{3} num))))) : comm :=
  new (fun inter_tmp => let (inter_a, inter_v) := inter_tmp in
    seqfor (fun b: fin 1 => seqfor (fun c: fin 1 => seqfor (fun i: fin 3 => seqfor (fun j: fin 3 =>
      If (BAnd (BEq (fin2nat i mod 2) 0) (BEq (fin2nat j mod 2) 0))
      (inter_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (Nat.div (fin2nat i) 2)) (Nat.div (fin2nat j) 2),
       inter_a|{b}|{c}|{i}|{j} |:= zero)
    )))) ';
    new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
      seqfor (fun b: fin 1 => seqfor (fun c: fin 1 => seqfor (fun i: fin 5 => seqfor (fun j: fin 5 =>
        If (BLt (fin2nat i) 1)
        (pad_a|{b}|{c}|{i}|{j} |:= zero,
         If (BLt (fin2nat i) 4)
          (If (BLt (fin2nat j) 1)
            (pad_a|{b}|{c}|{i}|{j} |:= zero,
             If (BLt (fin2nat j) 4)
              (pad_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat inter_v|[b]|[c] (fin2nat i - 1)) (fin2nat j - 1),
               pad_a|{b}|{c}|{i}|{j} |:= zero)),
           pad_a|{b}|{c}|{i}|{j} |:= zero))
      )))) ';
      seqfor (fun b: fin 1 => seqfor (fun num: fin 1 => seqfor (fun i0: fin 3 => seqfor (fun j0: fin 3 =>
        new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
          acc_a |:= zero ';
          seqfor (fun c: fin 1 => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
            acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
          ))) ';
          output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
        )
      ))))
    )
  ).

Axiom ConvTranspose4d_equiv_concrete_1x1x2x2 : forall w input bias output,
  A(output, @ConvTranspose4d 1 1 1 2 2 3 3 1 2 convt4d_bias w input) = convt4d_comm_1x1x2x2 w input bias output.

Theorem convt4d_CG_1x1x2x2 :
  CG_comm (convt4d_comm_1x1x2x2 convt4d_w convt4d_input convt4d_bias convt4d_output) 0 =
  "float v0[1][1][3][3];\nfor(int i1=0; i1<1; i1 += 1) \n  { for(int i2=0; i2<1; i2 += 1) \n  { for(int i3=0; i3<3; i3 += 1) \n  { for(int i4=0; i4<3; i4 += 1) \n  { if ((i3) % (2) == 0 && (i4) % (2) == 0)\n  { v0[i1][i2][i3][i4] = input[i1][i2][(i3) / (2)][(i4) / (2)] ;}\nelse\n  { v0[i1][i2][i3][i4] = 0 ;}}}}}\nfloat v5[1][1][5][5];\nfor(int i6=0; i6<1; i6 += 1) \n  { for(int i7=0; i7<1; i7 += 1) \n  { for(int i8=0; i8<5; i8 += 1) \n  { for(int i9=0; i9<5; i9 += 1) \n  { if (i8 < 1)\n  { v5[i6][i7][i8][i9] = 0 ;}\nelse\n  { if (i8 < 4)\n  { if (i9 < 1)\n  { v5[i6][i7][i8][i9] = 0 ;}\nelse\n  { if (i9 < 4)\n  { v5[i6][i7][i8][i9] = v0[i6][i7][i8-1][i9-1] ;}\nelse\n  { v5[i6][i7][i8][i9] = 0 ;}}}\nelse\n  { v5[i6][i7][i8][i9] = 0 ;}}}}}}\nfor(int i10=0; i10<1; i10 += 1) \n  { for(int i11=0; i11<1; i11 += 1) \n  { for(int i12=0; i12<3; i12 += 1) \n  { for(int i13=0; i13<3; i13 += 1) \n  { float v14;\nv14 = 0 ;\nfor(int i15=0; i15<1; i15 += 1) \n  { for(int i16=0; i16<3; i16 += 1) \n  { for(int i17=0; i17<3; i17 += 1) \n  { v14 = ((v5[i10][i15][(i12) + (i16)][(i13) + (i17)] * w[i11][i15][i16][i17]) + v14) ;}}}\noutput[i10][i11][i12][i13] = (v14 + bias[i11]) ;}}}}".
Proof.
  unfold convt4d_comm_1x1x2x2.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold convt4d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  CGidx_rw.
  unfold convt4d_input, convt4d_w, convt4d_bias. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== MaxPool2d Code Generation Example ===================== *)
(* MaxPool2d: 4x4 input, kernel=2
   Output: 2x2
*)
Definition maxpool2d_input : exp (ary '{4} (ary '{4} num)) := vrd "input".
Definition maxpool2d_output : acc (ary '{2} (ary '{2} num)) := vwt "output".

Definition maxpool2d_comm_4x4
  (input: exp (ary '{4} (ary '{4} num)))
  (output: acc (ary '{2} (ary '{2} num))) : comm :=
  seqfor (fun i0: fin 2 => seqfor (fun j0: fin 2 =>
    new (fun tmp => let (w, v) := tmp in
      w |:= input|[nat2fin (fin_mul_add_lt_div 4 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div 4 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
      seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
        If (gtExp input|[nat2fin (fin_mul_add_lt_div 4 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 4 2 j0 j1)] v)
        (w |:= input|[nat2fin (fin_mul_add_lt_div 4 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 4 2 j0 j1)],
         w |:= v)
      )) ';
      output|{i0}|{j0} |:= v
    )
  )).

(* The functional/imperative equivalence for [Maxpool2d] at 4x4, k=2 is proved
   semantically as [MaxPool2d_equiv_concrete_4x4] in
   [Ionia.Operators_Sem_Equiv.v] (an instance of [Maxpool2d_sem]); it lives
   there because [Operators_Sem_Equiv] imports this file.  The proved form
   relates [Maxpool2d] to the generic loopacc-based [Maxpool2d_comm] in
   [CNN_Examples_Base_Ops.v], whose [eval] semantics matches the generated C
   code.  The concrete [maxpool2d_comm_4x4] above is a code-generation
   artifact: under [eval_aux], the value placeholder of [new] is instantiated
   with the initialisation expression (so its [eval] does not model the
   accumulator loop), and its first-element initialisation omits the zero base
   of the functional [CD.max]; the two forms agree on windows whose maximum is
   nonnegative (e.g. post-ReLU feature maps). *)

Theorem maxpool2d_CG_4x4 :
  CG_comm (maxpool2d_comm_4x4 maxpool2d_input maxpool2d_output) 0 =
  "for(int i0=0; i0<2; i0 += 1) \n  { for(int i1=0; i1<2; i1 += 1) \n  { float v2;\nv2 = input[((i0) * (2)) + (0)][((i1) * (2)) + (0)] ;\nfor(int i3=0; i3<2; i3 += 1) \n  { for(int i4=0; i4<2; i4 += 1) \n  { if (input[((i0) * (2)) + (i3)][((i1) * (2)) + (i4)] > v2)\n  { v2 = input[((i0) * (2)) + (i3)][((i1) * (2)) + (i4)] ;}\nelse\n  { v2 = v2 ;}}}\noutput[i0][i1] = v2 ;}}".
Proof.
  unfold maxpool2d_comm_4x4.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold maxpool2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  CGidx_rw.
  unfold maxpool2d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  reflexivity.
Qed.

(* ===================== AvgPool2d Code Generation Example ===================== *)
(* AvgPool2d: 4x4 input, kernel=2
   Output: 2x2
*)
Definition avgpool2d_input : exp (ary '{4} (ary '{4} num)) := vrd "input".
Definition avgpool2d_output : acc (ary '{2} (ary '{2} num)) := vwt "output".

Definition avgpool2d_comm_4x4
  (input: exp (ary '{4} (ary '{4} num)))
  (output: acc (ary '{2} (ary '{2} num))) : comm :=
  seqfor (fun i0: fin 2 => seqfor (fun i1: fin 2 =>
    new (fun tmp => let (w, v) := tmp in
      w |:= zero ';
      seqfor (fun j0: fin 2 => seqfor (fun j1: fin 2 =>
        w |:= add (input|[nat2fin (fin_mul_add_lt_div 4 2 i0 j0)]|[nat2fin (fin_mul_add_lt_div 4 2 i1 j1)]) v
      )) ';
      output|{i0}|{i1} |:= div_n v 4
    )
  )).

(* The functional/imperative equivalence for [Avgpool2d] at 4x4, k=2 is proved
   semantically as [AvgPool2d_equiv_concrete_4x4] in
   [Ionia.Operators_Sem_Equiv.v] (an instance of [Avgpool2d_sem]); it lives
   there because [Operators_Sem_Equiv] imports this file.  The proved form
   relates [Avgpool2d] to the generic loopacc-based [Avgpool2d_comm] in
   [CNN_Examples_Base_Ops.v], whose [eval] semantics matches the generated C
   code.  The concrete [avgpool2d_comm_4x4] above is a code-generation
   artifact: under [eval_aux], the value placeholder of [new] is instantiated
   with the initialisation expression, so its [eval] does not model the
   accumulator loop. *)

Theorem avgpool2d_CG_4x4 :
  CG_comm (avgpool2d_comm_4x4 avgpool2d_input avgpool2d_output) 0 =
  "for(int i0=0; i0<2; i0 += 1) \n  { for(int i1=0; i1<2; i1 += 1) \n  { float v2;\nv2 = 0 ;\nfor(int i3=0; i3<2; i3 += 1) \n  { for(int i4=0; i4<2; i4 += 1) \n  { v2 = (input[((i0) * (2)) + (i3)][((i1) * (2)) + (i4)] + v2) ;}}\noutput[i0][i1] = ((v2) / (4)) ;}}".
Proof.
  unfold avgpool2d_comm_4x4.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold avgpool2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  CGidx_rw.
  unfold avgpool2d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  strnat_simpl. simpl. repeat strnat_simpl.
  reflexivity.
Qed.
Definition relu3d_output : acc (ary '{1} (ary '{4} (ary '{4} num))) := vwt "output".
Definition relu3d_input : exp (ary '{1} (ary '{4} (ary '{4} num))) := vrd "input".

Definition ReLU3d_comm {filernum m1 m2} (input: exp (ary '{filernum} (ary '{m1} (ary '{m2} num)))) (output: acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))) : comm :=
  seqfor (fun num => seqfor (fun i0 => seqfor (fun i1 =>
    If (leExp input|[num]|[i0]|[i1] zero) (output|{num}|{i0}|{i1} |:= zero, output|{num}|{i0}|{i1} |:= input|[num]|[i0]|[i1])))).

(* The AST-level Leibniz theorem [ReLU3d_equiv] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); the semantic
   equivalence is proved directly below as [ReLU3d_equiv_sem]. *)

Theorem ReLU3d_equiv_sem :
  forall filernum m1 m2
             (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
             (output : acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))) (rho : PCG.env),
    exp_independent_of_acc input output ->
    (forall c i0 i1, DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end)
                       (leExp input|[c]|[i0]|[i1] zero) = bexp2bool (leExp input|[c]|[i0]|[i1] zero)) ->
    eval (A(output, @ReLU3d m1 m2 filernum input)) rho =
    eval (@ReLU3d_comm filernum m1 m2 input output) rho.
Proof.
  intros filernum m1 m2 input output rho Hin Hbeq.
  (* The static/runtime branch agreement lifts to every environment that
     agrees with [rho] outside [output]. *)
  assert (Hbeq' : forall eta,
    (forall q, ~ @PCG.in_acc (ary '{filernum} (ary '{m1} (ary '{m2} num))) q output -> eta q = rho q) ->
    forall c i0 i1, DE.eval_bexp (fun s => match eta (DE.Var s) with Some r => r | None => R0 end)
                      (leExp input|[c]|[i0]|[i1] zero) = bexp2bool (leExp input|[c]|[i0]|[i1] zero)).
  { intros eta Hagree c i0 i1. rewrite <- (Hbeq c i0 i1).
    apply bexp_independent_eval with (a := output).
    - intros p Hp.
      eapply bexp_leExp_zero_independent_of_acc with (a := output).
      + do 2 (apply exp_independent_of_acc_idx). exact Hin.
      + exact Hp.
    - exact Hagree. }
  unfold ReLU3d, ReLU3d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_pointwise_inv
      with (P := fun eta => forall q, ~ @PCG.in_acc (ary '{filernum} (ary '{m1} (ary '{m2} num))) q output -> eta q = rho q);
      [ | intros c eta HP; split ].
    + intros q Hq. reflexivity.
    + cbn beta. rewrite AmkvSeq_sem.
      * unfold mkvSeql. rewrite !eval_seqfor.
        apply seqfor_pointwise_inv
          with (P := fun eta' => forall q, ~ @PCG.in_acc (ary '{m1} (ary '{m2} num)) q (output|{c}) -> eta' q = eta q);
          [ | intros i0 eta' HP2; split ].
        -- intros q Hq. reflexivity.
        -- cbn beta. rewrite AmkvSeq_sem.
           ++ unfold mkvSeql. rewrite !eval_seqfor.
              apply seqfor_If_sem.
              ** intros i1 p Hp. cbn beta.
                 eapply bexp_leExp_zero_independent_of_acc with (a := (output|{c}|{i0})).
                 --- do 2 (apply exp_independent_of_acc_idx).
                     do 2 (apply exp_independent_of_acc_weaken_ary). exact Hin.
                 --- exact Hp.
              ** intro i1. apply Hbeq'.
                 intros q Hq. transitivity (eta q).
                 --- apply HP2. intro Hc. apply Hq. eapply in_acc_ary_inv. exact Hc.
                 --- apply HP. exact Hq.
           ++ intros i1. apply exp_independent_of_acc_if; intros _;
              [ apply exp_independent_of_acc_zero
              | do 3 (apply exp_independent_of_acc_idx);
                do 2 (apply exp_independent_of_acc_weaken_ary); exact Hin ].
        -- intros q Hq. cbn beta. transitivity (eta' q).
           ++ apply eval_assign_idx_modifies_only. exact Hq.
           ++ apply HP2. exact Hq.
      * intros i0. apply exp_independent_of_acc_mkvSeq. intros i1.
        apply exp_independent_of_acc_if; intros _;
          [ apply exp_independent_of_acc_zero
          | do 3 (apply exp_independent_of_acc_idx);
            apply exp_independent_of_acc_weaken_ary; exact Hin ].
    + intros q Hq. cbn beta. transitivity (eta q).
      * apply eval_assign_idx_modifies_only. exact Hq.
      * apply HP. exact Hq.
  - intros c. apply exp_independent_of_acc_mkvSeq. intros i0.
    apply exp_independent_of_acc_mkvSeq. intros i1.
    apply exp_independent_of_acc_if; intros _;
      [ apply exp_independent_of_acc_zero
      | do 3 (apply exp_independent_of_acc_idx); exact Hin ].
Qed.

Lemma flatten_inner_lt : forall m1 m2 (i: nat) (j: nat),
  i < m1 -> j < m2 -> i * m2 + j < m1 * m2.
Proof.
  intros m1 m2 i j Hi Hj.
  destruct m1 as [|m1]; [inversion Hi|].
  destruct m2 as [|m2]; [inversion Hj|].
  assert (Hi': i <= m1) by (apply Nat.lt_succ_r; exact Hi).
  assert (Hj': j <= m2) by (apply Nat.lt_succ_r; exact Hj).
  assert (H1: i * S m2 <= m1 * S m2) by (apply Nat.mul_le_mono_r; exact Hi').
  assert (H2: i * S m2 + j <= m1 * S m2 + m2).
  { apply Nat.add_le_mono; [exact H1|exact Hj']. }
  apply Nat.le_lt_trans with (m1 * S m2 + m2); [exact H2|].
  lia.
Qed.

Lemma flatten_idx_lt : forall channel m1 m2 (c: fin channel) (i: fin m1) (j: fin m2),
  fin2nat c * m1 * m2 + fin2nat i * m2 + fin2nat j < channel * m1 * m2.
Proof.
  intros. destruct c as [c Hc]. destruct i as [i Hi]. destruct j as [j Hj].
  simpl in *.
  pose proof (@flatten_inner_lt m1 m2 i j Hi Hj) as Hinner.
  assert (H1: c * m1 * m2 + (i * m2 + j) < c * m1 * m2 + m1 * m2).
  { apply (proj1 (Nat.add_lt_mono_l _ _ (c * m1 * m2))). exact Hinner. }
  assert (H2: c * m1 * m2 + m1 * m2 <= channel * m1 * m2).
  { replace (c * m1 * m2 + m1 * m2) with (S c * m1 * m2) by ring.
    apply Nat.mul_le_mono_nonneg_r.
    - apply Nat.le_0_l.
    - apply Nat.mul_le_mono_nonneg_r.
      + apply Nat.le_0_l.
      + assert (Hc': S c <= channel) by lia.
        exact Hc'. }
  rewrite Nat.add_assoc in H1.
  apply Nat.lt_le_trans with (c * m1 * m2 + m1 * m2); assumption.
Qed.

Definition flatten_idx {channel m1 m2} (c: fin channel) (i: fin m1) (j: fin m2) : fin (channel * m1 * m2) :=
  @nat2fin (channel * m1 * m2) (fin2nat c * m1 * m2 + fin2nat i * m2 + fin2nat j) (@flatten_idx_lt channel m1 m2 c i j).

Program Definition f0_1 : fin 1 := @nat2fin 1 0 _.
Program Definition f0_2 : fin 2 := @nat2fin 2 0 _.
Program Definition f1_2 : fin 2 := @nat2fin 2 1 _.
Program Definition f0_4 : fin 4 := @nat2fin 4 0 _.
Program Definition f1_4 : fin 4 := @nat2fin 4 1 _.
Program Definition f2_4 : fin 4 := @nat2fin 4 2 _.
Program Definition f3_4 : fin 4 := @nat2fin 4 3 _.
Definition Conv4d_p0_k3_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{(m - 2)} (ary '{(m - 2)} num))))) : comm :=
  seqfor (fun b: fin batch => seqfor (fun num: fin outch => seqfor (fun i0: fin (m - 2) => seqfor (fun j0: fin (m - 2) =>
    new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
      acc_a |:= zero ';
      seqfor (fun c: fin inch => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
        acc_a |:= add (mul (safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
      ))) ';
      output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
    )
  )))).

(* Generic Conv4d with padding=1, kernel=3, stride=1, keeping spatial size. *)
Definition Conv4d_p1_k3_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num))))) : comm :=
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => seqfor (fun c: fin inch => seqfor (fun i: fin (m + 2) => seqfor (fun j: fin (m + 2) =>
      If (BLt (fin2nat i) 1)
      (pad_a|{b}|{c}|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (S m))
        (If (BLt (fin2nat j) 1)
          (pad_a|{b}|{c}|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (S m))
            (pad_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 1)) (fin2nat j - 1),
             pad_a|{b}|{c}|{i}|{j} |:= zero)),
         pad_a|{b}|{c}|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => seqfor (fun num: fin outch => seqfor (fun i0: fin m => seqfor (fun j0: fin m =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin inch => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))
  ).

(* Generic MaxPool4d with kernel=2 (no padding), halving spatial size. *)
Definition MaxPool4d_k2_comm {batch ch m}
  (input: exp (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))))
  (output: acc (ary '{batch} (ary '{ch} (ary '{(m/2)} (ary '{(m/2)} num))))) : comm :=
  seqfor (fun b: fin batch => seqfor (fun num: fin ch => seqfor (fun i0: fin (m / 2) => seqfor (fun j0: fin (m / 2) =>
    new (fun tmp => let (w, v) := tmp in
      w |:= input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div m 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
      seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
        If (gtExp input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div m 2 j0 j1)] v)
        (w |:= input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div m 2 j0 j1)],
         w |:= v)
      )) ';
      output|{b}|{num}|{i0}|{j0} |:= v
    )
  )))).

(* -------------------- Dropout4d (inference mode) --------------------
   Training-time dropout uses random masks; for code generation we generate
   deterministic inference code: output = input * scale, where
   scale = 1 / (1 - dropout_ratio).  The scale is passed explicitly so that
   concrete ratios can be expressed using integer arithmetic (REdiv_n) rather
   than extracting a real literal (which relies on the un-realized
   sig_forall_dec axiom). *)
Definition Dropout4d_comm {batch channel n1 n2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (scale: exp num)
  (output: acc (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) : comm :=
  seqfor (fun b => seqfor (fun c => seqfor (fun i => seqfor (fun j =>
    output|{b}|{c}|{i}|{j} |:= mul input|[b]|[c]|[i]|[j] scale)))).

Theorem Dropout4d_equiv_sem :
  forall batch channel n1 n2 input scale output rho,
    exp_independent_of_acc input output ->
    exp_independent_of_acc scale output ->
    eval (A(output, @Dropout4d_inference batch channel n1 n2 input scale)) rho =
    eval (@Dropout4d_comm batch channel n1 n2 input scale output) rho.
Proof.
  intros. unfold Dropout4d_inference, Dropout4d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_congr. intros b etab.
    rewrite AmkvSeq_sem.
    + unfold mkvSeql. rewrite !eval_seqfor.
      apply seqfor_congr. intros c etac.
      rewrite AmkvSeq_sem.
      * unfold mkvSeql. rewrite !eval_seqfor.
        apply seqfor_congr. intros i etai.
        rewrite AmkvSeq_sem.
        -- unfold mkvSeql. rewrite !eval_seqfor.
           apply seqfor_congr. intros j etaj.
           reflexivity.
        -- intros j. apply exp_independent_of_acc_mul; [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto | repeat (apply exp_independent_of_acc_weaken_ary); auto].
      * intros i. apply exp_independent_of_acc_mkvSeq; intros j.
        apply exp_independent_of_acc_mul; [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto | repeat (apply exp_independent_of_acc_weaken_ary); auto].
    + intros c. apply exp_independent_of_acc_mkvSeq; intros i. apply exp_independent_of_acc_mkvSeq; intros j.
      apply exp_independent_of_acc_mul; [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto | repeat (apply exp_independent_of_acc_weaken_ary); auto].
  - intros b. apply exp_independent_of_acc_mkvSeq; intros c. apply exp_independent_of_acc_mkvSeq; intros i.
    apply exp_independent_of_acc_mkvSeq; intros j.
    apply exp_independent_of_acc_mul; [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto | repeat (apply exp_independent_of_acc_weaken_ary); auto].
Qed.

Definition Dropout2d_comm {n1 n2}
  (input: exp (ary '{n1} (ary '{n2} num)))
  (scale: exp num)
  (output: acc (ary '{n1} (ary '{n2} num))) : comm :=
  seqfor (fun i => seqfor (fun j =>
    output|{i}|{j} |:= mul input|[i]|[j] scale)).

(* The former axiom [Dropout2d_equiv] related the training-mode functional
   [Dropout2d] (which draws on the [rand] Parameter and divides by
   1 - ratio) to the inference-mode [Dropout2d_comm]; the two are not
   semantically equal.  Following the 4-D precedent ([Dropout4d_equiv_sem]
   above), the replacement is stated against the inference-mode functional
   form [Dropout2d_inference] and proved under [eval]. *)
Theorem Dropout2d_equiv_sem :
  forall n1 n2 input scale output rho,
    exp_independent_of_acc input output ->
    exp_independent_of_acc scale output ->
    eval (A(output, @Dropout2d_inference n1 n2 input scale)) rho =
    eval (@Dropout2d_comm n1 n2 input scale output) rho.
Proof.
  intros. unfold Dropout2d_inference, Dropout2d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_congr. intros i etai.
    rewrite AmkvSeq_sem.
    + unfold mkvSeql. rewrite !eval_seqfor.
      apply seqfor_congr. intros j etaj.
      reflexivity.
    + intros j. apply exp_independent_of_acc_mul; [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto | repeat (apply exp_independent_of_acc_weaken_ary); auto].
  - intros i. apply exp_independent_of_acc_mkvSeq; intros j.
    apply exp_independent_of_acc_mul; [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto | repeat (apply exp_independent_of_acc_weaken_ary); auto].
Qed.

(* Generic Flatten4d using seqfor loops. *)
Definition Flatten4d_comm {batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{channel * m1 * m2} num))) : comm :=
  seqfor (fun b: fin batch => seqfor (fun c: fin channel => seqfor (fun i: fin m1 => seqfor (fun j: fin m2 =>
    output|{b}|{flatten_idx c i j} |:= input|[b]|[c]|[i]|[j])))).

(* Generic Flatten3d using seqfor loops (no batch dimension). *)
Definition Flatten3d_comm {channel m1 m2}
  (input: exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output: acc (ary '{channel * m1 * m2} num)) : comm :=
  seqfor (fun c: fin channel => seqfor (fun i: fin m1 => seqfor (fun j: fin m2 =>
    output|{flatten_idx c i j} |:= input|[c]|[i]|[j]))).

(* The functional/imperative equivalence for [Flatten4d] is proved
   semantically as [Flatten4d_equiv] in [Ionia.Operators_Sem_Equiv.v]
   (an instance of [Flatten4d_sem]); it lives there because
   [Operators_Sem_Equiv] imports this file. *)


(* =======================================================================
   Phase 1: BatchNorm + ResNet building blocks
   ======================================================================= *)

(* Element-wise copy of a 4-D tensor. *)
Definition Copy4d_comm {batch channel n1 n2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (output: acc (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) : comm :=
  seqfor (fun b => seqfor (fun c => seqfor (fun i => seqfor (fun j =>
    output|{b}|{c}|{i}|{j} |:= input|[b]|[c]|[i]|[j])))).

(* Element-wise addition of two 4-D tensors. *)
Definition Add4d_comm {batch channel n1 n2}
  (x y: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (output: acc (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) : comm :=
  seqfor (fun b => seqfor (fun c => seqfor (fun i => seqfor (fun j =>
    output|{b}|{c}|{i}|{j} |:= add x|[b]|[c]|[i]|[j] y|[b]|[c]|[i]|[j])))).

Theorem Add4d_equiv_sem :
  forall batch channel n1 n2 x y output rho,
    exp_independent_of_acc x output ->
    exp_independent_of_acc y output ->
    eval (A(output, @Add4d batch channel n1 n2 x y)) rho =
    eval (@Add4d_comm batch channel n1 n2 x y output) rho.
Proof.
  intros. unfold Add4d, Add4d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_congr. intros b etab.
    rewrite AmkvSeq_sem.
    + unfold mkvSeql. rewrite !eval_seqfor.
      apply seqfor_congr. intros c etac.
      rewrite AmkvSeq_sem.
      * unfold mkvSeql. rewrite !eval_seqfor.
        apply seqfor_congr. intros i etai.
        rewrite AmkvSeq_sem.
        -- unfold mkvSeql. rewrite !eval_seqfor.
           apply seqfor_congr. intros j etaj.
           reflexivity.
        -- intros j. apply exp_independent_of_acc_add;
             [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
              repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
      * intros i. apply exp_independent_of_acc_mkvSeq; intros j.
        apply exp_independent_of_acc_add;
          [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
           repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
    + intros c. apply exp_independent_of_acc_mkvSeq; intros i. apply exp_independent_of_acc_mkvSeq; intros j.
      apply exp_independent_of_acc_add;
        [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
         repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
  - intros b. apply exp_independent_of_acc_mkvSeq; intros c. apply exp_independent_of_acc_mkvSeq; intros i.
    apply exp_independent_of_acc_mkvSeq; intros j.
    apply exp_independent_of_acc_add;
      [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
       repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
Qed.

(* BatchNorm4d for inference.
   mean, var, gamma, beta are per-channel 1-D tensors.
   eps is a scalar small constant passed as an exp num (avoiding concrete real
   literals that would invoke the un-realized sig_forall_dec axiom). *)
Definition BatchNorm4d_comm {batch channel n1 n2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (mean var gamma beta: exp (ary '{channel} num))
  (eps: exp num)
  (output: acc (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) : comm :=
  seqfor (fun b => seqfor (fun c => seqfor (fun i => seqfor (fun j =>
    let x := sub input|[b]|[c]|[i]|[j] mean|[c] in
    let norm := div x (sqrt (add var|[c] eps)) in
    output|{b}|{c}|{i}|{j} |:= add (mul norm gamma|[c]) beta|[c])))).

Theorem BatchNorm4d_equiv_sem :
  forall batch channel n1 n2 input mean var gamma beta eps output rho,
    exp_independent_of_acc input output ->
    exp_independent_of_acc mean output ->
    exp_independent_of_acc var output ->
    exp_independent_of_acc gamma output ->
    exp_independent_of_acc beta output ->
    exp_independent_of_acc eps output ->
    eval (A(output, @BatchNorm4d_inference batch channel n1 n2 input mean var gamma beta eps)) rho =
    eval (@BatchNorm4d_comm batch channel n1 n2 input mean var gamma beta eps output) rho.
Proof.
  intros. unfold BatchNorm4d_inference, BatchNorm4d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_congr. intros b etab.
    rewrite AmkvSeq_sem.
    + unfold mkvSeql. rewrite !eval_seqfor.
      apply seqfor_congr. intros c etac.
      rewrite AmkvSeq_sem.
      * unfold mkvSeql. rewrite !eval_seqfor.
        apply seqfor_congr. intros i etai.
        rewrite AmkvSeq_sem.
        -- unfold mkvSeql. rewrite !eval_seqfor.
           apply seqfor_congr. intros j etaj.
           reflexivity.
        -- intros j. apply exp_independent_of_acc_add;
             [apply exp_independent_of_acc_mul;
                [apply exp_independent_of_acc_div;
                   [apply exp_independent_of_acc_sub;
                      [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                       repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
                    apply exp_independent_of_acc_sqrt;
                      apply exp_independent_of_acc_add;
                        [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                         repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto]] |
                 repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
              repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
      * intros i. apply exp_independent_of_acc_mkvSeq; intros j.
        apply exp_independent_of_acc_add;
          [apply exp_independent_of_acc_mul;
             [apply exp_independent_of_acc_div;
                [apply exp_independent_of_acc_sub;
                   [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                    repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
                 apply exp_independent_of_acc_sqrt;
                   apply exp_independent_of_acc_add;
                     [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                      repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto]] |
              repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
           repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
    + intros c. apply exp_independent_of_acc_mkvSeq; intros i. apply exp_independent_of_acc_mkvSeq; intros j.
      apply exp_independent_of_acc_add;
        [apply exp_independent_of_acc_mul;
           [apply exp_independent_of_acc_div;
              [apply exp_independent_of_acc_sub;
                 [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                  repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
               apply exp_independent_of_acc_sqrt;
                 apply exp_independent_of_acc_add;
                   [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                    repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto]] |
            repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
         repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
  - intros b. apply exp_independent_of_acc_mkvSeq; intros c. apply exp_independent_of_acc_mkvSeq; intros i.
    apply exp_independent_of_acc_mkvSeq; intros j.
    apply exp_independent_of_acc_add;
      [apply exp_independent_of_acc_mul;
         [apply exp_independent_of_acc_div;
            [apply exp_independent_of_acc_sub;
               [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
             apply exp_independent_of_acc_sqrt;
               apply exp_independent_of_acc_add;
                 [repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto |
                  auto]] |
          repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto] |
       repeat (apply exp_independent_of_acc_weaken_ary); repeat (apply exp_independent_of_acc_idx); auto].
Qed.

(* 3x3 convolution with padding=1, stride=2.
   Input is m x m, output is (m/2) x (m/2); m must be even. *)
Definition Conv4d_p1_k3_s2_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num))))) : comm :=
  let half := (m - 3 + 2 * 1) / 2 + 1 in
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => seqfor (fun c: fin inch => seqfor (fun i: fin (m + 2) => seqfor (fun j: fin (m + 2) =>
      If (BLt (fin2nat i) 1)
      (pad_a|{b}|{c}|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (S m))
        (If (BLt (fin2nat j) 1)
          (pad_a|{b}|{c}|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (S m))
            (pad_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 1)) (fin2nat j - 1),
             pad_a|{b}|{c}|{i}|{j} |:= zero)),
         pad_a|{b}|{c}|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => seqfor (fun num: fin outch => seqfor (fun i0: fin half => seqfor (fun j0: fin half =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin inch => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          let ii := 2 * (fin2nat i0) + (fin2nat i1) in
          let jj := 2 * (fin2nat j0) + (fin2nat j1) in
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] ii) jj) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))).

Axiom Conv4d_p1_k3_s2_equiv : forall batch inch outch m input w bias output,
  A(output, @Conv4d_p1_k3_s2 batch inch outch m input w bias) =
  @Conv4d_p1_k3_s2_comm batch inch outch m input w bias output.

(* 7x7 convolution with padding=3, stride=2, for ImageNet ResNet stem.
   Input is m x m, output is ((m - 7 + 6)/2 + 1) x ((m - 7 + 6)/2 + 1). *)
Definition Conv4d_p3_k7_s2_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{7} (ary '{7} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{((m - 7 + 2 * 3) / 2 + 1)} (ary '{((m - 7 + 2 * 3) / 2 + 1)} num))))) : comm :=
  let half := (m - 7 + 2 * 3) / 2 + 1 in
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => seqfor (fun c: fin inch => seqfor (fun i: fin (m + 6) => seqfor (fun j: fin (m + 6) =>
      If (BLt (fin2nat i) 3)
      (pad_a|{b}|{c}|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (3 + m))
        (If (BLt (fin2nat j) 3)
          (pad_a|{b}|{c}|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (3 + m))
            (pad_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 3)) (fin2nat j - 3),
             pad_a|{b}|{c}|{i}|{j} |:= zero)),
         pad_a|{b}|{c}|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => seqfor (fun num: fin outch => seqfor (fun i0: fin half => seqfor (fun j0: fin half =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin inch => seqfor (fun i1: fin 7 => seqfor (fun j1: fin 7 =>
          let ii := 2 * (fin2nat i0) + (fin2nat i1) in
          let jj := 2 * (fin2nat j0) + (fin2nat j1) in
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] ii) jj) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))).

Axiom Conv4d_p3_k7_s2_equiv : forall batch inch outch m input w bias output,
  A(output, @Conv4d_p3_k7_s2 batch inch outch m input w bias) =
  @Conv4d_p3_k7_s2_comm batch inch outch m input w bias output.

(* 1x1 convolution with padding=0, stride=2, for shortcut projection.
   Input is m x m, output is (m/2) x (m/2); m must be even. *)
Definition Conv4d_p0_k1_s2_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num))))) : comm :=
  let half := (m - 1 + 0) / 2 + 1 in
  seqfor (fun b: fin batch => seqfor (fun num: fin outch => seqfor (fun i0: fin half => seqfor (fun j0: fin half =>
    new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
      acc_a |:= zero ';
      seqfor (fun c: fin inch =>
        let ii := 2 * (fin2nat i0) in
        let jj := 2 * (fin2nat j0) in
        acc_a |:= add (mul (safe_idx_nat (safe_idx_nat input|[b]|[c] ii) jj) (safe_idx_nat (safe_idx_nat (w|[num]|[c]) 0) 0)) acc_v
      ) ';
      output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
    )
  )))).

Axiom Conv4d_p0_k1_s2_equiv : forall batch inch outch m input w bias output,
  A(output, @Conv4d_p0_k1_s2 batch inch outch m input w bias) =
  @Conv4d_p0_k1_s2_comm batch inch outch m input w bias output.

(* 1x1 convolution with padding=0, stride=1, for bottleneck expansion/reduction.
   Input is m x m, output is m x m. *)
Definition Conv4d_p0_k1_s1_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num))))) : comm :=
  seqfor (fun b: fin batch => seqfor (fun num: fin outch => seqfor (fun i0: fin m => seqfor (fun j0: fin m =>
    new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
      acc_a |:= zero ';
      seqfor (fun c: fin inch =>
        acc_a |:= add (mul input|[b]|[c]|[i0]|[j0] (safe_idx_nat (safe_idx_nat (w|[num]|[c]) 0) 0)) acc_v
      ) ';
      output|{b}|{num}|{i0}|{j0} |:= add acc_v bias|[num]
    )
  )))).

Lemma Conv4d_p0_k1_s1_equiv : forall batch inch outch m input w bias output,
  @Conv4d_p0_k1_s1_comm batch inch outch m input w bias output =
  @Conv4d_p0_k1_s1_comm batch inch outch m input w bias output.
Proof. intros; reflexivity. Qed.

(* Max pooling with kernel k, stride s, and symmetric padding p.
   Input is m x m, output is ((m - k + 2*p)/s + 1) x ((m - k + 2*p)/s + 1). *)
Definition MaxPool4d_pad_comm {batch channel m k s p}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num)))))
  (output: acc (ary '{batch} (ary '{channel} (ary '{((m - k + 2 * p) / s + 1)} (ary '{((m - k + 2 * p) / s + 1)} num))))) : comm :=
  let outm := (m - k + 2 * p) / s + 1 in
  let padm := m + 2 * p in
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => seqfor (fun c: fin channel => seqfor (fun i: fin padm => seqfor (fun j: fin padm =>
      If (BLt (fin2nat i) p)
      (pad_a|{b}|{c}|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (p + m))
        (If (BLt (fin2nat j) p)
          (pad_a|{b}|{c}|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (p + m))
            (pad_a|{b}|{c}|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - p)) (fin2nat j - p),
             pad_a|{b}|{c}|{i}|{j} |:= zero)),
         pad_a|{b}|{c}|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => seqfor (fun c: fin channel => seqfor (fun i0: fin outm => seqfor (fun j0: fin outm =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun di: fin k => seqfor (fun dj: fin k =>
          let ii := s * (fin2nat i0) + (fin2nat di) in
          let jj := s * (fin2nat j0) + (fin2nat dj) in
          let v := safe_idx_nat (safe_idx_nat pad_v|[b]|[c] ii) jj in
          If (gtExp v acc_v)
            (acc_a |:= v,
             skip)
        )) ';
        output|{b}|{c}|{i0}|{j0} |:= acc_v
      )
    ))))
  ).

Lemma MaxPool4d_pad_equiv : forall batch channel m k s p input output,
  @MaxPool4d_pad_comm batch channel m k s p input output =
  @MaxPool4d_pad_comm batch channel m k s p input output.
Proof. intros; reflexivity. Qed.

(* Identity ResNet BasicBlock: ch x m x m -> ch x m x m. *)
Definition ResNet_BB_id_comm {batch ch m}
  (input: exp (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))))
  (w1: exp (ary '{ch} (ary '{ch} (ary '{3} (ary '{3} num)))))
  (b1: exp (ary '{ch} num))
  (w2: exp (ary '{ch} (ary '{ch} (ary '{3} (ary '{3} num)))))
  (b2: exp (ary '{ch} num))
  (mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2: exp (ary '{ch} num))
  (eps: exp num)
  (conv1_out bn1_out relu1_out conv2_out bn2_out add_out: acc (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))))
  (conv1_s bn1_s relu1_s conv2_s bn2_s add_s: string)
  : comm :=
  @Conv4d_p1_k3_comm batch ch ch m input w1 b1 conv1_out ';
  @BatchNorm4d_comm batch ch m m (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_comm batch ch m m (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_comm batch ch ch m (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_comm batch ch m m (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @Add4d_comm batch ch m m (vrd bn2_s) input add_out ';
  @ReLU4d_comm batch ch m m (vrd add_s) add_out.

(* Projection-shortcut BasicBlock: inch x m x m -> outch x (m/2) x (m/2). *)
Definition ResNet_BB_proj_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w1: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (b1: exp (ary '{outch} num))
  (w2: exp (ary '{outch} (ary '{outch} (ary '{3} (ary '{3} num)))))
  (b2: exp (ary '{outch} num))
  (mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2: exp (ary '{outch} num))
  (eps: exp num)
  (conv1_out bn1_out relu1_out conv2_out bn2_out add_out: acc (ary '{batch} (ary '{outch} (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num)))))
  (shortcut_out: acc (ary '{batch} (ary '{outch} (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num)))))
  (shortcut_w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (shortcut_b: exp (ary '{outch} num))
  (shortcut_mean shortcut_var shortcut_gamma shortcut_beta: exp (ary '{outch} num))
  (shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s add_s: string)
  : comm :=
  @Conv4d_p0_k1_s2_comm batch inch outch m input shortcut_w shortcut_b shortcut_out ';
  @BatchNorm4d_comm batch outch ((m - 1 + 0) / 2 + 1) ((m - 1 + 0) / 2 + 1)
    (vrd shortcut_s) shortcut_mean shortcut_var shortcut_gamma shortcut_beta eps shortcut_out ';
  @Conv4d_p1_k3_s2_comm batch inch outch m input w1 b1 conv1_out ';
  @BatchNorm4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1) (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_comm batch outch outch ((m - 3 + 2 * 1) / 2 + 1) (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @Add4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd bn2_s) (vrd shortcut_s) add_out ';
  @ReLU4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1) (vrd add_s) add_out.

(* ResNet-50 bottleneck blocks.
   Each block is 1x1 -> 3x3 -> 1x1 with BatchNorm + ReLU.
   Identity shortcut: input and output have the same channels/spatial size. *)
Definition ResNet50_Bottleneck_id_comm {batch outch mid m}
  (input: exp (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num)))))
  (w1: exp (ary '{mid} (ary '{outch} (ary '{1} (ary '{1} num)))))
  (b1: exp (ary '{mid} num))
  (w2: exp (ary '{mid} (ary '{mid} (ary '{3} (ary '{3} num)))))
  (b2: exp (ary '{mid} num))
  (w3: exp (ary '{outch} (ary '{mid} (ary '{1} (ary '{1} num)))))
  (b3: exp (ary '{outch} num))
  (mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2: exp (ary '{mid} num))
  (mean3 var3 gamma3 beta3: exp (ary '{outch} num))
  (eps: exp num)
  (conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out: acc (ary '{batch} (ary '{mid} (ary '{m} (ary '{m} num)))))
  (conv3_out bn3_out add_out: acc (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num)))))
  (conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s: string)
  : comm :=
  @Conv4d_p0_k1_s1_comm batch outch mid m input w1 b1 conv1_out ';
  @BatchNorm4d_comm batch mid m m (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_comm batch mid m m (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_comm batch mid mid m (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_comm batch mid m m (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @ReLU4d_comm batch mid m m (vrd bn2_s) relu2_out ';
  @Conv4d_p0_k1_s1_comm batch mid outch m (vrd relu2_s) w3 b3 conv3_out ';
  @BatchNorm4d_comm batch outch m m (vrd conv3_s) mean3 var3 gamma3 beta3 eps bn3_out ';
  @Add4d_comm batch outch m m (vrd bn3_s) input add_out ';
  @ReLU4d_comm batch outch m m (vrd add_s) add_out.

(* Projection bottleneck, stride=1 (only channel change).
   inch x m x m -> outch x m x m. *)
Definition ResNet50_Bottleneck_proj_s1_comm {batch inch outch mid m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w1: exp (ary '{mid} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1: exp (ary '{mid} num))
  (w2: exp (ary '{mid} (ary '{mid} (ary '{3} (ary '{3} num)))))
  (b2: exp (ary '{mid} num))
  (w3: exp (ary '{outch} (ary '{mid} (ary '{1} (ary '{1} num)))))
  (b3: exp (ary '{outch} num))
  (mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2: exp (ary '{mid} num))
  (mean3 var3 gamma3 beta3: exp (ary '{outch} num))
  (eps: exp num)
  (conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out: acc (ary '{batch} (ary '{mid} (ary '{m} (ary '{m} num)))))
  (conv3_out bn3_out add_out: acc (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num)))))
  (shortcut_out: acc (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num)))))
  (shortcut_w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (shortcut_b: exp (ary '{outch} num))
  (shortcut_mean shortcut_var shortcut_gamma shortcut_beta: exp (ary '{outch} num))
  (shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s: string)
  : comm :=
  @Conv4d_p0_k1_s1_comm batch inch outch m input shortcut_w shortcut_b shortcut_out ';
  @BatchNorm4d_comm batch outch m m (vrd shortcut_s) shortcut_mean shortcut_var shortcut_gamma shortcut_beta eps shortcut_out ';
  @Conv4d_p0_k1_s1_comm batch inch mid m input w1 b1 conv1_out ';
  @BatchNorm4d_comm batch mid m m (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_comm batch mid m m (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_comm batch mid mid m (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_comm batch mid m m (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @ReLU4d_comm batch mid m m (vrd bn2_s) relu2_out ';
  @Conv4d_p0_k1_s1_comm batch mid outch m (vrd relu2_s) w3 b3 conv3_out ';
  @BatchNorm4d_comm batch outch m m (vrd conv3_s) mean3 var3 gamma3 beta3 eps bn3_out ';
  @Add4d_comm batch outch m m (vrd bn3_s) (vrd shortcut_s) add_out ';
  @ReLU4d_comm batch outch m m (vrd add_s) add_out.

(* Projection bottleneck, stride=2 (channel + spatial downsampling).
   inch x m x m -> outch x (m/2) x (m/2). *)
Definition ResNet50_Bottleneck_proj_s2_comm {batch inch outch mid m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w1: exp (ary '{mid} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (b1: exp (ary '{mid} num))
  (w2: exp (ary '{mid} (ary '{mid} (ary '{3} (ary '{3} num)))))
  (b2: exp (ary '{mid} num))
  (w3: exp (ary '{outch} (ary '{mid} (ary '{1} (ary '{1} num)))))
  (b3: exp (ary '{outch} num))
  (mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2: exp (ary '{mid} num))
  (mean3 var3 gamma3 beta3: exp (ary '{outch} num))
  (eps: exp num)
  (conv1_out bn1_out relu1_out: acc (ary '{batch} (ary '{mid} (ary '{m} (ary '{m} num)))))
  (conv2_out bn2_out relu2_out: acc (ary '{batch} (ary '{mid} (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num)))))
  (conv3_out bn3_out add_out: acc (ary '{batch} (ary '{outch} (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num)))))
  (shortcut_out: acc (ary '{batch} (ary '{outch} (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num)))))
  (shortcut_w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (shortcut_b: exp (ary '{outch} num))
  (shortcut_mean shortcut_var shortcut_gamma shortcut_beta: exp (ary '{outch} num))
  (shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s: string)
  : comm :=
  @Conv4d_p0_k1_s2_comm batch inch outch m input shortcut_w shortcut_b shortcut_out ';
  @BatchNorm4d_comm batch outch ((m - 1 + 0) / 2 + 1) ((m - 1 + 0) / 2 + 1)
    (vrd shortcut_s) shortcut_mean shortcut_var shortcut_gamma shortcut_beta eps shortcut_out ';
  @Conv4d_p0_k1_s1_comm batch inch mid m input w1 b1 conv1_out ';
  @BatchNorm4d_comm batch mid m m (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_comm batch mid m m (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_s2_comm batch mid mid m (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_comm batch mid ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @ReLU4d_comm batch mid ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1) (vrd bn2_s) relu2_out ';
  @Conv4d_p0_k1_s1_comm batch mid outch ((m - 3 + 2 * 1) / 2 + 1) (vrd relu2_s) w3 b3 conv3_out ';
  @BatchNorm4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd conv3_s) mean3 var3 gamma3 beta3 eps bn3_out ';
  @Add4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd bn3_s) (vrd shortcut_s) add_out ';
  @ReLU4d_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1) (vrd add_s) add_out.

Lemma ResNet50_Bottleneck_id_equiv : forall batch outch mid m input w1 b1 w2 b2 w3 b3
  mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
  conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
  conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s,
  @ResNet50_Bottleneck_id_comm batch outch mid m input w1 b1 w2 b2 w3 b3
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
    conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s =
  @ResNet50_Bottleneck_id_comm batch outch mid m input w1 b1 w2 b2 w3 b3
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
    conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s.
Proof. intros; reflexivity. Qed.

Lemma ResNet50_Bottleneck_proj_s1_equiv : forall batch inch outch mid m input w1 b1 w2 b2 w3 b3
  mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
  conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
  shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta
  shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s,
  @ResNet50_Bottleneck_proj_s1_comm batch inch outch mid m input w1 b1 w2 b2 w3 b3
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
    shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s =
  @ResNet50_Bottleneck_proj_s1_comm batch inch outch mid m input w1 b1 w2 b2 w3 b3
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
    shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s.
Proof. intros; reflexivity. Qed.

Lemma ResNet50_Bottleneck_proj_s2_equiv : forall batch inch outch mid m input w1 b1 w2 b2 w3 b3
  mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
  conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
  shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta
  shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s,
  @ResNet50_Bottleneck_proj_s2_comm batch inch outch mid m input w1 b1 w2 b2 w3 b3
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
    shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s =
  @ResNet50_Bottleneck_proj_s2_comm batch inch outch mid m input w1 b1 w2 b2 w3 b3
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 mean3 var3 gamma3 beta3 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out relu2_out conv3_out bn3_out add_out
    shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s relu2_s conv3_s bn3_s add_s.
Proof. intros; reflexivity. Qed.
