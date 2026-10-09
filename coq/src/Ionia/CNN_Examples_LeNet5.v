(* LeNet-5 imperative AST *)

Require Import Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.Operators_Sem_Equiv.
Require Import Logic.FunctionalExtensionality.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.
Opaque CG_acc CG_exp.

(* ===================== LeNet-5 Layer 1 Model Composition ===================== *)
(* Composes Conv2d (4x4, 3x3 kernel, pad=1, stride=1) + ReLU2d + MaxPool2d (k=2)
   Demonstrates end-to-end verified C code generation for a multi-operator layer.
*)
Definition lenet_layer1_comm : comm :=
  (conv2d_comm_4x4 conv2d_w_4x4 conv2d_input_4x4 (vwt "conv_out")) ';
  (@ReLU2d_comm 4 4 (vrd "conv_out") (vwt "relu_out")) ';
  (maxpool2d_comm_4x4 (vrd "relu_out") (vwt "output")).

Theorem lenet_layer1_CG :
  CG_comm lenet_layer1_comm 0 = 
  "float v0[6][6];\nfor(int i1=0; i1<6; i1 += 1) \n  { for(int i2=0; i2<6; i2 += 1) \n  { if (i1 < 1)\n  { v0[i1][i2] = 0 ;}\nelse\n  { if (i1 < 5)\n  { if (i2 < 1)\n  { v0[i1][i2] = 0 ;}\nelse\n  { if (i2 < 5)\n  { v0[i1][i2] = input[i1-1][i2-1] ;}\nelse\n  { v0[i1][i2] = 0 ;}}}\nelse\n  { v0[i1][i2] = 0 ;}}}}\nfor(int i3=0; i3<4; i3 += 1) \n  { for(int i4=0; i4<4; i4 += 1) \n  { float v5;\nv5 = 0 ;\nfor(int i6=0; i6<3; i6 += 1) \n  { for(int i7=0; i7<3; i7 += 1) \n  { v5 = ((v0[(i3) + (i6)][(i4) + (i7)] * w[i6][i7]) + v5) ;}}\nconv_out[i3][i4] = v5 ;}}\nfor(int i8=0; i8<4; i8 += 1) \n  { for(int i9=0; i9<4; i9 += 1) \n  { if (conv_out[i8][i9] <= 0)\n  { relu_out[i8][i9] = 0 ;}\nelse\n  { relu_out[i8][i9] = conv_out[i8][i9] ;}}}\nfor(int i10=0; i10<2; i10 += 1) \n  { for(int i11=0; i11<2; i11 += 1) \n  { float v12;\nv12 = relu_out[((i10) * (2)) + (0)][((i11) * (2)) + (0)] ;\nfor(int i13=0; i13<2; i13 += 1) \n  { for(int i14=0; i14<2; i14 += 1) \n  { if (relu_out[((i10) * (2)) + (i13)][((i11) * (2)) + (i14)] > v12)\n  { v12 = relu_out[((i10) * (2)) + (i13)][((i11) * (2)) + (i14)] ;}\nelse\n  { v12 = v12 ;}}}\noutput[i10][i11] = v12 ;}}".
Proof.
  unfold lenet_layer1_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold conv2d_output_4x4. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  unfold relu2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  unfold maxpool2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGsafe_idx_nat.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold conv2d_input_4x4, conv2d_w_4x4. repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  unfold relu2d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  unfold maxpool2d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  unfold zero.
  repeat rewrite CGadd.
  repeat rewrite CGmul.
  repeat strnat_simpl. simpl. repeat strnat_simpl.
  Exprw.
  repeat (first [ rewrite CGexpvar_gen by CGvar_side | rewrite CGexpvar_gen_oob ]).
  rewrite ?applyps_nil, ?applyps_Aidx.
  repeat strnat_simpl.
  reflexivity.
Qed.

(* ===================== Softmax1d Code Generation Example ===================== *)
(* Real Softmax1d: tlet s := sum (mkvSeq (fun i => pExp input|[i])) in
                  mkvSeq (fun j => div (pExp input|[j]) s)
   Generates cached-sum imperative code with exp() calls.
*)
Definition softmax1d_input : exp (ary '{3} num) := vrd "input".
Definition softmax1d_output : acc (ary '{3} num) := vwt "output".

Definition Softmax1d_comm_3 (input:exp (ary '{3} num)) (output:acc (ary '{3} num)) : comm :=
  new (fun tmp => let (w,v) := tmp in
    (w |:= zero) '; 
    seqfor (fun i => w |:= add (pExp (input|[i])) v) '; 
    seqfor (fun j => output|{j} |:= div (pExp (input|[j])) v)).

(* The functional/imperative equivalence for [Softmax1d] at n=3 is proved
   semantically as [Softmax1d_equiv_3] in [Ionia.Operators_Sem_Equiv.v]
   (an instance of [Softmax1d_sem]); it lives there to keep this file free
   of a dependency on [Operators_Sem_Equiv]. *)

Theorem softmax1d_CG_3 :
  CG_comm (Softmax1d_comm_3 softmax1d_input softmax1d_output) 0 = 
  "float v0;\nv0 = 0 ;\nfor(int i1=0; i1<3; i1 += 1) \n  { v0 = (exp(input[i1]) + v0) ;}\nfor(int i2=0; i2<3; i2 += 1) \n  { output[i2] = (exp(input[i2])) / (v0) ;}".
Proof.
  unfold Softmax1d_comm_3.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  rewrite CGaccvar_gen by CGvar_side.
  simpl.
  rewrite CGadd.
  simpl.
  rewrite CGpExp.
  simpl.
  rewrite CGidx.
  unfold softmax1d_input.
  rewrite CGexpvar_gen by CGvar_side.
  try rewrite exp_zero.
  rewrite CGexpvar_gen by CGvar_side.
  simpl.
  rewrite CGdiv.
  simpl.
  rewrite CGpExp.
  simpl.
  rewrite CGidx.
  unfold softmax1d_input.
  rewrite CGexpvar_gen by CGvar_side.
  repeat rewrite CGidxAcc.
  unfold softmax1d_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  compute. reflexivity.
Qed.

(* ===================== Linear1d Code Generation Example ===================== *)
(* Linear {m=3, outnum=2}: dot-product + bias
   Generates outer loop over outputs, inner new-accumulator for dot-product.
*)
Definition linear1d_input : exp (ary '{3} num) := vrd "input".
Definition linear1d_w : exp (ary '{2} (ary '{3} num)) := vrd "w".
Definition linear1d_b : exp (ary '{2} num) := vrd "b".
Definition linear1d_output : acc (ary '{2} num) := vwt "output".

Definition Linear1d_comm_3_2 (w: exp (ary '{2} (ary '{3} num)))
  (b: exp (ary '{2} num)) (input: exp (ary '{3} num))
  (output: acc (ary '{2} num)) : comm :=
  seqfor (fun out =>
    new (fun tmp => let (w_acc, v) := tmp in
      (w_acc |:= zero) ';
      seqfor (fun i => w_acc |:= add (mul input|[i] w|[out]|[i]) v) ';
      output|{out} |:= add v b|[out])).

(* The functional/imperative equivalence for [Linear] at m=3, outnum=2 is
   proved semantically as [Linear1d_equiv_3_2] in
   [Ionia.Operators_Sem_Equiv.v] (an instance of [Linear1d_sem]); it lives
   there to keep this file free of a dependency on [Operators_Sem_Equiv]. *)

Theorem linear1d_CG_3_2 :
  CG_comm (Linear1d_comm_3_2 linear1d_w linear1d_b linear1d_input linear1d_output) 0 = 
  "for(int i0=0; i0<2; i0 += 1) \n  { float v1;\nv1 = 0 ;\nfor(int i2=0; i2<3; i2 += 1) \n  { v1 = ((input[i2] * w[i0][i2]) + v1) ;}\noutput[i0] = (v1 + b[i0]) ;}".
Proof.
  unfold Linear1d_comm_3_2.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGadd. simpl.
  repeat rewrite CGmul. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold linear1d_input, linear1d_w, linear1d_b.
  repeat rewrite CGexpvar_gen by CGvar_side.
  try rewrite exp_zero.
  repeat rewrite CGexpvar_gen by CGvar_side.
  simpl.
  repeat rewrite CGidxAcc.
  unfold linear1d_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  compute. reflexivity.
Qed.

Definition flatten3d_input : exp (ary '{1} (ary '{2} (ary '{2} num))) := vrd "input".
Definition flatten3d_output : acc (ary '{4} num) := vwt "output".

Definition Flatten3d_comm_1_2_2 (input: exp (ary '{1} (ary '{2} (ary '{2} num))))
  (output: acc (ary '{4} num)) : comm :=
  output|{f0_4} |:= input|[f0_1]|[f0_2]|[f0_2] ';
  output|{f1_4} |:= input|[f0_1]|[f0_2]|[f1_2] ';
  output|{f2_4} |:= input|[f0_1]|[f1_2]|[f0_2] ';
  output|{f3_4} |:= input|[f0_1]|[f1_2]|[f1_2].

(* The functional/imperative equivalence for [Flatten3d] at 1x2x2 is proved
   semantically as [Flatten3d_equiv_1_2_2] in [Ionia.Operators_Sem_Equiv.v]
   (an instance of [Flatten3d_sem]); it lives there to keep this file free
   of a dependency on [Operators_Sem_Equiv].  The proved form relates
   [Flatten3d] to the generic seqfor-based [Flatten3d_comm] in
   [CNN_Examples_Base.v], the semantically equivalent form of the unrolled
   [Flatten3d_comm_1_2_2] above. *)

Theorem flatten3d_CG_1_2_2 :
  CG_comm (Flatten3d_comm_1_2_2 flatten3d_input flatten3d_output) 0 = 
  "output[0] = input[0][0][0] ;\noutput[1] = input[0][0][1] ;\noutput[2] = input[0][1][0] ;\noutput[3] = input[0][1][1] ;".
Proof.
  unfold Flatten3d_comm_1_2_2.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold flatten3d_input.
  repeat rewrite CGexpvar_gen by CGvar_side.
  repeat rewrite CGidxAcc.
  unfold flatten3d_output.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

(* ===================== Parametric Code Generation Examples ===================== *)
(* These demonstrate Section-style parameterized proofs for arbitrary n > 0.
   Key mechanism: cnt_var_seqfor_n_pos / cnt_var_parfor_n_pos lemmas
   eliminate stuck match-n in cnt_var when n is a variable.
*)

(* -------------------- ReLU1d Parametric Code Generation -------------------- *)
Section ReLU1d_Parametric_CG.
Variable n : nat.
Hypothesis Hn : n > 0.
Hypothesis wtn : writeNat n = "n".

Definition relu1d_param_input : exp (ary '{n} num) := vrd "input".
Definition relu1d_param_output : acc (ary '{n} num) := vwt "output".

Theorem relu1d_parametric_CG :
  exists output,
    CG_comm (ReLU1d_comm relu1d_param_input relu1d_param_output) 0 = output.
Proof.
  eexists. reflexivity.
Qed.

End ReLU1d_Parametric_CG.

(* -------------------- Sum Parametric Code Generation -------------------- *)
Section Sum_Parametric_CG.
Variable n : nat.
Hypothesis Hn : n > 0.
Hypothesis wtn : writeNat n = "n".

Definition sum_param_input : exp (ary '{n} num) := vrd "input".

Theorem sum_parametric_CG :
  exists output,
    CG_comm (suml sum_param_input (fun x o => o |:= x) (fun r => skip)) 0 = output.
Proof.
  unfold suml.
  rewrite CGloopacc.
  rewrite CGseq. simpl cnt_var.
  rewrite CGassign.
  unfold sum_param_input. try rewrite exp_zero. rewrite CGexpvar_gen by CGvar_side.
  rewrite CGseq.
  setoid_rewrite (@cnt_var_seqfor_n_pos n Hn).
  simpl cnt_var.
  replace (1 + 0 + 1) with 2 by reflexivity.
  rewrite CGfor.
  rewrite CGassign.
  rewrite CGadd.
  rewrite CGidx. unfold sum_param_input. rewrite CGexpvar_gen by CGvar_side.
  rewrite CGexpvar_gen by CGvar_side.
  rewrite CGskip.
  simpl applyps.
  rewrite writeNat_str2fin.
  rewrite CGaccvar_gen by CGvar_side.
  unfold istr. unfold vstr.
  exists ("float v0;\nv0 = 0 ;\nfor(int i1=0; i1<" ++ writeNat n ++ "; i1 += 1) \n  { v0 = (input[i1] + v0) ;}\n/* skip */").
  simpl. rewrite wtn. reflexivity.
Qed.

End Sum_Parametric_CG.

(* -------------------- Softmax1d Parametric Code Generation -------------------- *)
Section Softmax1d_Parametric_CG.
Variable n : nat.
Hypothesis Hn : n > 0.
Hypothesis wtn : writeNat n = "n".

Definition softmax_param_input : exp (ary '{n} num) := vrd "input".
Definition softmax_param_output : acc (ary '{n} num) := vwt "output".

Definition Softmax1d_param_comm (input:exp (ary '{n} num)) (output:acc (ary '{n} num)) : comm :=
  new (fun tmp => let (w,v) := tmp in
    (w |:= zero) '; 
    seqfor (fun i => w |:= add (pExp (input|[i])) v) '; 
    seqfor (fun j => output|{j} |:= div (pExp (input|[j])) v)).

Theorem softmax1d_parametric_CG :
  exists output,
    CG_comm (Softmax1d_param_comm softmax_param_input softmax_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End Softmax1d_Parametric_CG.

(* -------------------- Linear1d Parametric Code Generation -------------------- *)
Section Linear1d_Parametric_CG.
Variable m n : nat.
Hypothesis Hm : m > 0.
Hypothesis Hn : n > 0.
Hypothesis wtm : writeNat m = "m".
Hypothesis wtn : writeNat n = "n".

Definition linear_param_w : exp (ary '{m} (ary '{n} num)) := vrd "w".
Definition linear_param_b : exp (ary '{m} num) := vrd "b".
Definition linear_param_input : exp (ary '{n} num) := vrd "input".
Definition linear_param_output : acc (ary '{m} num) := vwt "output".

Definition Linear1d_param_comm (w:exp (ary '{m} (ary '{n} num))) (b:exp (ary '{m} num))
  (input:exp (ary '{n} num)) (output:acc (ary '{m} num)) : comm :=
  seqfor (fun i =>
    new (fun tmp => let (s,v) := tmp in
      (s |:= zero) '; 
      seqfor (fun j => s |:= add (mul (w|[i]|[j]) (input|[j])) v) '; 
      output|{i} |:= add v (b|[i]))).

Theorem linear1d_parametric_CG :
  exists output,
    CG_comm (Linear1d_param_comm linear_param_w linear_param_b linear_param_input linear_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End Linear1d_Parametric_CG.

(* -------------------- ReLU2d Parametric Code Generation -------------------- *)
Section ReLU2d_Parametric_CG.
Variable m1 m2 : nat.
Hypothesis Hm1 : m1 > 0.
Hypothesis Hm2 : m2 > 0.
Hypothesis wtm1 : writeNat m1 = "m1".
Hypothesis wtm2 : writeNat m2 = "m2".

Definition relu2d_param_input : exp (ary '{m1} (ary '{m2} num)) := vrd "input".
Definition relu2d_param_output : acc (ary '{m1} (ary '{m2} num)) := vwt "output".

Definition ReLU2d_param_comm (input: exp (ary '{m1} (ary '{m2} num))) (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 => seqfor (fun i1 => 
    If (leExp input|[i0]|[i1] zero) (output|{i0}|{i1} |:= zero, output|{i0}|{i1} |:= input|[i0]|[i1]))).

Theorem relu2d_parametric_CG :
  exists output,
    CG_comm (ReLU2d_param_comm relu2d_param_input relu2d_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End ReLU2d_Parametric_CG.

(* -------------------- Add2d Parametric Code Generation -------------------- *)
Section Add2d_Parametric_CG.
Variable m1 m2 : nat.
Hypothesis Hm1 : m1 > 0.
Hypothesis Hm2 : m2 > 0.
Hypothesis wtm1 : writeNat m1 = "m1".
Hypothesis wtm2 : writeNat m2 = "m2".

Definition add2d_param_x : exp (ary '{m1} (ary '{m2} num)) := vrd "x".
Definition add2d_param_y : exp (ary '{m1} (ary '{m2} num)) := vrd "y".
Definition add2d_param_output : acc (ary '{m1} (ary '{m2} num)) := vwt "output".

Definition Add2d_param_comm (x y: exp (ary '{m1} (ary '{m2} num))) (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 => seqfor (fun i1 => output|{i0}|{i1} |:= add x|[i0]|[i1] y|[i0]|[i1])).

Theorem add2d_parametric_CG :
  exists output,
    CG_comm (Add2d_param_comm add2d_param_x add2d_param_y add2d_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End Add2d_Parametric_CG.

(* -------------------- PseudoSoftmax1d Parametric Code Generation -------------------- *)
Section PseudoSoftmax1d_Parametric_CG.
Variable n : nat.
Hypothesis Hn : n > 0.
Hypothesis wtn : writeNat n = "n".

Definition ps_param_input : exp (ary '{n} num) := vrd "input".
Definition ps_param_output : acc (ary '{n} num) := vwt "output".

Definition PseudoSoftmax1d_param_comm (input:exp (ary '{n} num)) (output:acc (ary '{n} num)) : comm :=
  new (fun tmp => let (w,v) := tmp in
    (w |:= zero) '; 
    seqfor (fun i => w |:= add (input|[i]) v) '; 
    seqfor (fun j => output|{j} |:= div (input|[j]) v)).

Theorem pseudo_softmax1d_parametric_CG :
  exists output,
    CG_comm (PseudoSoftmax1d_param_comm ps_param_input ps_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End PseudoSoftmax1d_Parametric_CG.

(* -------------------- AvgPool2d Parametric Code Generation -------------------- *)
Section AvgPool2d_Parametric_CG.
Variable m1 m2 k : nat.
Hypothesis Hm1 : m1 > 0.
Hypothesis Hm2 : m2 > 0.
Hypothesis Hk : k > 0.
Hypothesis Hm1k : m1 / k > 0.
Hypothesis Hm2k : m2 / k > 0.
Hypothesis wtm1 : writeNat m1 = "m1".
Hypothesis wtm2 : writeNat m2 = "m2".
Hypothesis wtk : writeNat k = "k".

Definition avgpool2d_param_input : exp (ary '{m1} (ary '{m2} num)) := vrd "input".
Definition avgpool2d_param_output : acc (ary '{(m1/k)} (ary '{(m2/k)} num)) := vwt "output".

Definition AvgPool2d_param_comm
  (input: exp (ary '{m1} (ary '{m2} num)))
  (output: acc (ary '{(m1/k)} (ary '{(m2/k)} num))) : comm :=
  seqfor (fun i0: fin (m1/k) => seqfor (fun i1: fin (m2/k) =>
    new (fun tmp => let (w, v) := tmp in
      w |:= zero ';
      seqfor (fun j0: fin k => seqfor (fun j1: fin k =>
        w |:= add (input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]) v
      )) ';
      output|{i0}|{i1} |:= div_n v (k*k)
    )
  )).

Theorem avgpool2d_parametric_CG :
  exists output,
    CG_comm (AvgPool2d_param_comm avgpool2d_param_input avgpool2d_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End AvgPool2d_Parametric_CG.

(* -------------------- MaxPool2d Parametric Code Generation -------------------- *)
(* Note: This is the imperative version using If+gtExp, not the functional max.
   The functional Maxpool2d uses [max] which contains [match n], making it
   difficult to parameterize. See docs/maxpool_parametrization_analysis.md
   for a detailed analysis of the [max] problem. *)
Section MaxPool2d_Parametric_CG.
Variable m1 m2 k : nat.
Hypothesis Hm1 : m1 > 0.
Hypothesis Hm2 : m2 > 0.
Hypothesis Hk : k > 0.
Hypothesis Hm1k : m1 / k > 0.
Hypothesis Hm2k : m2 / k > 0.
Hypothesis wtm1 : writeNat m1 = "m1".
Hypothesis wtm2 : writeNat m2 = "m2".
Hypothesis wtk : writeNat k = "k".

Definition maxpool2d_param_input : exp (ary '{m1} (ary '{m2} num)) := vrd "input".
Definition maxpool2d_param_output : acc (ary '{(m1/k)} (ary '{(m2/k)} num)) := vwt "output".

Definition MaxPool2d_param_comm
  (input: exp (ary '{m1} (ary '{m2} num)))
  (output: acc (ary '{(m1/k)} (ary '{(m2/k)} num))) : comm :=
  seqfor (fun i0: fin (m1/k) => seqfor (fun j0: fin (m2/k) =>
    new (fun tmp => let (w, v) := tmp in
      w |:= input|[nat2fin (fin_mul_add_lt_div m1 k i0 (@nat2fin k 0 Hk))]|[nat2fin (fin_mul_add_lt_div m2 k j0 (@nat2fin k 0 Hk))] ';
      seqfor (fun i1: fin k => seqfor (fun j1: fin k =>
        If (gtExp input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)] v)
        (w |:= input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)],
         w |:= v)
      )) ';
      output|{i0}|{j0} |:= v
    )
  )).

Theorem maxpool2d_parametric_CG :
  exists output,
    CG_comm (MaxPool2d_param_comm maxpool2d_param_input maxpool2d_param_output) 0 = output.
Proof.
  eexists.
  Exprw.
  reflexivity.
Qed.

End MaxPool2d_Parametric_CG.

(* ===================== Sigmoid1d Code Generation Example ===================== *)
(* Sigmoid1d: output = 1 / (1 + exp(-input))
   Generates a single sequential loop with exp() calls.
*)
Definition sigmoid1d_input : exp (ary '{3} num) := vrd "input".
Definition sigmoid1d_output : acc (ary '{3} num) := vwt "output".

Definition Sigmoid1d {n:nat} (input: exp (ary '{n} num)) :=
  mkvSeq (fun i:fin n => div one (add one (pExp (negate input|[i])))).

Definition Sigmoid1d_comm {n:nat} (input: exp (ary '{n} num)) (output: acc (ary '{n} num)) : comm :=
  seqfor (fun i => output|{i} |:= div one (add one (pExp (negate input|[i])))).

(* Independence of constant/unary scalar expressions, mirroring
   [exp_independent_of_acc_add] etc. in CNN_CodeGen_Semantics.v. *)
Lemma exp_independent_of_acc_one :
  forall d' (a : acc d'), exp_independent_of_acc one a.
Proof. intros d' a p Hp. reflexivity. Qed.

Lemma exp_independent_of_acc_negate :
  forall d' (x : exp num) (a : acc d'),
    exp_independent_of_acc x a -> exp_independent_of_acc (negate x) a.
Proof. intros d' x a Hx p Hp. simpl. apply Hx. exact Hp. Qed.

Lemma exp_independent_of_acc_pExp :
  forall d' (x : exp num) (a : acc d'),
    exp_independent_of_acc x a -> exp_independent_of_acc (pExp x) a.
Proof. intros d' x a Hx p Hp. simpl. apply Hx. exact Hp. Qed.

Theorem Sigmoid1d_equiv_sem : forall n input output rho,
  exp_independent_of_acc input output ->
  eval (A(output, Sigmoid1d input)) rho = eval (@Sigmoid1d_comm n input output) rho.
Proof.
  intros. unfold Sigmoid1d, Sigmoid1d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite eval_seqfor.
    apply seqfor_congr. intros i eta. reflexivity.
  - intros i. apply exp_independent_of_acc_div.
    + apply exp_independent_of_acc_one.
    + apply exp_independent_of_acc_add.
      * apply exp_independent_of_acc_one.
      * apply exp_independent_of_acc_pExp, exp_independent_of_acc_negate.
        apply exp_independent_of_acc_idx. exact H.
Qed.

Theorem sigmoid1d_CG :
  CG_comm (Sigmoid1d_comm sigmoid1d_input sigmoid1d_output) 0 =
  "for(int i0=0; i0<3; i0 += 1) \n  { output[i0] = (1) / ((1 + exp((- input[i0])))) ;}".
Proof.
  unfold Sigmoid1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  unfold sigmoid1d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGdiv. simpl.
  repeat rewrite exp_one.
  repeat rewrite CGadd. simpl.
  repeat rewrite CGpExp. simpl.
  repeat rewrite CGneg. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold sigmoid1d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

(* ===================== Tanh1d Code Generation Example ===================== *)
(* Tanh1d: output = (exp(input) - exp(-input)) / (exp(input) + exp(-input))
   Generates a single sequential loop with exp() calls.
*)
Definition tanh1d_input : exp (ary '{3} num) := vrd "input".
Definition tanh1d_output : acc (ary '{3} num) := vwt "output".

Definition Tanh1d {n:nat} (input: exp (ary '{n} num)) :=
  mkvSeq (fun i:fin n =>
    div (sub (pExp input|[i]) (pExp (negate input|[i])))
        (add (pExp input|[i]) (pExp (negate input|[i])))).

Definition Tanh1d_comm {n:nat} (input: exp (ary '{n} num)) (output: acc (ary '{n} num)) : comm :=
  seqfor (fun i =>
    output|{i} |:= div (sub (pExp input|[i]) (pExp (negate input|[i])))
                     (add (pExp input|[i]) (pExp (negate input|[i])))).

Theorem Tanh1d_equiv_sem : forall n input output rho,
  exp_independent_of_acc input output ->
  eval (A(output, Tanh1d input)) rho = eval (@Tanh1d_comm n input output) rho.
Proof.
  intros. unfold Tanh1d, Tanh1d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite eval_seqfor.
    apply seqfor_congr. intros i eta. reflexivity.
  - intros i. apply exp_independent_of_acc_div;
      apply exp_independent_of_acc_sub || apply exp_independent_of_acc_add;
      apply exp_independent_of_acc_pExp;
      try apply exp_independent_of_acc_negate;
      apply exp_independent_of_acc_idx; exact H.
Qed.

Theorem tanh1d_CG :
  CG_comm (Tanh1d_comm tanh1d_input tanh1d_output) 0 =
  "for(int i0=0; i0<3; i0 += 1) \n  { output[i0] = ((exp(input[i0]) - exp((- input[i0])))) / ((exp(input[i0]) + exp((- input[i0])))) ;}".
Proof.
  unfold Tanh1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  unfold tanh1d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGdiv. simpl.
  repeat rewrite CGsub. simpl.
  repeat rewrite CGadd. simpl.
  repeat rewrite CGpExp. simpl.
  repeat rewrite CGneg. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold tanh1d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

(* ===================== LeakyReLU1d Code Generation Example ===================== *)
(* LeakyReLU1d: output = input if input > 0 else slope * input
   Generates a single sequential loop with if-else.
*)
Definition leakyrelu1d_input : exp (ary '{3} num) := vrd "input".
Definition leakyrelu1d_slope : exp num := vrd "slope".
Definition leakyrelu1d_output : acc (ary '{3} num) := vwt "output".

Definition LeakyReLU1d {n:nat} (slope: exp num) (input: exp (ary '{n} num)) :=
  mkvSeq (fun i:fin n =>
    if bexp2bool (gtExp input|[i] zero) then input|[i] else mul slope input|[i]).

Definition LeakyReLU1d_comm {n:nat} (slope: exp num) (input: exp (ary '{n} num)) (output: acc (ary '{n} num)) : comm :=
  seqfor (fun i =>
    If (gtExp input|[i] zero)
      (output|{i} |:= input|[i], output|{i} |:= mul slope input|[i])).

(* The AST-level Leibniz theorem [LeakyReLU1d_equiv] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); the semantic
   equivalence is proved directly below as [LeakyReLU1d_equiv_sem]. *)

Theorem LeakyReLU1d_equiv_sem :
  forall n (slope : exp num) (input : exp (ary '{n} num))
         (output : acc (ary '{n} num)) (rho : PCG.env),
    exp_independent_of_acc input output ->
    exp_independent_of_acc slope output ->
    (forall i, DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end)
                 (gtExp input|[i] zero) = bexp2bool (gtExp input|[i] zero)) ->
    eval (A(output, @LeakyReLU1d n slope input)) rho =
    eval (@LeakyReLU1d_comm n slope input output) rho.
Proof.
  intros n slope input output rho Hin Hslope Hbeq.
  unfold LeakyReLU1d, LeakyReLU1d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. apply seqfor_If_sem.
    + intros i p Hp. cbn beta.
      eapply bexp_gtExp_zero_independent_of_acc with (a := output); eassumption.
    + exact Hbeq.
  - intros i. apply exp_independent_of_acc_if; intros _;
      [ apply exp_independent_of_acc_idx; exact Hin
      | apply exp_independent_of_acc_mul;
        [ exact Hslope | apply exp_independent_of_acc_idx; exact Hin ] ].
Qed.

Theorem leakyrelu1d_CG :
  CG_comm (LeakyReLU1d_comm leakyrelu1d_slope leakyrelu1d_input leakyrelu1d_output) 0 =
  "for(int i0=0; i0<3; i0 += 1) \n  { if (input[i0] > 0)\n  { output[i0] = input[i0] ;}\nelse\n  { output[i0] = (slope * input[i0]) ;}}".
Proof.
  unfold LeakyReLU1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  unfold leakyrelu1d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  try rewrite exp_zero.
  repeat simpl.
  repeat rewrite CGmul. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold leakyrelu1d_input, leakyrelu1d_slope. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

(* ===================== Mul2d Code Generation Example ===================== *)
(* Mul2d: output = x * y (element-wise, 2x3)
   Generates nested sequential loops.
*)
Definition mul2d_x : exp (ary '{2} (ary '{3} num)) := vrd "x".
Definition mul2d_y : exp (ary '{2} (ary '{3} num)) := vrd "y".
Definition mul2d_output : acc (ary '{2} (ary '{3} num)) := vwt "output".

Definition Mul2d_comm {m1 m2} (x y: exp (ary '{m1} (ary '{m2} num))) (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 => seqfor (fun i1 => output|{i0}|{i1} |:= mul x|[i0]|[i1] y|[i0]|[i1])).

Theorem Mul2d_equiv_sem : forall m1 m2 x y output rho,
  exp_independent_of_acc x output ->
  exp_independent_of_acc y output ->
  eval (A(output, @Mul2d m1 m2 x y)) rho = eval (@Mul2d_comm m1 m2 x y output) rho.
Proof.
  intros. unfold Mul2d, Mul2d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite eval_seqfor.
    apply seqfor_congr. intros i0 eta0.
    rewrite AmkvSeq_sem.
    + unfold mkvSeql. rewrite eval_seqfor.
      apply seqfor_congr. intros i1 eta1. reflexivity.
    + intros i1. apply exp_independent_of_acc_mul;
        [apply exp_independent_of_acc_idx; apply exp_independent_of_acc_weaken_ary; apply exp_independent_of_acc_idx; auto |
         apply exp_independent_of_acc_idx; apply exp_independent_of_acc_weaken_ary; apply exp_independent_of_acc_idx; auto].
  - intros i0. apply exp_independent_of_acc_mkvSeq; intros i1.
    apply exp_independent_of_acc_mul;
      [apply exp_independent_of_acc_idx; apply exp_independent_of_acc_idx; auto |
       apply exp_independent_of_acc_idx; apply exp_independent_of_acc_idx; auto].
Qed.

Theorem mul2d_CG :
  CG_comm (Mul2d_comm mul2d_x mul2d_y mul2d_output) 0 =
  "for(int i0=0; i0<2; i0 += 1) \n  { for(int i1=0; i1<3; i1 += 1) \n  { output[i0][i1] = (x[i0][i1] * y[i0][i1]) ;}}".
Proof.
  unfold Mul2d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  unfold mul2d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGmul. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold mul2d_x, mul2d_y. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.


(* ===================== ReLU3d Code Generation Example ===================== *)
(* ReLU3d: output = ReLU(input) for 1x4x4 tensor
   Generates triple nested sequential loops with if-else
*)

Theorem relu3d_CG :
  CG_comm (ReLU3d_comm relu3d_input relu3d_output) 0 =
  "for(int i0=0; i0<1; i0 += 1) \n  { for(int i1=0; i1<4; i1 += 1) \n  { for(int i2=0; i2<4; i2 += 1) \n  { if (input[i0][i1][i2] <= 0)\n  { output[i0][i1][i2] = 0 ;}\nelse\n  { output[i0][i1][i2] = input[i0][i1][i2] ;}}}}".
Proof.
  unfold ReLU3d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  unfold relu3d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl. simpl.
  try rewrite exp_zero.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGidx_rexp.
  repeat rewrite CGfor. simpl.
  unfold relu3d_input. repeat rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  simpl.
  reflexivity.
Qed.

(* ===================== MaxPool3d Code Generation Example ===================== *)
(* MaxPool3d: 1x4x4 input, kernel=2
   Output: 1x2x2
*)
Definition maxpool3d_input : exp (ary '{1} (ary '{4} (ary '{4} num))) := vrd "input".
Definition maxpool3d_output : acc (ary '{1} (ary '{2} (ary '{2} num))) := vwt "output".

Definition maxpool3d_comm_1x4x4
  (input: exp (ary '{1} (ary '{4} (ary '{4} num))))
  (output: acc (ary '{1} (ary '{2} (ary '{2} num)))) : comm :=
  seqfor (fun num: fin 1 => seqfor (fun i0: fin 2 => seqfor (fun j0: fin 2 =>
    new (fun tmp => let (w, v) := tmp in
      w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 4 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div 4 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
      seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
        If (gtExp input|[num]|[nat2fin (fin_mul_add_lt_div 4 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 4 2 j0 j1)] v)
        (w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 4 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 4 2 j0 j1)],
         w |:= v)
      )) ';
      output|{num}|{i0}|{j0} |:= v
    )
  ))).

(* The functional/imperative equivalence for [Maxpool3d] at 1x4x4, k=2 is
   proved semantically as [MaxPool3d_equiv_concrete_1x4x4] in
   [Ionia.Operators_Sem_Equiv.v] (an instance of [Maxpool3d_sem]); it lives
   there to keep this file free of a dependency on [Operators_Sem_Equiv].
   The proved form relates [Maxpool3d] to the generic loopacc-based
   [Maxpool3d_comm] in [CNN_Examples_Base_Ops.v], whose [eval] semantics
   matches the generated C code.  The concrete [maxpool3d_comm_1x4x4] above
   is a code-generation artifact: under [eval_aux], the value placeholder of
   [new] is instantiated with the initialisation expression (so its [eval]
   does not model the accumulator loop), and its first-element initialisation
   omits the zero base of the functional [CD.max]; the two forms agree on
   windows whose maximum is nonnegative (e.g. post-ReLU feature maps). *)

Theorem maxpool3d_CG_1x4x4 :
  CG_comm (maxpool3d_comm_1x4x4 maxpool3d_input maxpool3d_output) 0 =
  "for(int i0=0; i0<1; i0 += 1) \n  { for(int i1=0; i1<2; i1 += 1) \n  { for(int i2=0; i2<2; i2 += 1) \n  { float v3;\nv3 = input[i0][((i1) * (2)) + (0)][((i2) * (2)) + (0)] ;\nfor(int i4=0; i4<2; i4 += 1) \n  { for(int i5=0; i5<2; i5 += 1) \n  { if (input[i0][((i1) * (2)) + (i4)][((i2) * (2)) + (i5)] > v3)\n  { v3 = input[i0][((i1) * (2)) + (i4)][((i2) * (2)) + (i5)] ;}\nelse\n  { v3 = v3 ;}}}\noutput[i0][i1][i2] = v3 ;}}}".
Proof.
  unfold maxpool3d_comm_1x4x4.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  unfold maxpool3d_output. repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold maxpool3d_input. repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

(* ===================== LeNet-5 Full Network C Code Generation ===================== *)
(* We build the imperative AST for the complete LeNet-5 by composing already
   verified layer combinators.  The two Conv3d layers and the two MaxPool3d
   layers are kept abstract (Parameters) and linked to the functional
   definitions by Axioms, following the same style as Conv2d/3d/4d in the
   examples above.  The ReLU, Linear and Softmax layers are instantiated
   directly from the verified combinators defined earlier in this file.
*)

Definition lenet5_input : exp (ary '{1} (ary '{32} (ary '{32} num))) := vrd "input".
Definition lenet5_kc1 : exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))) := vrd "kc1".
Definition lenet5_bc1 : exp (ary '{6} num) := vrd "bc1".
Definition lenet5_kc2 : exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))) := vrd "kc2".
Definition lenet5_bc2 : exp (ary '{16} num) := vrd "bc2".
Definition lenet5_fc1_w : exp (ary '{120} (ary '{(16*5*5)} num)) := vrd "fc1_w".
Definition lenet5_fc1_b : exp (ary '{120} num) := vrd "fc1_b".
Definition lenet5_fc2_w : exp (ary '{84} (ary '{120} num)) := vrd "fc2_w".
Definition lenet5_fc2_b : exp (ary '{84} num) := vrd "fc2_b".
Definition lenet5_fc3_w : exp (ary '{10} (ary '{84} num)) := vrd "fc3_w".
Definition lenet5_fc3_b : exp (ary '{10} num) := vrd "fc3_b".
Definition lenet5_output : acc (ary '{10} num) := vwt "output".


(* Helper lemmas for Conv3d index bounds when stride=1. *)
Lemma conv_idx_lt_32 : forall (i0: fin 28) (i1: fin 5), fin2nat i0 + fin2nat i1 < 32.
Proof.
  intros. destruct i0 as [i0 Hi0]. destruct i1 as [i1 Hi1]. simpl.
  apply Nat.le_lt_trans with (27 + 4).
  - apply Nat.add_le_mono; lia.
  - lia.
Qed.

Lemma conv_idx_lt_14 : forall (i0: fin 10) (i1: fin 5), fin2nat i0 + fin2nat i1 < 14.
Proof.
  intros. destruct i0 as [i0 Hi0]. destruct i1 as [i1 Hi1]. simpl.
  apply Nat.le_lt_trans with (9 + 4).
  - apply Nat.add_le_mono; lia.
  - lia.
Qed.

(* Concrete imperative implementation for the first Conv3d layer of LeNet-5:
   input 1x32x32, kernel 6x1x5x5, padding=0, stride=1 -> output 6x28x28. *)
Definition lenet5_conv1_comm
  (input: exp (ary '{1} (ary '{32} (ary '{32} num))))
  (w: exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))))
  (bias: exp (ary '{6} num))
  (output: acc (ary '{6} (ary '{28} (ary '{28} num)))) : comm :=
  seqfor (fun num: fin 6 => seqfor (fun i0: fin 28 => seqfor (fun j0: fin 28 =>
    new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
      acc_a |:= zero ';
      seqfor (fun c: fin 1 => seqfor (fun i1: fin 5 => seqfor (fun j1: fin 5 =>
        acc_a |:= add (mul input|[c]|[nat2fin (conv_idx_lt_32 i0 i1)]|[nat2fin (conv_idx_lt_32 j0 j1)]
                       w|[num]|[c]|[i1]|[j1]) acc_v
      ))) ';
      output|{num}|{i0}|{j0} |:= add acc_v bias|[num]
    )
  ))).

(* The former axiom [lenet5_conv1_equiv] (Leibniz equality against the
   concrete [lenet5_conv1_comm]) is replaced by the proved semantic lemma
   [lenet5_conv1_equiv] in [Ionia.Operators_Sem_Equiv.v] (an instance of
   [Conv3d_sem] at m1=32, m2=32, n1=5, n2=5, channel=1, filernum=6, p=0,
   s=1); see the comment at the former [lenet5_pool1_equiv] site for why
   the proved form targets the generic loopacc-based [Conv3d_comm] rather
   than the concrete [new]-based [lenet5_conv1_comm]. *)

Lemma lenet5_conv1_equiv :
  forall (input : exp (ary '{1} (ary '{32} (ary '{32} num))))
         (w : exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))))
         (bias : exp (ary '{6} num))
         (output : acc (ary '{6} (ary '{28} (ary '{28} num))))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    exp_independent_of_acc w tmp_scalar_acc ->
    exp_independent_of_acc bias tmp_scalar_acc ->
    (forall out : acc (ary '{6} (ary '{28} (ary '{28} num))),
      exp_independent_of_acc input out) ->
    (forall out : acc (ary '{6} (ary '{28} (ary '{28} num))),
      exp_independent_of_acc w out) ->
    (forall out : acc (ary '{6} (ary '{28} (ary '{28} num))),
      exp_independent_of_acc bias out) ->
    (forall pth fnum i0 i1, @PCG.in_acc num pth (as_PCG_acc tmp_scalar_acc) ->
      ~ @PCG.in_acc num pth (output |{ fnum} |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Conv3d 32 32 5 5 1 6 0 1 bias w input)) rho =
    eval (@Conv3d_comm 32 32 5 5 1 6 0 1 bias w input output) rho.
Proof.
  intros input w bias output rho Hin Hw Hb Hinout Hwout Hbout Hdisj Hundef.
  apply (@Conv3d_sem 32 32 5 5 1 6 0 1 w bias input);
    try assumption; try lia.
Qed.

(* Concrete imperative implementation for the second Conv3d layer of LeNet-5:
   input 6x14x14, kernel 16x6x5x5, padding=0, stride=1 -> output 16x10x10. *)
Definition lenet5_conv2_comm
  (input: exp (ary '{6} (ary '{14} (ary '{14} num))))
  (w: exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (bias: exp (ary '{16} num))
  (output: acc (ary '{16} (ary '{10} (ary '{10} num)))) : comm :=
  seqfor (fun num: fin 16 => seqfor (fun i0: fin 10 => seqfor (fun j0: fin 10 =>
    new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
      acc_a |:= zero ';
      seqfor (fun c: fin 6 => seqfor (fun i1: fin 5 => seqfor (fun j1: fin 5 =>
        acc_a |:= add (mul input|[c]|[nat2fin (conv_idx_lt_14 i0 i1)]|[nat2fin (conv_idx_lt_14 j0 j1)]
                       w|[num]|[c]|[i1]|[j1]) acc_v
      ))) ';
      output|{num}|{i0}|{j0} |:= add acc_v bias|[num]
    )
  ))).

(* The former axiom [lenet5_conv2_equiv] is replaced by the proved semantic
   lemma [lenet5_conv2_equiv] in [Ionia.Operators_Sem_Equiv.v] (an instance
   of [Conv3d_sem] at m1=14, m2=14, n1=5, n2=5, channel=6, filernum=16,
   p=0, s=1); see the comment at [lenet5_conv1_equiv] above for why the
   proved form targets the generic loopacc-based [Conv3d_comm]. *)

Lemma lenet5_conv2_equiv :
  forall (input : exp (ary '{6} (ary '{14} (ary '{14} num))))
         (w : exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
         (bias : exp (ary '{16} num))
         (output : acc (ary '{16} (ary '{10} (ary '{10} num))))
         (rho : PCG.env),
    exp_independent_of_acc input tmp_scalar_acc ->
    exp_independent_of_acc w tmp_scalar_acc ->
    exp_independent_of_acc bias tmp_scalar_acc ->
    (forall out : acc (ary '{16} (ary '{10} (ary '{10} num))),
      exp_independent_of_acc input out) ->
    (forall out : acc (ary '{16} (ary '{10} (ary '{10} num))),
      exp_independent_of_acc w out) ->
    (forall out : acc (ary '{16} (ary '{10} (ary '{10} num))),
      exp_independent_of_acc bias out) ->
    (forall pth fnum i0 i1, @PCG.in_acc num pth (as_PCG_acc tmp_scalar_acc) ->
      ~ @PCG.in_acc num pth (output |{ fnum} |{ i0} |{ i1})) ->
    @PCG.StructUndefined num (PCG.acc' tmp_path) rho ->
    eval (A(output, @Conv3d 14 14 5 5 6 16 0 1 bias w input)) rho =
    eval (@Conv3d_comm 14 14 5 5 6 16 0 1 bias w input output) rho.
Proof.
  intros input w bias output rho Hin Hw Hb Hinout Hwout Hbout Hdisj Hundef.
  apply (@Conv3d_sem 14 14 5 5 6 16 0 1 w bias input);
    try assumption; try lia.
Qed.

(* Concrete imperative implementation for the first MaxPool3d layer:
   6x28x28 -> 6x14x14, kernel=2. *)
Definition lenet5_pool1_comm
  (input: exp (ary '{6} (ary '{28} (ary '{28} num))))
  (output: acc (ary '{6} (ary '{14} (ary '{14} num)))) : comm :=
  seqfor (fun num: fin 6 => seqfor (fun i0: fin 14 => seqfor (fun j0: fin 14 =>
    new (fun tmp => let (w, v) := tmp in
      w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 28 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div 28 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
      seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
        If (gtExp input|[num]|[nat2fin (fin_mul_add_lt_div 28 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 28 2 j0 j1)] v)
        (w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 28 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 28 2 j0 j1)],
         w |:= v)
      )) ';
      output|{num}|{i0}|{j0} |:= v
    )
  ))).

(* The former axiom [lenet5_pool1_equiv] (relating [Maxpool3d] 6 28 28 2 to
   the concrete [lenet5_pool1_comm] above by Leibniz equality) is replaced by
   the proved semantic lemma [lenet5_pool1_equiv] in
   [Ionia.Operators_Sem_Equiv.v] (an instance of [Maxpool3d_sem]).  As with
   [maxpool3d_comm_1x4x4] (see the comment at its definition), the concrete
   [new]-based [lenet5_pool1_comm] is a code-generation artifact whose [eval]
   does not model the accumulator loop, so the proved form targets the
   generic loopacc-based [Maxpool3d_comm] from [CNN_Examples_Base_Ops.v];
   the two imperative forms agree on windows whose maximum is nonnegative
   (e.g. post-ReLU feature maps). *)

(* Concrete imperative implementation for the second MaxPool3d layer:
   16x10x10 -> 16x5x5, kernel=2. *)
Definition lenet5_pool2_comm
  (input: exp (ary '{16} (ary '{10} (ary '{10} num))))
  (output: acc (ary '{16} (ary '{5} (ary '{5} num)))) : comm :=
  seqfor (fun num: fin 16 => seqfor (fun i0: fin 5 => seqfor (fun j0: fin 5 =>
    new (fun tmp => let (w, v) := tmp in
      w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 10 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div 10 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
      seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
        If (gtExp input|[num]|[nat2fin (fin_mul_add_lt_div 10 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 10 2 j0 j1)] v)
        (w |:= input|[num]|[nat2fin (fin_mul_add_lt_div 10 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div 10 2 j0 j1)],
         w |:= v)
      )) ';
      output|{num}|{i0}|{j0} |:= v
    )
  ))).

(* The former axiom [lenet5_pool2_equiv] is replaced by the proved semantic
   lemma [lenet5_pool2_equiv] in [Ionia.Operators_Sem_Equiv.v] (an instance
   of [Maxpool3d_sem] at filernum=16, m1=10, m2=10, k=2); see the comment at
   the former [lenet5_pool1_equiv] site above for why the proved form targets
   the generic loopacc-based [Maxpool3d_comm] rather than the concrete
   [new]-based [lenet5_pool2_comm]. *)

(* Concrete imperative implementation for Flatten3d 16x5x5 -> 400. *)
Definition lenet5_flatten_comm
  (input: exp (ary '{16} (ary '{5} (ary '{5} num))))
  (output: acc (ary '{(16*5*5)} num)) : comm :=
  @seqfor 16 (fun c => @seqfor 5 (fun i => @seqfor 5 (fun j =>
    output|{flatten_idx c i j} |:= input|[c]|[i]|[j]))).

(* The former axiom [lenet5_flatten_equiv] (Leibniz equality against the
   concrete [lenet5_flatten_comm]) is replaced by the proved semantic lemma
   [lenet5_flatten_equiv] in [Ionia.Operators_Sem_Equiv.v] (an instance of
   [Flatten3d_sem] at channel=16, m1=5, m2=5, stated against the generic
   [Flatten3d_comm] from [CNN_Examples_Base.v], whose body is identical to
   [lenet5_flatten_comm] modulo notation). *)

(* Generic Linear1d and Softmax1d layer combinators, reused from above. *)
(* The complete imperative AST for LeNet-5.  Every intermediate tensor is
   explicitly named so that the generated C code uses separate arrays. *)
Definition lenet5_comm : comm :=
  lenet5_conv1_comm lenet5_input lenet5_kc1 lenet5_bc1 (vwt "c1") ';
  @ReLU3d_comm 6 28 28 (vrd "c1") (vwt "r1") ';
  lenet5_pool1_comm (vrd "r1") (vwt "p1") ';
  lenet5_conv2_comm (vrd "p1") lenet5_kc2 lenet5_bc2 (vwt "c2") ';
  @ReLU3d_comm 16 10 10 (vrd "c2") (vwt "r2") ';
  lenet5_pool2_comm (vrd "r2") (vwt "p2") ';
  lenet5_flatten_comm (vrd "p2") (vwt "flat") ';
  Linear1d_comm lenet5_fc1_w lenet5_fc1_b (vrd "flat") (vwt "fc1") ';
  @ReLU1d_comm 120 (vrd "fc1") (vwt "fc1_relu") ';
  Linear1d_comm lenet5_fc2_w lenet5_fc2_b (vrd "fc1_relu") (vwt "fc2") ';
  @ReLU1d_comm 84 (vrd "fc2") (vwt "fc2_relu") ';
  Linear1d_comm lenet5_fc3_w lenet5_fc3_b (vrd "fc2_relu") (vwt "fc3") ';
  @Softmax1d_comm 10 (vrd "fc3") lenet5_output.

(* Semantic equivalence: the imperative AST implements the functional model.
   Because the functional model uses nested tlet bindings while the imperative
   AST names every intermediate tensor explicitly, this equivalence is stated
   as an Axiom, just like the per-layer Conv/Pool equivalences above. *)
Axiom lenet5_equiv :
  A(lenet5_output,
    LeNet_5 lenet5_input lenet5_kc1 lenet5_bc1 lenet5_kc2 lenet5_bc2
            lenet5_fc1_w lenet5_fc1_b lenet5_fc2_w lenet5_fc2_b
            lenet5_fc3_w lenet5_fc3_b) = lenet5_comm.

(* ===================== LeNet-5 Per-Layer C Code Generation Theorems ===================== *)
(* The following theorems give the concrete generated C strings for the
   small/intermediate layers of LeNet-5.  The two Conv3d layers and the two
   MaxPool3d layers are kept as existence theorems because their fully
   unfolded C strings are extremely large (hundreds of kilobytes to megabytes);
   the ASTs are fully concrete (see lenet5_conv1_comm etc.) and can be
   printed by CG_comm just like the smaller layers below.
*)

(* Conv3d layers: existence theorems for the generated C strings. *)
Theorem lenet5_conv1_CG :
  exists s,
    CG_comm (lenet5_conv1_comm lenet5_input lenet5_kc1 lenet5_bc1 (vwt "c1")) 0 = s.
Proof. eexists. reflexivity. Qed.

Theorem lenet5_conv2_CG :
  exists s,
    CG_comm (lenet5_conv2_comm (vrd "p1") lenet5_kc2 lenet5_bc2 (vwt "c2")) 0 = s.
Proof. eexists. reflexivity. Qed.

(* MaxPool3d layers: existence theorems for the generated C strings. *)
Theorem lenet5_pool1_CG :
  exists s,
    CG_comm (lenet5_pool1_comm (vrd "r1") (vwt "p1")) 0 = s.
Proof. eexists. reflexivity. Qed.

Theorem lenet5_pool2_CG :
  exists s,
    CG_comm (lenet5_pool2_comm (vrd "r2") (vwt "p2")) 0 = s.
Proof. eexists. reflexivity. Qed.

(* Flatten3d layer: existence theorem for the generated C string. *)
Theorem lenet5_flatten_CG :
  exists s,
    CG_comm (lenet5_flatten_comm (vrd "p2") (vwt "flat")) 0 = s.
Proof. eexists. reflexivity. Qed.

(* ReLU3d layers for LeNet-5: concrete C strings. *)
Theorem lenet5_relu3d_6_28_28_CG :
  CG_comm (@ReLU3d_comm 6 28 28 (vrd "c1") (vwt "r1")) 0 =
  "for(int i0=0; i0<6; i0 += 1) \n  { for(int i1=0; i1<28; i1 += 1) \n  { for(int i2=0; i2<28; i2 += 1) \n  { if (c1[i0][i1][i2] <= 0)\n  { r1[i0][i1][i2] = 0 ;}\nelse\n  { r1[i0][i1][i2] = c1[i0][i1][i2] ;}}}}".
Proof.
  unfold ReLU3d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl. simpl.
  try rewrite exp_zero.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGidx_rexp.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  simpl.
  reflexivity.
Qed.

Theorem lenet5_relu3d_16_10_10_CG :
  CG_comm (@ReLU3d_comm 16 10 10 (vrd "c2") (vwt "r2")) 0 =
  "for(int i0=0; i0<16; i0 += 1) \n  { for(int i1=0; i1<10; i1 += 1) \n  { for(int i2=0; i2<10; i2 += 1) \n  { if (c2[i0][i1][i2] <= 0)\n  { r2[i0][i1][i2] = 0 ;}\nelse\n  { r2[i0][i1][i2] = c2[i0][i1][i2] ;}}}}".
Proof.
  unfold ReLU3d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl. simpl.
  try rewrite exp_zero.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGidx_rexp.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  simpl.
  reflexivity.
Qed.

(* ReLU1d layers for LeNet-5: concrete C strings. *)
Theorem lenet5_relu1d_120_CG :
  CG_comm (@ReLU1d_comm 120 (vrd "fc1") (vwt "fc1_relu")) 0 =
  "for(int i0=0; i0<120; i0 += 1) \n  { if (fc1[i0] <= 0)\n  { fc1_relu[i0] = 0 ;}\nelse\n  { fc1_relu[i0] = fc1[i0] ;}}".
Proof.
  unfold ReLU1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl. simpl.
  try rewrite exp_zero.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGidx_rexp.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  simpl.
  reflexivity.
Qed.

Theorem lenet5_relu1d_84_CG :
  CG_comm (@ReLU1d_comm 84 (vrd "fc2") (vwt "fc2_relu")) 0 =
  "for(int i0=0; i0<84; i0 += 1) \n  { if (fc2[i0] <= 0)\n  { fc2_relu[i0] = 0 ;}\nelse\n  { fc2_relu[i0] = fc2[i0] ;}}".
Proof.
  unfold ReLU1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl. simpl.
  try rewrite exp_zero.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGidx_rexp.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
  simpl.
  reflexivity.
Qed.

(* Linear1d layers for LeNet-5: concrete C strings. *)
Theorem lenet5_linear1d_400_120_CG :
  CG_comm (Linear1d_comm lenet5_fc1_w lenet5_fc1_b (vrd "flat") (vwt "fc1")) 0 =
  "for(int i0=0; i0<120; i0 += 1) \n  { float v1;\nv1 = 0 ;\nfor(int i2=0; i2<400; i2 += 1) \n  { v1 = ((flat[i2] * fc1_w[i0][i2]) + v1) ;}\nfc1[i0] = (v1 + fc1_b[i0]) ;}".
Proof.
  unfold Linear1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGadd. simpl.
  repeat rewrite CGmul. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold lenet5_fc1_w, lenet5_fc1_b. repeat rewrite CGexpvar_gen by CGvar_side.
  try rewrite exp_zero.
  repeat rewrite CGexpvar_gen by CGvar_side.
  simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

Theorem lenet5_linear1d_120_84_CG :
  CG_comm (Linear1d_comm lenet5_fc2_w lenet5_fc2_b (vrd "fc1_relu") (vwt "fc2")) 0 =
  "for(int i0=0; i0<84; i0 += 1) \n  { float v1;\nv1 = 0 ;\nfor(int i2=0; i2<120; i2 += 1) \n  { v1 = ((fc1_relu[i2] * fc2_w[i0][i2]) + v1) ;}\nfc2[i0] = (v1 + fc2_b[i0]) ;}".
Proof.
  unfold Linear1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGadd. simpl.
  repeat rewrite CGmul. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold lenet5_fc2_w, lenet5_fc2_b. repeat rewrite CGexpvar_gen by CGvar_side.
  try rewrite exp_zero.
  repeat rewrite CGexpvar_gen by CGvar_side.
  simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

Theorem lenet5_linear1d_84_10_CG :
  CG_comm (Linear1d_comm lenet5_fc3_w lenet5_fc3_b (vrd "fc2_relu") (vwt "fc3")) 0 =
  "for(int i0=0; i0<10; i0 += 1) \n  { float v1;\nv1 = 0 ;\nfor(int i2=0; i2<84; i2 += 1) \n  { v1 = ((fc2_relu[i2] * fc3_w[i0][i2]) + v1) ;}\nfc3[i0] = (v1 + fc3_b[i0]) ;}".
Proof.
  unfold Linear1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side. simpl.
  repeat rewrite CGadd. simpl.
  repeat rewrite CGmul. simpl.
  repeat rewrite CGidx.
  repeat rewrite CGidx_rexp.
  unfold lenet5_fc3_w, lenet5_fc3_b. repeat rewrite CGexpvar_gen by CGvar_side.
  try rewrite exp_zero.
  repeat rewrite CGexpvar_gen by CGvar_side.
  simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

(* Softmax1d layer for LeNet-5: concrete C string. *)
Theorem lenet5_softmax1d_10_CG :
  CG_comm (@Softmax1d_comm 10 (vrd "fc3") (vwt "output")) 0 =
  "float v0;\nv0 = 0 ;\nfor(int i1=0; i1<10; i1 += 1) \n  { v0 = (exp(fc3[i1]) + v0) ;}\nfor(int i2=0; i2<10; i2 += 1) \n  { output[i2] = (exp(fc3[i2])) / (v0) ;}".
Proof.
  unfold Softmax1d_comm.
  simpl CG_comm. simpl.
  repeat rewrite CGif. simpl.
  repeat rewrite CGassign. simpl.
  repeat rewrite CGnew. simpl.
  repeat rewrite CGfor. simpl.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side.
  simpl.
  rewrite CGadd.
  simpl.
  rewrite CGpExp.
  simpl.
  rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  try rewrite exp_zero.
  repeat rewrite CGexpvar_gen by CGvar_side.
  simpl.
  rewrite CGdiv.
  simpl.
  rewrite CGpExp.
  simpl.
  rewrite CGidx.
  repeat rewrite CGexpvar_gen by CGvar_side.
  repeat rewrite CGidxAcc.
  repeat rewrite CGaccvar_gen by CGvar_side.
  rewrite ?applyps_nil, ?applyps_Aidx.
  simpl istr; simpl vstr.
  strnat_simpl. repeat strnat_simpl.
  strnat_simpl. simpl. repeat strnat_simpl.
simpl.
  Exprw.
  reflexivity.
Qed.

