(* ========================================================================= *)
(* AlexNet_Par.v                                                             *)
(*                                                                           *)
(* OpenMP (M7): a parallel variant of the classic AlexNet imperative AST     *)
(* [Bridge_AlexNet.alexnet_gen_comm] (224x224 input, 5 conv + 3 fc, the net  *)
(* whose whole-network bridge to route A [AlexNet_DPIA.alexnet_comm] is      *)
(* proved in [Bridge_AlexNet]).                                              *)
(*                                                                           *)
(* Parallelization (same recipe as [LeNet5_Par] / ResNet18_OMP): the batch   *)
(* loop (batch = 1) stays sequential; the loop one level deeper is turned    *)
(* from [seqfor] into [parfor]:                                              *)
(*   - Conv4d_ast_comm    : output channel  nu : fin filernum                *)
(*   - ReLU4d_comm        : channel         num : fin filernum               *)
(*   - Maxpool4d_pad_ast  : channel         nu : fin filernum                *)
(*   - Linear2d_comm      : output unit     out : fin outnum                 *)
(*   - ReLU2d_comm        : second dim      i1 : fin m2                      *)
(*   - Softmax2d_comm     : division loop   j : fin m (sum stays sequential) *)
(* Every reduction inner loop (flattened conv window over channel*n1*n2,     *)
(* maxpool window scan, Linear dot product, softmax sum) stays sequential    *)
(* because the loopacc accumulator dependency forbids parallelization.       *)
(* Flatten4d stays sequential: its outer channel index (fin 256) does not    *)
(* match the 1-D output acceptor shape required by [parfor].                 *)
(*                                                                           *)
(* Correctness: [CNN_CodeGen_Semantics.eval_aux] maps both [parfor] and   *)
(* [seqfor] to the same [Pseqfor], so each parallel layer has the same *)
(* denotation as its sequential counterpart, proved PER LAYER by             *)
(* [reflexivity] at the EVAL level (a single whole-net reflexivity iota-     *)
(* expands every concrete [Pseqfor] and does not terminate — see          *)
(* [LeNet5_Par]; likewise a TERM-level Leibniz equality of the whole         *)
(* 20-layer tower against [Ionia.Bridge_AlexNet.alexnet_gen_comm] does not terminate in        *)
(* practice, so all equalities here are eval-level, chained pointwise by     *)
(* [eval_seq_congr]).                                                        *)
(*                                                                           *)
(*   [alexnet_par_eval_eq] : eval alexnet_par_gen_comm rho                   *)
(*                         = eval Bridge_AlexNet.alexnet_gen_comm rho        *)
(*   [alexnet_seq_eval_eq] : eval alexnet_seq_gen_comm rho                   *)
(*                         = eval Bridge_AlexNet.alexnet_gen_comm rho        *)
(* so the [Bridge_AlexNet] chain to route A ([AlexNet_DPIA.A_AlexNet])       *)
(* transfers literally to both nets.                                         *)
(*                                                                           *)
(* Extraction note: monolithic [Extraction] cannot reference constants of    *)
(* [Bridge_AlexNet] / [Bridge_ReduceConv2] (both files define inner module   *)
(* aliases, which forces module extraction).  This file therefore carries    *)
(* LOCAL verbatim copies [Conv4d_ast_seq_comm] /                             *)
(* [Maxpool4d_pad_ast_seq_comm] of the two sequential operators and local    *)
(* copies of the buffer-shape aliases [Tin..Tout]; the sequential reference  *)
(* net [alexnet_seq_gen_comm] is assembled from them and related to          *)
(* [Ionia.Bridge_AlexNet.alexnet_gen_comm] by the eval-level chain [alexnet_seq_eval_eq]       *)
(* (per-layer reflexivity lemmas [seq_conv_eval_eq] / [seq_pool_eval_eq]     *)
(* witness that the local copies are the same operators).                    *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

Require Import Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_Examples_Base_Ops.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.CNN_OP.
Require Ionia.Bridge_ReduceConv2.
Require Ionia.Bridge_AlexNet.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

(* See [Bridge_AlexNet]: the buffer name types are local [Definition]s, so
   the matching below relies on keyed unification. *)
Set Keyed Unification.

(* -------------------- Local copies of the two sequential ops -------------- *)
(* Verbatim copies of [Bridge_ReduceConv2.Conv4d_ast_comm] and               *)
(* [Bridge_ReduceConv2.Maxpool4d_pad_ast_comm] (see the extraction note      *)
(* above); [seq_conv_eval_eq] / [seq_pool_eval_eq] below witness that they   *)
(* have the same denotations.                                                *)

Definition Conv4d_ast_seq_comm {batch m1 m2 n1 n2 channel filernum : nat}
  (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun nu : fin filernum =>
    seqfor (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
      seqfor (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
        @loopacc num (fun tmp =>
          (vwt tmp |:= zero) ';
          seqfor (fun kk : fin (channel * n1 * n2) =>
            vwt tmp |:= add (mul (safe_idx_nat (safe_idx_nat (Padding4d p input)|[b]|[nat2fin (conv3d_flat_c_bound kk)] (fin2nat i0 * s + Nat.div (Nat.modulo (fin2nat kk) (n1 * n2)) n2)) (fin2nat j0 * s + Nat.modulo (fin2nat kk) n2)) w|[nu]|[nat2fin (conv3d_flat_c_bound kk)]|[nat2fin (conv3d_flat_i1_bound kk)]|[nat2fin (conv3d_flat_j1_bound kk)]) (vrd tmp)) ';
          output|{b}|{nu}|{i0}|{j0} |:= add (vrd tmp) (bias|[nu])))))).

Definition Maxpool4d_pad_ast_seq_comm {batch filernum m1 m2 : nat}
  (kersize stride padding : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun nu : fin filernum =>
    seqfor (fun i0 : fin ((m1 - kersize + 2 * padding) / stride + 1) =>
      seqfor (fun j0 : fin ((m2 - kersize + 2 * padding) / stride + 1) =>
        @loopacc num (fun tmp =>
          (vwt tmp |:= zero) ';
          seqfor (fun kk : fin (kersize * kersize) =>
            If (gtExp (safe_idx_nat (safe_idx_nat ((Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (vrd tmp))
              (vwt tmp |:= safe_idx_nat (safe_idx_nat ((Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), vwt tmp |:= (vrd tmp : exp num))) ';
          output|{b}|{nu}|{i0}|{j0} |:= (vrd tmp : exp num)))))).

(* -------------------- Parallel layer variants -------------------- *)

(* Conv4d: batch loop sequential, output channels parallel; the flattened
   window reduction (kk : fin (channel*n1*n2)) stays sequential. *)
Definition Conv4d_ast_par_comm {batch m1 m2 n1 n2 channel filernum : nat}
  (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2 * p) / s + 1)} (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))) : comm :=
  seqfor (fun b : fin batch =>
    parfor (output|{b}) (fun nu o =>
      seqfor (fun i0 : fin ((m1 - n1 + 2 * p) / s + 1) =>
        seqfor (fun j0 : fin ((m2 - n2 + 2 * p) / s + 1) =>
          @loopacc num (fun tmp =>
            (vwt tmp |:= zero) ';
            seqfor (fun kk : fin (channel * n1 * n2) =>
              vwt tmp |:= add (mul (safe_idx_nat (safe_idx_nat (Padding4d p input)|[b]|[nat2fin (conv3d_flat_c_bound kk)] (fin2nat i0 * s + Nat.div (Nat.modulo (fin2nat kk) (n1 * n2)) n2)) (fin2nat j0 * s + Nat.modulo (fin2nat kk) n2)) w|[nu]|[nat2fin (conv3d_flat_c_bound kk)]|[nat2fin (conv3d_flat_i1_bound kk)]|[nat2fin (conv3d_flat_j1_bound kk)]) (vrd tmp)) ';
            o|{i0}|{j0} |:= add (vrd tmp) (bias|[nu])))))).

(* ReLU4d: batch loop sequential, channels parallel. *)
Definition ReLU4d_par_comm {batch filernum m1 m2}
  (input: exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b => parfor (output|{b}) (fun num o => seqfor (fun i0 => seqfor (fun i1 =>
    If (leExp input|[b]|[num]|[i0]|[i1] zero)
      (o|{i0}|{i1} |:= zero, o|{i0}|{i1} |:= input|[b]|[num]|[i0]|[i1]))))).

(* Maxpool4d with padding: batch loop sequential, channels parallel; the
   flattened window max scan (kk : fin (kersize*kersize)) stays sequential. *)
Definition Maxpool4d_pad_ast_par_comm {batch filernum m1 m2 : nat}
  (kersize stride padding : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{((m1 - kersize + 2 * padding) / stride + 1)} (ary '{((m2 - kersize + 2 * padding) / stride + 1)} num))))) : comm :=
  seqfor (fun b : fin batch =>
    parfor (output|{b}) (fun nu o =>
      seqfor (fun i0 : fin ((m1 - kersize + 2 * padding) / stride + 1) =>
        seqfor (fun j0 : fin ((m2 - kersize + 2 * padding) / stride + 1) =>
          @loopacc num (fun tmp =>
            (vwt tmp |:= zero) ';
            seqfor (fun kk : fin (kersize * kersize) =>
              If (gtExp (safe_idx_nat (safe_idx_nat ((Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize)) (vrd tmp))
                (vwt tmp |:= safe_idx_nat (safe_idx_nat ((Padding4d padding input)|[b]|[nu]) (fin2nat i0 * stride + Nat.div (fin2nat kk) kersize)) (fin2nat j0 * stride + Nat.modulo (fin2nat kk) kersize), vwt tmp |:= (vrd tmp : exp num))) ';
            o|{i0}|{j0} |:= (vrd tmp : exp num)))))).

(* Linear2d: batch loop sequential, output units parallel; the dot-product
   loopacc reduction stays sequential. *)
Definition Linear2d_par_comm {batch m outnum}
  (w: exp (ary '{outnum} (ary '{m} num)))
  (b: exp (ary '{outnum} num))
  (input: exp (ary '{batch} (ary '{m} num)))
  (output: acc (ary '{batch} (ary '{outnum} num))) : comm :=
  seqfor (fun bi: fin batch => parfor (output|{bi}) (fun out o =>
    @loopacc num (fun tmp =>
      let w_acc := vwt tmp in
      let v := vrd tmp in
      (w_acc |:= zero) ';
      seqfor (fun i => w_acc |:= add (mul input|[bi]|[i] w|[out]|[i]) v) ';
      o |:= add v b|[out]))).

(* ReLU2d: first dim (batch = 1) sequential, second dim parallel. *)
Definition ReLU2d_par_comm {m1 m2:nat}
  (input: exp (ary '{m1} (ary '{m2} num)))
  (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 => parfor (output|{i0}) (fun i1 o =>
    If (leExp input|[i0]|[i1] zero) (o |:= zero, o |:= input|[i0]|[i1]))).

(* Softmax2d: the sum loopacc reduction stays sequential; the division loop
   is parallel over elements. *)
Definition Softmax2d_par_comm {batch m}
  (input: exp (ary '{batch} (ary '{m} num)))
  (output: acc (ary '{batch} (ary '{m} num))) : comm :=
  seqfor (fun bi: fin batch =>
    @loopacc num (fun tmp =>
      let w := vwt tmp in
      let v := vrd tmp in
      (w |:= zero) ';
      seqfor (fun i => w |:= add (pExp (input|[bi]|[i])) v) ';
      parfor (output|{bi}) (fun j o => o |:= div (pExp (input|[bi]|[j])) v))).

(* -------------------- Buffer-shape aliases (local copies) ------------------ *)
(* Verbatim copies of the [Bridge_AlexNet] aliases (see the extraction note  *)
(* above).                                                                   *)

Definition Tin  : data := ary '{1} (ary '{3} (ary '{224} (ary '{224} num))).
Definition Tw1  : data := ary '{64} (ary '{3} (ary '{11} (ary '{11} num))).
Definition Tb1  : data := ary '{64} num.
Definition Tc1  : data := ary '{1} (ary '{64} (ary '{55} (ary '{55} num))).
Definition Tp1  : data := ary '{1} (ary '{64} (ary '{27} (ary '{27} num))).
Definition Tw2  : data := ary '{192} (ary '{64} (ary '{5} (ary '{5} num))).
Definition Tb2  : data := ary '{192} num.
Definition Tc2  : data := ary '{1} (ary '{192} (ary '{27} (ary '{27} num))).
Definition Tp2  : data := ary '{1} (ary '{192} (ary '{13} (ary '{13} num))).
Definition Tw3  : data := ary '{384} (ary '{192} (ary '{3} (ary '{3} num))).
Definition Tb3  : data := ary '{384} num.
Definition Tc3  : data := ary '{1} (ary '{384} (ary '{13} (ary '{13} num))).
Definition Tw4  : data := ary '{256} (ary '{384} (ary '{3} (ary '{3} num))).
Definition Tb4  : data := ary '{256} num.
Definition Tc4  : data := ary '{1} (ary '{256} (ary '{13} (ary '{13} num))).
Definition Tw5  : data := ary '{256} (ary '{256} (ary '{3} (ary '{3} num))).
Definition Tb5  : data := ary '{256} num.
Definition Tc5  : data := ary '{1} (ary '{256} (ary '{13} (ary '{13} num))).
Definition Tp5  : data := ary '{1} (ary '{256} (ary '{6} (ary '{6} num))).
Definition Tflat: data := ary '{1} (ary '{(256*6*6)} num).
Definition Tf1w : data := ary '{4096} (ary '{(256*6*6)} num).
Definition Tf1b : data := ary '{4096} num.
Definition Tfc  : data := ary '{1} (ary '{4096} num).
Definition Tf2w : data := ary '{4096} (ary '{4096} num).
Definition Tf2b : data := ary '{4096} num.
Definition Tf3w : data := ary '{1000} (ary '{4096} num).
Definition Tf3b : data := ary '{1000} num.
Definition Tout : data := ary '{1} (ary '{1000} num).

(* -------------------- The parallel whole-net AST -------------------- *)
(* Layer-for-layer mirror of [Bridge_AlexNet.alexnet_gen_comm] with the      *)
(* parallel layer variants; Flatten4d is identical (sequential).             *)

Definition alexnet_par_gen_comm : comm :=
  @Conv4d_ast_par_comm 1 224 224 11 11 3 64 2 4
             (@vrd Tb1 "c1_b") (@vrd Tw1 "c1_w")
             (@vrd Tin "input") (@vwt Tc1 "c1") ';
  @ReLU4d_par_comm 1 64 55 55
             (@vrd Tc1 "c1") (@vwt Tc1 "r1") ';
  @Maxpool4d_pad_ast_par_comm 1 64 55 55 3 2 0
             (@vrd Tc1 "r1") (@vwt Tp1 "p1") ';
  @Conv4d_ast_par_comm 1 27 27 5 5 64 192 2 1
             (@vrd Tb2 "c2_b") (@vrd Tw2 "c2_w")
             (@vrd Tp1 "p1") (@vwt Tc2 "c2") ';
  @ReLU4d_par_comm 1 192 27 27
             (@vrd Tc2 "c2") (@vwt Tc2 "r2") ';
  @Maxpool4d_pad_ast_par_comm 1 192 27 27 3 2 0
             (@vrd Tc2 "r2") (@vwt Tp2 "p2") ';
  @Conv4d_ast_par_comm 1 13 13 3 3 192 384 1 1
             (@vrd Tb3 "c3_b") (@vrd Tw3 "c3_w")
             (@vrd Tp2 "p2") (@vwt Tc3 "c3") ';
  @ReLU4d_par_comm 1 384 13 13
             (@vrd Tc3 "c3") (@vwt Tc3 "r3") ';
  @Conv4d_ast_par_comm 1 13 13 3 3 384 256 1 1
             (@vrd Tb4 "c4_b") (@vrd Tw4 "c4_w")
             (@vrd Tc3 "r3") (@vwt Tc4 "c4") ';
  @ReLU4d_par_comm 1 256 13 13
             (@vrd Tc4 "c4") (@vwt Tc4 "r4") ';
  @Conv4d_ast_par_comm 1 13 13 3 3 256 256 1 1
             (@vrd Tb5 "c5_b") (@vrd Tw5 "c5_w")
             (@vrd Tc4 "r4") (@vwt Tc5 "c5") ';
  @ReLU4d_par_comm 1 256 13 13
             (@vrd Tc5 "c5") (@vwt Tc5 "r5") ';
  @Maxpool4d_pad_ast_par_comm 1 256 13 13 3 2 0
             (@vrd Tc5 "r5") (@vwt Tp5 "p5") ';
  @Flatten4d_comm 1 256 6 6
             (@vrd Tp5 "p5") (@vwt Tflat "flat") ';
  @Linear2d_par_comm 1 (256*6*6) 4096
             (@vrd Tf1w "f1_w") (@vrd Tf1b "f1_b")
             (@vrd Tflat "flat") (@vwt Tfc "fc1") ';
  @ReLU2d_par_comm 1 4096
             (@vrd Tfc "fc1") (@vwt Tfc "fc1r") ';
  @Linear2d_par_comm 1 4096 4096
             (@vrd Tf2w "f2_w") (@vrd Tf2b "f2_b")
             (@vrd Tfc "fc1r") (@vwt Tfc "fc2") ';
  @ReLU2d_par_comm 1 4096
             (@vrd Tfc "fc2") (@vwt Tfc "fc2r") ';
  @Linear2d_par_comm 1 4096 1000
             (@vrd Tf3w "f3_w") (@vrd Tf3b "f3_b")
             (@vrd Tfc "fc2r") (@vwt Tout "fc3") ';
             @Softmax2d_par_comm 1 1000
             (@vrd Tout "fc3") (@vwt Tout "output").

(* -------------------- The sequential reference net ------------------------- *)
(* Textual mirror of [Bridge_AlexNet.alexnet_gen_comm] built from the local  *)
(* operator copies; related to it by [alexnet_seq_eval_eq] below.            *)

Definition alexnet_seq_gen_comm : comm :=
  @Conv4d_ast_seq_comm 1 224 224 11 11 3 64 2 4
             (@vrd Tb1 "c1_b") (@vrd Tw1 "c1_w")
             (@vrd Tin "input") (@vwt Tc1 "c1") ';
  @ReLU4d_comm 1 64 55 55
             (@vrd Tc1 "c1") (@vwt Tc1 "r1") ';
  @Maxpool4d_pad_ast_seq_comm 1 64 55 55 3 2 0
             (@vrd Tc1 "r1") (@vwt Tp1 "p1") ';
  @Conv4d_ast_seq_comm 1 27 27 5 5 64 192 2 1
             (@vrd Tb2 "c2_b") (@vrd Tw2 "c2_w")
             (@vrd Tp1 "p1") (@vwt Tc2 "c2") ';
  @ReLU4d_comm 1 192 27 27
             (@vrd Tc2 "c2") (@vwt Tc2 "r2") ';
  @Maxpool4d_pad_ast_seq_comm 1 192 27 27 3 2 0
             (@vrd Tc2 "r2") (@vwt Tp2 "p2") ';
  @Conv4d_ast_seq_comm 1 13 13 3 3 192 384 1 1
             (@vrd Tb3 "c3_b") (@vrd Tw3 "c3_w")
             (@vrd Tp2 "p2") (@vwt Tc3 "c3") ';
  @ReLU4d_comm 1 384 13 13
             (@vrd Tc3 "c3") (@vwt Tc3 "r3") ';
  @Conv4d_ast_seq_comm 1 13 13 3 3 384 256 1 1
             (@vrd Tb4 "c4_b") (@vrd Tw4 "c4_w")
             (@vrd Tc3 "r3") (@vwt Tc4 "c4") ';
  @ReLU4d_comm 1 256 13 13
             (@vrd Tc4 "c4") (@vwt Tc4 "r4") ';
  @Conv4d_ast_seq_comm 1 13 13 3 3 256 256 1 1
             (@vrd Tb5 "c5_b") (@vrd Tw5 "c5_w")
             (@vrd Tc4 "r4") (@vwt Tc5 "c5") ';
  @ReLU4d_comm 1 256 13 13
             (@vrd Tc5 "c5") (@vwt Tc5 "r5") ';
  @Maxpool4d_pad_ast_seq_comm 1 256 13 13 3 2 0
             (@vrd Tc5 "r5") (@vwt Tp5 "p5") ';
  @Flatten4d_comm 1 256 6 6
             (@vrd Tp5 "p5") (@vwt Tflat "flat") ';
  @Linear2d_comm 1 (256*6*6) 4096
             (@vrd Tf1w "f1_w") (@vrd Tf1b "f1_b")
             (@vrd Tflat "flat") (@vwt Tfc "fc1") ';
  @ReLU2d_comm 1 4096
             (@vrd Tfc "fc1") (@vwt Tfc "fc1r") ';
  @Linear2d_comm 1 4096 4096
             (@vrd Tf2w "f2_w") (@vrd Tf2b "f2_b")
             (@vrd Tfc "fc1r") (@vwt Tfc "fc2") ';
  @ReLU2d_comm 1 4096
             (@vrd Tfc "fc2") (@vwt Tfc "fc2r") ';
  @Linear2d_comm 1 4096 1000
             (@vrd Tf3w "f3_w") (@vrd Tf3b "f3_b")
             (@vrd Tfc "fc2r") (@vwt Tout "fc3") ';
             @Softmax2d_comm 1 1000
             (@vrd Tout "fc3") (@vwt Tout "output").

(* -------------------- Correctness: per-layer eval equalities --------------- *)

(* Parallel layer vs its sequential counterpart (the [Bridge_ReduceConv2] /
   [CNN_Examples_Base_Ops] / [CNN_Examples_Base] operators used by
   [Ionia.Bridge_AlexNet.alexnet_gen_comm]).  Each holds by conversion at one constructor of
   depth: [eval_aux] maps [parfor] and [seqfor] to the same
   [Pseqfor]. *)

Lemma conv4d_ast_par_eval : forall batch m1 m2 n1 n2 channel filernum p s bias w input output rho,
  eval (@Conv4d_ast_par_comm batch m1 m2 n1 n2 channel filernum p s bias w input output) rho =
  eval (@Ionia.Bridge_ReduceConv2.Conv4d_ast_comm batch m1 m2 n1 n2 channel filernum p s bias w input output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu4d_par_eval : forall batch filernum m1 m2 input output rho,
  eval (@ReLU4d_par_comm batch filernum m1 m2 input output) rho =
  eval (@ReLU4d_comm batch filernum m1 m2 input output) rho.
Proof. intros. reflexivity. Qed.

Lemma maxpool4d_pad_ast_par_eval : forall batch filernum m1 m2 kersize stride padding input output rho,
  eval (@Maxpool4d_pad_ast_par_comm batch filernum m1 m2 kersize stride padding input output) rho =
  eval (@Ionia.Bridge_ReduceConv2.Maxpool4d_pad_ast_comm batch filernum m1 m2 kersize stride padding input output) rho.
Proof. intros. reflexivity. Qed.

Lemma linear2d_par_eval : forall batch m outnum w b input output rho,
  eval (@Linear2d_par_comm batch m outnum w b input output) rho =
  eval (@Linear2d_comm batch m outnum w b input output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu2d_par_eval : forall m1 m2 input output rho,
  eval (@ReLU2d_par_comm m1 m2 input output) rho =
  eval (@ReLU2d_comm m1 m2 input output) rho.
Proof. intros. reflexivity. Qed.

Lemma softmax2d_par_eval : forall batch m input output rho,
  eval (@Softmax2d_par_comm batch m input output) rho =
  eval (@Softmax2d_comm batch m input output) rho.
Proof. intros. reflexivity. Qed.

(* The local sequential operator copies have the same denotations as the
   [Bridge_ReduceConv2] originals (verbatim bodies). *)

Lemma seq_conv_eval_eq : forall batch m1 m2 n1 n2 channel filernum p s bias w input output rho,
  eval (@Conv4d_ast_seq_comm batch m1 m2 n1 n2 channel filernum p s bias w input output) rho =
  eval (@Ionia.Bridge_ReduceConv2.Conv4d_ast_comm batch m1 m2 n1 n2 channel filernum p s bias w input output) rho.
Proof. intros. reflexivity. Qed.

Lemma seq_pool_eval_eq : forall batch filernum m1 m2 kersize stride padding input output rho,
  eval (@Maxpool4d_pad_ast_seq_comm batch filernum m1 m2 kersize stride padding input output) rho =
  eval (@Ionia.Bridge_ReduceConv2.Maxpool4d_pad_ast_comm batch filernum m1 m2 kersize stride padding input output) rho.
Proof. intros. reflexivity. Qed.

(* Congruence of [eval] under sequential composition (same lemma as in
   [LeNet5_Par], restated here to keep this file self-contained). *)
Lemma eval_seq_congr : forall c1 c1' c2 c2' rho,
  (forall r, eval c1 r = eval c1' r) ->
  (forall r, eval c2 r = eval c2' r) ->
  eval (c1 '; c2) rho = eval (c1' '; c2') rho.
Proof.
  intros c1 c1' c2 c2' rho H1 H2.
  unfold eval in *. rewrite !eval_seq_aux.
  unfold PCG.seq. rewrite H1, H2. reflexivity.
Qed.

(* The parallel net has the same denotation as the sequential net of
   [Bridge_AlexNet], hence the whole-network bridge to route A
   ([AlexNet_DPIA.A_AlexNet]) applies to it. *)
Theorem alexnet_par_eval_eq : forall rho,
  eval alexnet_par_gen_comm rho = eval Ionia.Bridge_AlexNet.alexnet_gen_comm rho.
Proof.
  intros rho. unfold alexnet_par_gen_comm, Ionia.Bridge_AlexNet.alexnet_gen_comm.
  apply eval_seq_congr; [ intros r; apply conv4d_ast_par_eval |].
  intros r. apply eval_seq_congr; [ intros r0; apply relu4d_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply maxpool4d_pad_ast_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply conv4d_ast_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply relu4d_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply maxpool4d_pad_ast_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; apply conv4d_ast_par_eval |].
  intros r5. apply eval_seq_congr; [ intros r6; apply relu4d_par_eval |].
  intros r6. apply eval_seq_congr; [ intros r7; apply conv4d_ast_par_eval |].
  intros r7. apply eval_seq_congr; [ intros r8; apply relu4d_par_eval |].
  intros r8. apply eval_seq_congr; [ intros r9; apply conv4d_ast_par_eval |].
  intros r9. apply eval_seq_congr; [ intros r10; apply relu4d_par_eval |].
  intros r10. apply eval_seq_congr; [ intros r11; apply maxpool4d_pad_ast_par_eval |].
  intros r11. apply eval_seq_congr; [ intros r12; reflexivity (* flatten: identical *) |].
  intros r12. apply eval_seq_congr; [ intros r13; apply linear2d_par_eval |].
  intros r13. apply eval_seq_congr; [ intros r14; apply relu2d_par_eval |].
  intros r14. apply eval_seq_congr; [ intros r15; apply linear2d_par_eval |].
  intros r15. apply eval_seq_congr; [ intros r16; apply relu2d_par_eval |].
  intros r16. apply eval_seq_congr; [ intros r17; apply linear2d_par_eval |].
  intros r17. apply softmax2d_par_eval.
Qed.

(* The local sequential net has the same denotation as
   [Bridge_AlexNet.alexnet_gen_comm]; layers that are the same operator
   constant on both sides close by [reflexivity], the two local operator
   copies by [seq_conv_eval_eq] / [seq_pool_eval_eq]. *)
Theorem alexnet_seq_eval_eq : forall rho,
  eval alexnet_seq_gen_comm rho = eval Ionia.Bridge_AlexNet.alexnet_gen_comm rho.
Proof.
  intros rho. unfold alexnet_seq_gen_comm, Ionia.Bridge_AlexNet.alexnet_gen_comm.
  apply eval_seq_congr; [ intros r; apply seq_conv_eval_eq |].
  intros r. apply eval_seq_congr; [ intros r0; reflexivity |].
  intros r0. apply eval_seq_congr; [ intros r1; apply seq_pool_eval_eq |].
  intros r1. apply eval_seq_congr; [ intros r2; apply seq_conv_eval_eq |].
  intros r2. apply eval_seq_congr; [ intros r3; reflexivity |].
  intros r3. apply eval_seq_congr; [ intros r4; apply seq_pool_eval_eq |].
  intros r4. apply eval_seq_congr; [ intros r5; apply seq_conv_eval_eq |].
  intros r5. apply eval_seq_congr; [ intros r6; reflexivity |].
  intros r6. apply eval_seq_congr; [ intros r7; apply seq_conv_eval_eq |].
  intros r7. apply eval_seq_congr; [ intros r8; reflexivity |].
  intros r8. apply eval_seq_congr; [ intros r9; apply seq_conv_eval_eq |].
  intros r9. apply eval_seq_congr; [ intros r10; reflexivity |].
  intros r10. apply eval_seq_congr; [ intros r11; apply seq_pool_eval_eq |].
  intros r11. apply eval_seq_congr; [ intros r12; reflexivity (* flatten *) |].
  intros r12. apply eval_seq_congr; [ intros r13; reflexivity (* fc1 *) |].
  intros r13. apply eval_seq_congr; [ intros r14; reflexivity |].
  intros r14. apply eval_seq_congr; [ intros r15; reflexivity (* fc2 *) |].
  intros r15. apply eval_seq_congr; [ intros r16; reflexivity |].
  intros r16. apply eval_seq_congr; [ intros r17; reflexivity (* fc3 *) |].
  intros r17. reflexivity (* softmax *).
Qed.

(* par = seq (local reference net), as a corollary. *)
Theorem alexnet_par_eval_seq : forall rho,
  eval alexnet_par_gen_comm rho = eval alexnet_seq_gen_comm rho.
Proof.
  intros rho.
  rewrite alexnet_par_eval_eq. symmetry. apply alexnet_seq_eval_eq.
Qed.

(* -------------------- Extraction for the streaming printer -------------------- *)

Extraction "alexnet_par_comm.ml" alexnet_par_gen_comm alexnet_seq_gen_comm.
