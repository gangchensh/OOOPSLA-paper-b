(* ========================================================================= *)
(* VGG16_Par.v                                                               *)
(*                                                                           *)
(* OpenMP (M7): a parallel variant of the concrete imperative VGG-16 AST     *)
(* [CNN_Examples_VGG16.vgg16_comm].  As in [LeNet5_Par], only the outer      *)
(* parallelizable loop of each layer is turned from [seqfor] into [parfor];  *)
(* every reduction inner loop (convolution window accumulation, maxpool      *)
(* window scan, Linear dot product) stays sequential.  Because batch = 1,    *)
(* parallelizing the batch loop would give parallelism 1; the parallel       *)
(* combinators therefore descend one level and parallelize over output       *)
(* channels (conv/pool/ReLU4d), output units (Linear2d) or the second        *)
(* dimension (ReLU2d).  Flatten4d is kept sequential: its per-channel index  *)
(* does not match the 1-D output acceptor shape required by [parfor]         *)
(* (same situation as Flatten3d in [LeNet5_Par]).  The zero-padding loop of  *)
(* Conv4d_p1_k3 is kept sequential: it costs ~(m+2)^2*inch writes against    *)
(* 9*outch*m^2*inch MACs of the main loop (< 1/(9*outch) of the work).       *)
(*                                                                           *)
(* Correctness: [CNN_CodeGen_Semantics.eval] maps [CG.parfor n d a p] to     *)
(* [PCG.seqfor (fun i => eval (p i (DE.idxAcc a i)))], i.e. the same         *)
(* denotation as [CG.seqfor]; per-layer Leibniz equalities under [eval]      *)
(* hold by conversion at one constructor depth and are chained with          *)
(* [eval_seq_congr], giving [vgg16_par_eval_eq].  Hence the whole-net        *)
(* route-A/route-B bridge of [Bridge_VGG16] transfers to the parallel net.   *)
(*                                                                           *)
(* Topology note: [vgg16_par_comm] mirrors [CNN_Examples_VGG16.vgg16_comm]   *)
(* EXACTLY, including its buffer topology: conv x_1 of blocks 2..5 reads the *)
(* previous block's last ReLU buffer (pool1..pool4 are computed but never    *)
(* read there; only pool5 feeds Flatten4d).  The inline route-B AST bridged  *)
(* in [Bridge_VGG16] instead reads the pool outputs (the architecturally     *)
(* standard VGG-16 data flow), so the two route-B ASTs differ; the equality  *)
(* proved here concerns the extraction AST (the one used for C codegen).     *)
(*                                                                           *)
(* Sizes: the theorem is proved for the full 224x224 network.  For C code    *)
(* generation / numerical + performance validation we additionally define    *)
(* a structurally identical 32x32 network [vgg16s_par_comm] (same channel    *)
(* widths; flatten = 512, fc1 = 512->4096) and prove                         *)
(* [vgg16s_par_eval_eq]; the 224x224 net is too slow (~15 GFLOPs/inference)  *)
(* for naive generated C.  The per-layer lemmas are size-generic, so both    *)
(* instances are covered by the same proofs.                                 *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

Require Import Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_Examples_Base_Ops.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.CNN_Examples_VGG16.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

(* -------------------- Parallel layer combinators -------------------- *)

(* Conv4d (padding=1, kernel=3, stride=1): the zero-padding loop stays
   sequential; the main loop is parallel over output channels [num]
   (batch = 1 in VGG-16, so the batch loop is not worth parallelizing).
   The window reduction (c,i1,j1) stays sequential. *)
Definition Conv4d_p1_k3_par_comm {batch inch outch m}
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
    seqfor (fun b: fin batch =>
      parfor (output|{b}) (fun num o =>
        seqfor (fun i0: fin m => seqfor (fun j0: fin m =>
          new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
            acc_a |:= zero ';
            seqfor (fun c: fin inch => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
              acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
            ))) ';
            o|{i0}|{j0} |:= add acc_v bias|[num]
          )
        ))))
  ).

(* ReLU4d: parallel over channels. *)
Definition ReLU4d_par_comm {batch filernum m1 m2}
  (input: exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b =>
    parfor (output|{b}) (fun num o => seqfor (fun i0 => seqfor (fun i1 =>
      If (leExp input|[b]|[num]|[i0]|[i1] zero)
        (o|{i0}|{i1} |:= zero,
         o|{i0}|{i1} |:= input|[b]|[num]|[i0]|[i1]))))).

(* MaxPool4d (kernel=2): parallel over channels; window max scan sequential. *)
Definition MaxPool4d_k2_par_comm {batch ch m}
  (input: exp (ary '{batch} (ary '{ch} (ary '{m} (ary '{m} num)))))
  (output: acc (ary '{batch} (ary '{ch} (ary '{(m/2)} (ary '{(m/2)} num))))) : comm :=
  seqfor (fun b: fin batch =>
    parfor (output|{b}) (fun num o =>
      seqfor (fun i0: fin (m / 2) => seqfor (fun j0: fin (m / 2) =>
        new (fun tmp => let (w, v) := tmp in
          w |:= input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m 2 i0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))]|[nat2fin (fin_mul_add_lt_div m 2 j0 (@nat2fin 2 0 (Nat.lt_0_succ 1)))] ';
          seqfor (fun i1: fin 2 => seqfor (fun j1: fin 2 =>
            If (gtExp input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div m 2 j0 j1)] v)
            (w |:= input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m 2 i0 i1)]|[nat2fin (fin_mul_add_lt_div m 2 j0 j1)],
             w |:= v)
          )) ';
          o|{i0}|{j0} |:= v
        )
      )))).

(* Linear2d: parallel over output units; dot-product reduction sequential. *)
Definition Linear2d_par_comm {batch m outnum}
  (w: exp (ary '{outnum} (ary '{m} num)))
  (b: exp (ary '{outnum} num))
  (input: exp (ary '{batch} (ary '{m} num)))
  (output: acc (ary '{batch} (ary '{outnum} num))) : comm :=
  seqfor (fun bi: fin batch =>
    parfor (output|{bi}) (fun out o =>
      @loopacc num (fun tmp =>
        let w_acc := vwt tmp in
        let v := vrd tmp in
        (w_acc |:= zero) ';
        seqfor (fun i => w_acc |:= add (mul input|[bi]|[i] w|[out]|[i]) v) ';
        o |:= add v b|[out]))).

(* ReLU2d: parallel over the second dimension (first dim is batch = 1). *)
Definition ReLU2d_par_comm {m1 m2:nat}
  (input: exp (ary '{m1} (ary '{m2} num)))
  (output: acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 =>
    parfor (output|{i0}) (fun i1 o =>
      If (leExp input|[i0]|[i1] zero) (o |:= zero, o |:= input|[i0]|[i1]))).

(* -------------------- The parallel whole-net AST (224x224) -------------------- *)

Definition vgg16_par_comm : comm :=
  @Conv4d_p1_k3_par_comm 1 3 64 224
    vgg16_input vgg16_conv1_1_w vgg16_conv1_1_b vgg16_conv1_1_out ';
  @ReLU4d_par_comm 1 64 224 224
    (vrd "conv1_1_out") vgg16_relu1_1_out ';
  @Conv4d_p1_k3_par_comm 1 64 64 224
    (vrd "relu1_1_out") vgg16_conv1_2_w vgg16_conv1_2_b vgg16_conv1_2_out ';
  @ReLU4d_par_comm 1 64 224 224
    (vrd "conv1_2_out") vgg16_relu1_2_out ';
  @MaxPool4d_k2_par_comm 1 64 224
    (vrd "relu1_2_out") vgg16_pool1_out ';
  @Conv4d_p1_k3_par_comm 1 64 128 112
    (vrd "relu1_2_out") vgg16_conv2_1_w vgg16_conv2_1_b vgg16_conv2_1_out ';
  @ReLU4d_par_comm 1 128 112 112
    (vrd "conv2_1_out") vgg16_relu2_1_out ';
  @Conv4d_p1_k3_par_comm 1 128 128 112
    (vrd "relu2_1_out") vgg16_conv2_2_w vgg16_conv2_2_b vgg16_conv2_2_out ';
  @ReLU4d_par_comm 1 128 112 112
    (vrd "conv2_2_out") vgg16_relu2_2_out ';
  @MaxPool4d_k2_par_comm 1 128 112
    (vrd "relu2_2_out") vgg16_pool2_out ';
  @Conv4d_p1_k3_par_comm 1 128 256 56
    (vrd "relu2_2_out") vgg16_conv3_1_w vgg16_conv3_1_b vgg16_conv3_1_out ';
  @ReLU4d_par_comm 1 256 56 56
    (vrd "conv3_1_out") vgg16_relu3_1_out ';
  @Conv4d_p1_k3_par_comm 1 256 256 56
    (vrd "relu3_1_out") vgg16_conv3_2_w vgg16_conv3_2_b vgg16_conv3_2_out ';
  @ReLU4d_par_comm 1 256 56 56
    (vrd "conv3_2_out") vgg16_relu3_2_out ';
  @Conv4d_p1_k3_par_comm 1 256 256 56
    (vrd "relu3_2_out") vgg16_conv3_3_w vgg16_conv3_3_b vgg16_conv3_3_out ';
  @ReLU4d_par_comm 1 256 56 56
    (vrd "conv3_3_out") vgg16_relu3_3_out ';
  @MaxPool4d_k2_par_comm 1 256 56
    (vrd "relu3_3_out") vgg16_pool3_out ';
  @Conv4d_p1_k3_par_comm 1 256 512 28
    (vrd "relu3_3_out") vgg16_conv4_1_w vgg16_conv4_1_b vgg16_conv4_1_out ';
  @ReLU4d_par_comm 1 512 28 28
    (vrd "conv4_1_out") vgg16_relu4_1_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 28
    (vrd "relu4_1_out") vgg16_conv4_2_w vgg16_conv4_2_b vgg16_conv4_2_out ';
  @ReLU4d_par_comm 1 512 28 28
    (vrd "conv4_2_out") vgg16_relu4_2_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 28
    (vrd "relu4_2_out") vgg16_conv4_3_w vgg16_conv4_3_b vgg16_conv4_3_out ';
  @ReLU4d_par_comm 1 512 28 28
    (vrd "conv4_3_out") vgg16_relu4_3_out ';
  @MaxPool4d_k2_par_comm 1 512 28
    (vrd "relu4_3_out") vgg16_pool4_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 14
    (vrd "relu4_3_out") vgg16_conv5_1_w vgg16_conv5_1_b vgg16_conv5_1_out ';
  @ReLU4d_par_comm 1 512 14 14
    (vrd "conv5_1_out") vgg16_relu5_1_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 14
    (vrd "relu5_1_out") vgg16_conv5_2_w vgg16_conv5_2_b vgg16_conv5_2_out ';
  @ReLU4d_par_comm 1 512 14 14
    (vrd "conv5_2_out") vgg16_relu5_2_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 14
    (vrd "relu5_2_out") vgg16_conv5_3_w vgg16_conv5_3_b vgg16_conv5_3_out ';
  @ReLU4d_par_comm 1 512 14 14
    (vrd "conv5_3_out") vgg16_relu5_3_out ';
  @MaxPool4d_k2_par_comm 1 512 14
    (vrd "relu5_3_out") vgg16_pool5_out ';
  @Flatten4d_comm 1 512 7 7
    (vrd "pool5_out") vgg16_flatten_out ';
  @Linear2d_par_comm 1 25088 4096
    vgg16_fc1_w vgg16_fc1_b (vrd "flatten_out") vgg16_fc1_out ';
  @ReLU2d_par_comm 1 4096
    (vrd "fc1_out") vgg16_fc1_relu_out ';
  @Linear2d_par_comm 1 4096 4096
    vgg16_fc2_w vgg16_fc2_b (vrd "fc1_relu_out") vgg16_fc2_out ';
  @ReLU2d_par_comm 1 4096
    (vrd "fc2_out") vgg16_fc2_relu_out ';
  @Linear2d_par_comm 1 4096 1000
    vgg16_fc3_w vgg16_fc3_b (vrd "fc2_relu_out") vgg16_output.


(* -------------------- Correctness: par = seq -------------------- *)

(* See [LeNet5_Par] for why these hold by conversion and why the proof must
   be decomposed per layer (a whole-net [reflexivity] iota-expands every
   concrete [PCG.seqfor] and does not terminate). *)

Lemma conv4d_p1_k3_par_eval : forall batch inch outch m input w bias output rho,
  eval (@Conv4d_p1_k3_par_comm batch inch outch m input w bias output) rho =
  eval (@Conv4d_p1_k3_comm batch inch outch m input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu4d_par_eval : forall batch filernum m1 m2 input output rho,
  eval (@ReLU4d_par_comm batch filernum m1 m2 input output) rho =
  eval (@ReLU4d_comm batch filernum m1 m2 input output) rho.
Proof. intros. reflexivity. Qed.

Lemma maxpool4d_k2_par_eval : forall batch ch m input output rho,
  eval (@MaxPool4d_k2_par_comm batch ch m input output) rho =
  eval (@MaxPool4d_k2_comm batch ch m input output) rho.
Proof. intros. reflexivity. Qed.

Lemma linear2d_par_eval : forall batch m outnum w b input output rho,
  eval (@Linear2d_par_comm batch m outnum w b input output) rho =
  eval (@Linear2d_comm batch m outnum w b input output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu2d_par_eval : forall m1 m2 input output rho,
  eval (@ReLU2d_par_comm m1 m2 input output) rho =
  eval (@ReLU2d_comm m1 m2 input output) rho.
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

Theorem vgg16_par_eval_eq : forall rho,
  eval vgg16_par_comm rho = eval vgg16_comm rho.
Proof.
  intros rho. unfold vgg16_par_comm, vgg16_comm.
apply eval_seq_congr; [ intros r0; apply conv4d_p1_k3_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply relu4d_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply conv4d_p1_k3_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply relu4d_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply maxpool4d_k2_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; apply conv4d_p1_k3_par_eval |].
  intros r5. apply eval_seq_congr; [ intros r6; apply relu4d_par_eval |].
  intros r6. apply eval_seq_congr; [ intros r7; apply conv4d_p1_k3_par_eval |].
  intros r7. apply eval_seq_congr; [ intros r8; apply relu4d_par_eval |].
  intros r8. apply eval_seq_congr; [ intros r9; apply maxpool4d_k2_par_eval |].
  intros r9. apply eval_seq_congr; [ intros r10; apply conv4d_p1_k3_par_eval |].
  intros r10. apply eval_seq_congr; [ intros r11; apply relu4d_par_eval |].
  intros r11. apply eval_seq_congr; [ intros r12; apply conv4d_p1_k3_par_eval |].
  intros r12. apply eval_seq_congr; [ intros r13; apply relu4d_par_eval |].
  intros r13. apply eval_seq_congr; [ intros r14; apply conv4d_p1_k3_par_eval |].
  intros r14. apply eval_seq_congr; [ intros r15; apply relu4d_par_eval |].
  intros r15. apply eval_seq_congr; [ intros r16; apply maxpool4d_k2_par_eval |].
  intros r16. apply eval_seq_congr; [ intros r17; apply conv4d_p1_k3_par_eval |].
  intros r17. apply eval_seq_congr; [ intros r18; apply relu4d_par_eval |].
  intros r18. apply eval_seq_congr; [ intros r19; apply conv4d_p1_k3_par_eval |].
  intros r19. apply eval_seq_congr; [ intros r20; apply relu4d_par_eval |].
  intros r20. apply eval_seq_congr; [ intros r21; apply conv4d_p1_k3_par_eval |].
  intros r21. apply eval_seq_congr; [ intros r22; apply relu4d_par_eval |].
  intros r22. apply eval_seq_congr; [ intros r23; apply maxpool4d_k2_par_eval |].
  intros r23. apply eval_seq_congr; [ intros r24; apply conv4d_p1_k3_par_eval |].
  intros r24. apply eval_seq_congr; [ intros r25; apply relu4d_par_eval |].
  intros r25. apply eval_seq_congr; [ intros r26; apply conv4d_p1_k3_par_eval |].
  intros r26. apply eval_seq_congr; [ intros r27; apply relu4d_par_eval |].
  intros r27. apply eval_seq_congr; [ intros r28; apply conv4d_p1_k3_par_eval |].
  intros r28. apply eval_seq_congr; [ intros r29; apply relu4d_par_eval |].
  intros r29. apply eval_seq_congr; [ intros r30; apply maxpool4d_k2_par_eval |].
  intros r30. apply eval_seq_congr; [ intros r31; reflexivity (* flatten: identical *) |].
  intros r31. apply eval_seq_congr; [ intros r32; apply linear2d_par_eval |].
  intros r32. apply eval_seq_congr; [ intros r33; apply relu2d_par_eval |].
  intros r33. apply eval_seq_congr; [ intros r34; apply linear2d_par_eval |].
  intros r34. apply eval_seq_congr; [ intros r35; apply relu2d_par_eval |].
  intros r35. apply linear2d_par_eval.
Qed.

(* -------------------- The 32x32 validation network -------------------- *)

Definition vgg16s_input : exp (ary '{1} (ary '{3} (ary '{32} (ary '{32} num)))) := vrd "input".
Definition vgg16s_conv1_1_w : exp (ary '{64} (ary '{3} (ary '{3} (ary '{3} num)))) := vrd "conv1_1_w".
Definition vgg16s_conv1_1_b : exp (ary '{64} num) := vrd "conv1_1_b".
Definition vgg16s_conv1_1_out : acc (ary '{1} (ary '{64} (ary '{32} (ary '{32} num)))) := vwt "conv1_1_out".
Definition vgg16s_relu1_1_out : acc (ary '{1} (ary '{64} (ary '{32} (ary '{32} num)))) := vwt "relu1_1_out".
Definition vgg16s_conv1_2_w : exp (ary '{64} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "conv1_2_w".
Definition vgg16s_conv1_2_b : exp (ary '{64} num) := vrd "conv1_2_b".
Definition vgg16s_conv1_2_out : acc (ary '{1} (ary '{64} (ary '{32} (ary '{32} num)))) := vwt "conv1_2_out".
Definition vgg16s_relu1_2_out : acc (ary '{1} (ary '{64} (ary '{32} (ary '{32} num)))) := vwt "relu1_2_out".
Definition vgg16s_conv2_1_w : exp (ary '{128} (ary '{64} (ary '{3} (ary '{3} num)))) := vrd "conv2_1_w".
Definition vgg16s_conv2_1_b : exp (ary '{128} num) := vrd "conv2_1_b".
Definition vgg16s_conv2_1_out : acc (ary '{1} (ary '{128} (ary '{16} (ary '{16} num)))) := vwt "conv2_1_out".
Definition vgg16s_relu2_1_out : acc (ary '{1} (ary '{128} (ary '{16} (ary '{16} num)))) := vwt "relu2_1_out".
Definition vgg16s_conv2_2_w : exp (ary '{128} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "conv2_2_w".
Definition vgg16s_conv2_2_b : exp (ary '{128} num) := vrd "conv2_2_b".
Definition vgg16s_conv2_2_out : acc (ary '{1} (ary '{128} (ary '{16} (ary '{16} num)))) := vwt "conv2_2_out".
Definition vgg16s_relu2_2_out : acc (ary '{1} (ary '{128} (ary '{16} (ary '{16} num)))) := vwt "relu2_2_out".
Definition vgg16s_conv3_1_w : exp (ary '{256} (ary '{128} (ary '{3} (ary '{3} num)))) := vrd "conv3_1_w".
Definition vgg16s_conv3_1_b : exp (ary '{256} num) := vrd "conv3_1_b".
Definition vgg16s_conv3_1_out : acc (ary '{1} (ary '{256} (ary '{8} (ary '{8} num)))) := vwt "conv3_1_out".
Definition vgg16s_relu3_1_out : acc (ary '{1} (ary '{256} (ary '{8} (ary '{8} num)))) := vwt "relu3_1_out".
Definition vgg16s_conv3_2_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "conv3_2_w".
Definition vgg16s_conv3_2_b : exp (ary '{256} num) := vrd "conv3_2_b".
Definition vgg16s_conv3_2_out : acc (ary '{1} (ary '{256} (ary '{8} (ary '{8} num)))) := vwt "conv3_2_out".
Definition vgg16s_relu3_2_out : acc (ary '{1} (ary '{256} (ary '{8} (ary '{8} num)))) := vwt "relu3_2_out".
Definition vgg16s_conv3_3_w : exp (ary '{256} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "conv3_3_w".
Definition vgg16s_conv3_3_b : exp (ary '{256} num) := vrd "conv3_3_b".
Definition vgg16s_conv3_3_out : acc (ary '{1} (ary '{256} (ary '{8} (ary '{8} num)))) := vwt "conv3_3_out".
Definition vgg16s_relu3_3_out : acc (ary '{1} (ary '{256} (ary '{8} (ary '{8} num)))) := vwt "relu3_3_out".
Definition vgg16s_conv4_1_w : exp (ary '{512} (ary '{256} (ary '{3} (ary '{3} num)))) := vrd "conv4_1_w".
Definition vgg16s_conv4_1_b : exp (ary '{512} num) := vrd "conv4_1_b".
Definition vgg16s_conv4_1_out : acc (ary '{1} (ary '{512} (ary '{4} (ary '{4} num)))) := vwt "conv4_1_out".
Definition vgg16s_relu4_1_out : acc (ary '{1} (ary '{512} (ary '{4} (ary '{4} num)))) := vwt "relu4_1_out".
Definition vgg16s_conv4_2_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv4_2_w".
Definition vgg16s_conv4_2_b : exp (ary '{512} num) := vrd "conv4_2_b".
Definition vgg16s_conv4_2_out : acc (ary '{1} (ary '{512} (ary '{4} (ary '{4} num)))) := vwt "conv4_2_out".
Definition vgg16s_relu4_2_out : acc (ary '{1} (ary '{512} (ary '{4} (ary '{4} num)))) := vwt "relu4_2_out".
Definition vgg16s_conv4_3_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv4_3_w".
Definition vgg16s_conv4_3_b : exp (ary '{512} num) := vrd "conv4_3_b".
Definition vgg16s_conv4_3_out : acc (ary '{1} (ary '{512} (ary '{4} (ary '{4} num)))) := vwt "conv4_3_out".
Definition vgg16s_relu4_3_out : acc (ary '{1} (ary '{512} (ary '{4} (ary '{4} num)))) := vwt "relu4_3_out".
Definition vgg16s_conv5_1_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv5_1_w".
Definition vgg16s_conv5_1_b : exp (ary '{512} num) := vrd "conv5_1_b".
Definition vgg16s_conv5_1_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "conv5_1_out".
Definition vgg16s_relu5_1_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "relu5_1_out".
Definition vgg16s_conv5_2_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv5_2_w".
Definition vgg16s_conv5_2_b : exp (ary '{512} num) := vrd "conv5_2_b".
Definition vgg16s_conv5_2_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "conv5_2_out".
Definition vgg16s_relu5_2_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "relu5_2_out".
Definition vgg16s_conv5_3_w : exp (ary '{512} (ary '{512} (ary '{3} (ary '{3} num)))) := vrd "conv5_3_w".
Definition vgg16s_conv5_3_b : exp (ary '{512} num) := vrd "conv5_3_b".
Definition vgg16s_conv5_3_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "conv5_3_out".
Definition vgg16s_relu5_3_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "relu5_3_out".
Definition vgg16s_pool1_out : acc (ary '{1} (ary '{64} (ary '{16} (ary '{16} num)))) := vwt "pool1_out".
Definition vgg16s_pool2_out : acc (ary '{1} (ary '{128} (ary '{8} (ary '{8} num)))) := vwt "pool2_out".
Definition vgg16s_pool3_out : acc (ary '{1} (ary '{256} (ary '{4} (ary '{4} num)))) := vwt "pool3_out".
Definition vgg16s_pool4_out : acc (ary '{1} (ary '{512} (ary '{2} (ary '{2} num)))) := vwt "pool4_out".
Definition vgg16s_pool5_out : acc (ary '{1} (ary '{512} (ary '{1} (ary '{1} num)))) := vwt "pool5_out".
Definition vgg16s_flatten_out : acc (ary '{1} (ary '{512} num)) := vwt "flatten_out".
Definition vgg16s_fc1_w : exp (ary '{4096} (ary '{512} num)) := vrd "fc1_w".
Definition vgg16s_fc1_b : exp (ary '{4096} num) := vrd "fc1_b".
Definition vgg16s_fc1_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc1_out".
Definition vgg16s_fc1_relu_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc1_relu_out".
Definition vgg16s_fc2_w : exp (ary '{4096} (ary '{4096} num)) := vrd "fc2_w".
Definition vgg16s_fc2_b : exp (ary '{4096} num) := vrd "fc2_b".
Definition vgg16s_fc2_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc2_out".
Definition vgg16s_fc2_relu_out : acc (ary '{1} (ary '{4096} num)) := vwt "fc2_relu_out".
Definition vgg16s_fc3_w : exp (ary '{1000} (ary '{4096} num)) := vrd "fc3_w".
Definition vgg16s_fc3_b : exp (ary '{1000} num) := vrd "fc3_b".
Definition vgg16s_output : acc (ary '{1} (ary '{1000} num)) := vwt "output".


Definition vgg16s_par_comm : comm :=
  @Conv4d_p1_k3_par_comm 1 3 64 32
    vgg16s_input vgg16s_conv1_1_w vgg16s_conv1_1_b vgg16s_conv1_1_out ';
  @ReLU4d_par_comm 1 64 32 32
    (vrd "conv1_1_out") vgg16s_relu1_1_out ';
  @Conv4d_p1_k3_par_comm 1 64 64 32
    (vrd "relu1_1_out") vgg16s_conv1_2_w vgg16s_conv1_2_b vgg16s_conv1_2_out ';
  @ReLU4d_par_comm 1 64 32 32
    (vrd "conv1_2_out") vgg16s_relu1_2_out ';
  @MaxPool4d_k2_par_comm 1 64 32
    (vrd "relu1_2_out") vgg16s_pool1_out ';
  @Conv4d_p1_k3_par_comm 1 64 128 16
    (vrd "relu1_2_out") vgg16s_conv2_1_w vgg16s_conv2_1_b vgg16s_conv2_1_out ';
  @ReLU4d_par_comm 1 128 16 16
    (vrd "conv2_1_out") vgg16s_relu2_1_out ';
  @Conv4d_p1_k3_par_comm 1 128 128 16
    (vrd "relu2_1_out") vgg16s_conv2_2_w vgg16s_conv2_2_b vgg16s_conv2_2_out ';
  @ReLU4d_par_comm 1 128 16 16
    (vrd "conv2_2_out") vgg16s_relu2_2_out ';
  @MaxPool4d_k2_par_comm 1 128 16
    (vrd "relu2_2_out") vgg16s_pool2_out ';
  @Conv4d_p1_k3_par_comm 1 128 256 8
    (vrd "relu2_2_out") vgg16s_conv3_1_w vgg16s_conv3_1_b vgg16s_conv3_1_out ';
  @ReLU4d_par_comm 1 256 8 8
    (vrd "conv3_1_out") vgg16s_relu3_1_out ';
  @Conv4d_p1_k3_par_comm 1 256 256 8
    (vrd "relu3_1_out") vgg16s_conv3_2_w vgg16s_conv3_2_b vgg16s_conv3_2_out ';
  @ReLU4d_par_comm 1 256 8 8
    (vrd "conv3_2_out") vgg16s_relu3_2_out ';
  @Conv4d_p1_k3_par_comm 1 256 256 8
    (vrd "relu3_2_out") vgg16s_conv3_3_w vgg16s_conv3_3_b vgg16s_conv3_3_out ';
  @ReLU4d_par_comm 1 256 8 8
    (vrd "conv3_3_out") vgg16s_relu3_3_out ';
  @MaxPool4d_k2_par_comm 1 256 8
    (vrd "relu3_3_out") vgg16s_pool3_out ';
  @Conv4d_p1_k3_par_comm 1 256 512 4
    (vrd "relu3_3_out") vgg16s_conv4_1_w vgg16s_conv4_1_b vgg16s_conv4_1_out ';
  @ReLU4d_par_comm 1 512 4 4
    (vrd "conv4_1_out") vgg16s_relu4_1_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 4
    (vrd "relu4_1_out") vgg16s_conv4_2_w vgg16s_conv4_2_b vgg16s_conv4_2_out ';
  @ReLU4d_par_comm 1 512 4 4
    (vrd "conv4_2_out") vgg16s_relu4_2_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 4
    (vrd "relu4_2_out") vgg16s_conv4_3_w vgg16s_conv4_3_b vgg16s_conv4_3_out ';
  @ReLU4d_par_comm 1 512 4 4
    (vrd "conv4_3_out") vgg16s_relu4_3_out ';
  @MaxPool4d_k2_par_comm 1 512 4
    (vrd "relu4_3_out") vgg16s_pool4_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 2
    (vrd "relu4_3_out") vgg16s_conv5_1_w vgg16s_conv5_1_b vgg16s_conv5_1_out ';
  @ReLU4d_par_comm 1 512 2 2
    (vrd "conv5_1_out") vgg16s_relu5_1_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 2
    (vrd "relu5_1_out") vgg16s_conv5_2_w vgg16s_conv5_2_b vgg16s_conv5_2_out ';
  @ReLU4d_par_comm 1 512 2 2
    (vrd "conv5_2_out") vgg16s_relu5_2_out ';
  @Conv4d_p1_k3_par_comm 1 512 512 2
    (vrd "relu5_2_out") vgg16s_conv5_3_w vgg16s_conv5_3_b vgg16s_conv5_3_out ';
  @ReLU4d_par_comm 1 512 2 2
    (vrd "conv5_3_out") vgg16s_relu5_3_out ';
  @MaxPool4d_k2_par_comm 1 512 2
    (vrd "relu5_3_out") vgg16s_pool5_out ';
  @Flatten4d_comm 1 512 1 1
    (vrd "pool5_out") vgg16s_flatten_out ';
  @Linear2d_par_comm 1 512 4096
    vgg16s_fc1_w vgg16s_fc1_b (vrd "flatten_out") vgg16s_fc1_out ';
  @ReLU2d_par_comm 1 4096
    (vrd "fc1_out") vgg16s_fc1_relu_out ';
  @Linear2d_par_comm 1 4096 4096
    vgg16s_fc2_w vgg16s_fc2_b (vrd "fc1_relu_out") vgg16s_fc2_out ';
  @ReLU2d_par_comm 1 4096
    (vrd "fc2_out") vgg16s_fc2_relu_out ';
  @Linear2d_par_comm 1 4096 1000
    vgg16s_fc3_w vgg16s_fc3_b (vrd "fc2_relu_out") vgg16s_output.

Definition vgg16s_comm : comm :=
  @Conv4d_p1_k3_comm 1 3 64 32
    vgg16s_input vgg16s_conv1_1_w vgg16s_conv1_1_b vgg16s_conv1_1_out ';
  @ReLU4d_comm 1 64 32 32
    (vrd "conv1_1_out") vgg16s_relu1_1_out ';
  @Conv4d_p1_k3_comm 1 64 64 32
    (vrd "relu1_1_out") vgg16s_conv1_2_w vgg16s_conv1_2_b vgg16s_conv1_2_out ';
  @ReLU4d_comm 1 64 32 32
    (vrd "conv1_2_out") vgg16s_relu1_2_out ';
  @MaxPool4d_k2_comm 1 64 32
    (vrd "relu1_2_out") vgg16s_pool1_out ';
  @Conv4d_p1_k3_comm 1 64 128 16
    (vrd "relu1_2_out") vgg16s_conv2_1_w vgg16s_conv2_1_b vgg16s_conv2_1_out ';
  @ReLU4d_comm 1 128 16 16
    (vrd "conv2_1_out") vgg16s_relu2_1_out ';
  @Conv4d_p1_k3_comm 1 128 128 16
    (vrd "relu2_1_out") vgg16s_conv2_2_w vgg16s_conv2_2_b vgg16s_conv2_2_out ';
  @ReLU4d_comm 1 128 16 16
    (vrd "conv2_2_out") vgg16s_relu2_2_out ';
  @MaxPool4d_k2_comm 1 128 16
    (vrd "relu2_2_out") vgg16s_pool2_out ';
  @Conv4d_p1_k3_comm 1 128 256 8
    (vrd "relu2_2_out") vgg16s_conv3_1_w vgg16s_conv3_1_b vgg16s_conv3_1_out ';
  @ReLU4d_comm 1 256 8 8
    (vrd "conv3_1_out") vgg16s_relu3_1_out ';
  @Conv4d_p1_k3_comm 1 256 256 8
    (vrd "relu3_1_out") vgg16s_conv3_2_w vgg16s_conv3_2_b vgg16s_conv3_2_out ';
  @ReLU4d_comm 1 256 8 8
    (vrd "conv3_2_out") vgg16s_relu3_2_out ';
  @Conv4d_p1_k3_comm 1 256 256 8
    (vrd "relu3_2_out") vgg16s_conv3_3_w vgg16s_conv3_3_b vgg16s_conv3_3_out ';
  @ReLU4d_comm 1 256 8 8
    (vrd "conv3_3_out") vgg16s_relu3_3_out ';
  @MaxPool4d_k2_comm 1 256 8
    (vrd "relu3_3_out") vgg16s_pool3_out ';
  @Conv4d_p1_k3_comm 1 256 512 4
    (vrd "relu3_3_out") vgg16s_conv4_1_w vgg16s_conv4_1_b vgg16s_conv4_1_out ';
  @ReLU4d_comm 1 512 4 4
    (vrd "conv4_1_out") vgg16s_relu4_1_out ';
  @Conv4d_p1_k3_comm 1 512 512 4
    (vrd "relu4_1_out") vgg16s_conv4_2_w vgg16s_conv4_2_b vgg16s_conv4_2_out ';
  @ReLU4d_comm 1 512 4 4
    (vrd "conv4_2_out") vgg16s_relu4_2_out ';
  @Conv4d_p1_k3_comm 1 512 512 4
    (vrd "relu4_2_out") vgg16s_conv4_3_w vgg16s_conv4_3_b vgg16s_conv4_3_out ';
  @ReLU4d_comm 1 512 4 4
    (vrd "conv4_3_out") vgg16s_relu4_3_out ';
  @MaxPool4d_k2_comm 1 512 4
    (vrd "relu4_3_out") vgg16s_pool4_out ';
  @Conv4d_p1_k3_comm 1 512 512 2
    (vrd "relu4_3_out") vgg16s_conv5_1_w vgg16s_conv5_1_b vgg16s_conv5_1_out ';
  @ReLU4d_comm 1 512 2 2
    (vrd "conv5_1_out") vgg16s_relu5_1_out ';
  @Conv4d_p1_k3_comm 1 512 512 2
    (vrd "relu5_1_out") vgg16s_conv5_2_w vgg16s_conv5_2_b vgg16s_conv5_2_out ';
  @ReLU4d_comm 1 512 2 2
    (vrd "conv5_2_out") vgg16s_relu5_2_out ';
  @Conv4d_p1_k3_comm 1 512 512 2
    (vrd "relu5_2_out") vgg16s_conv5_3_w vgg16s_conv5_3_b vgg16s_conv5_3_out ';
  @ReLU4d_comm 1 512 2 2
    (vrd "conv5_3_out") vgg16s_relu5_3_out ';
  @MaxPool4d_k2_comm 1 512 2
    (vrd "relu5_3_out") vgg16s_pool5_out ';
  @Flatten4d_comm 1 512 1 1
    (vrd "pool5_out") vgg16s_flatten_out ';
  @Linear2d_comm 1 512 4096
    vgg16s_fc1_w vgg16s_fc1_b (vrd "flatten_out") vgg16s_fc1_out ';
  @ReLU2d_comm 1 4096
    (vrd "fc1_out") vgg16s_fc1_relu_out ';
  @Linear2d_comm 1 4096 4096
    vgg16s_fc2_w vgg16s_fc2_b (vrd "fc1_relu_out") vgg16s_fc2_out ';
  @ReLU2d_comm 1 4096
    (vrd "fc2_out") vgg16s_fc2_relu_out ';
  @Linear2d_comm 1 4096 1000
    vgg16s_fc3_w vgg16s_fc3_b (vrd "fc2_relu_out") vgg16s_output.

Theorem vgg16s_par_eval_eq : forall rho,
  eval vgg16s_par_comm rho = eval vgg16s_comm rho.
Proof.
  intros rho. unfold vgg16s_par_comm, vgg16s_comm.
apply eval_seq_congr; [ intros r0; apply conv4d_p1_k3_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply relu4d_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply conv4d_p1_k3_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply relu4d_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply maxpool4d_k2_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; apply conv4d_p1_k3_par_eval |].
  intros r5. apply eval_seq_congr; [ intros r6; apply relu4d_par_eval |].
  intros r6. apply eval_seq_congr; [ intros r7; apply conv4d_p1_k3_par_eval |].
  intros r7. apply eval_seq_congr; [ intros r8; apply relu4d_par_eval |].
  intros r8. apply eval_seq_congr; [ intros r9; apply maxpool4d_k2_par_eval |].
  intros r9. apply eval_seq_congr; [ intros r10; apply conv4d_p1_k3_par_eval |].
  intros r10. apply eval_seq_congr; [ intros r11; apply relu4d_par_eval |].
  intros r11. apply eval_seq_congr; [ intros r12; apply conv4d_p1_k3_par_eval |].
  intros r12. apply eval_seq_congr; [ intros r13; apply relu4d_par_eval |].
  intros r13. apply eval_seq_congr; [ intros r14; apply conv4d_p1_k3_par_eval |].
  intros r14. apply eval_seq_congr; [ intros r15; apply relu4d_par_eval |].
  intros r15. apply eval_seq_congr; [ intros r16; apply maxpool4d_k2_par_eval |].
  intros r16. apply eval_seq_congr; [ intros r17; apply conv4d_p1_k3_par_eval |].
  intros r17. apply eval_seq_congr; [ intros r18; apply relu4d_par_eval |].
  intros r18. apply eval_seq_congr; [ intros r19; apply conv4d_p1_k3_par_eval |].
  intros r19. apply eval_seq_congr; [ intros r20; apply relu4d_par_eval |].
  intros r20. apply eval_seq_congr; [ intros r21; apply conv4d_p1_k3_par_eval |].
  intros r21. apply eval_seq_congr; [ intros r22; apply relu4d_par_eval |].
  intros r22. apply eval_seq_congr; [ intros r23; apply maxpool4d_k2_par_eval |].
  intros r23. apply eval_seq_congr; [ intros r24; apply conv4d_p1_k3_par_eval |].
  intros r24. apply eval_seq_congr; [ intros r25; apply relu4d_par_eval |].
  intros r25. apply eval_seq_congr; [ intros r26; apply conv4d_p1_k3_par_eval |].
  intros r26. apply eval_seq_congr; [ intros r27; apply relu4d_par_eval |].
  intros r27. apply eval_seq_congr; [ intros r28; apply conv4d_p1_k3_par_eval |].
  intros r28. apply eval_seq_congr; [ intros r29; apply relu4d_par_eval |].
  intros r29. apply eval_seq_congr; [ intros r30; apply maxpool4d_k2_par_eval |].
  intros r30. apply eval_seq_congr; [ intros r31; reflexivity (* flatten: identical *) |].
  intros r31. apply eval_seq_congr; [ intros r32; apply linear2d_par_eval |].
  intros r32. apply eval_seq_congr; [ intros r33; apply relu2d_par_eval |].
  intros r33. apply eval_seq_congr; [ intros r34; apply linear2d_par_eval |].
  intros r34. apply eval_seq_congr; [ intros r35; apply relu2d_par_eval |].
  intros r35. apply linear2d_par_eval.
Qed.


(* -------------------- Extraction for the streaming printer -------------------- *)

Extraction "vgg16s.ml" vgg16s_comm vgg16s_par_comm.

(* Full-size (224x224) extraction: optional performance data point. *)
Extraction "vgg16p.ml" vgg16_comm vgg16_par_comm.
