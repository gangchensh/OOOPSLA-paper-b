(* ========================================================================= *)
(* ResNet18_Par.v                                                            *)
(*                                                                           *)
(* OpenMP (M7): a parallel variant of the concrete imperative ResNet-18 AST  *)
(* [CNN_Examples_ResNet18.resnet18_comm] (ImageNet, batch = 1, 224x224).     *)
(*                                                                           *)
(* Parallelization scheme (same recipe as [LeNet5_Par]): the outermost loop  *)
(* of every 4-D layer is the batch loop (batch = 1, useless to parallelize), *)
(* so the CHANNEL loop (second outermost) is turned from [seqfor] into       *)
(* [parfor] via [parfor (output|{b}) (fun c o => ...)]: convolution output   *)
(* channels and padding-fill channels, BatchNorm / ReLU / residual Add       *)
(* channels, GlobalAvgPool channels, and Linear output units.  Every         *)
(* reduction inner loop (convolution window accumulation, GAP sum, Linear    *)
(* dot product, MaxPool window max scan) stays sequential because the        *)
(* accumulator dependency forbids parallelization.                           *)
(*                                                                           *)
(* Correctness: CG.parfor and CG.seqfor are different constructors, but      *)
(* [CNN_CodeGen_Semantics.eval_aux] maps both to the same [PCG.seqfor], so   *)
(* each layer is eval-equal BY CONVERSION (one constructor depth,            *)
(* [reflexivity]); [eval_seq_congr] then composes the per-layer equalities   *)
(* into the whole-net [resnet18_par_eval_eq].  Hence every semantic          *)
(* property of the sequential net — in particular the route-A/route-B        *)
(* bridge of [Bridge_ResNet18] (BatchNorm bridge stated for batch = 1) —     *)
(* transfers literally to the parallel net.                                  *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

Require Import Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_Examples_Base_Ops.
Require Import Ionia.CNN_CodeGen_Semantics.
Require Import Ionia.CNN_Examples_ResNet18.

From Stdlib Require Import List String.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

(* -------------------- Parallel layer variants -------------------- *)

(* 3x3 conv, padding=1, stride=1: pad-fill and conv loops parallel over
   channels (fin inch / fin outch); window reduction sequential. *)
Definition Conv4d_p1_k3_par_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{m} (ary '{m} num))))) : comm :=
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => parfor (pad_a|{b}) (fun c po => seqfor (fun i: fin (m + 2) => seqfor (fun j: fin (m + 2) =>
      If (BLt (fin2nat i) 1)
      (po|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (S m))
        (If (BLt (fin2nat j) 1)
          (po|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (S m))
            (po|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 1)) (fin2nat j - 1),
             po|{i}|{j} |:= zero)),
         po|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => parfor (output|{b}) (fun num o => seqfor (fun i0: fin m => seqfor (fun j0: fin m =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin inch => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        o|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))
  ).

(* 3x3 conv, padding=1, stride=2 (BasicBlock first conv of a projection
   block): same scheme; output spatial size halves. *)
Definition Conv4d_p1_k3_s2_par_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num))))) : comm :=
  let half := (m - 3 + 2 * 1) / 2 + 1 in
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => parfor (pad_a|{b}) (fun c po => seqfor (fun i: fin (m + 2) => seqfor (fun j: fin (m + 2) =>
      If (BLt (fin2nat i) 1)
      (po|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (S m))
        (If (BLt (fin2nat j) 1)
          (po|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (S m))
            (po|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 1)) (fin2nat j - 1),
             po|{i}|{j} |:= zero)),
         po|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => parfor (output|{b}) (fun num o => seqfor (fun i0: fin half => seqfor (fun j0: fin half =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin inch => seqfor (fun i1: fin 3 => seqfor (fun j1: fin 3 =>
          let ii := 2 * (fin2nat i0) + (fin2nat i1) in
          let jj := 2 * (fin2nat j0) + (fin2nat j1) in
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] ii) jj) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        o|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))
  ).

(* 1x1 conv, padding=0, stride=2 (shortcut projection): parallel over output
   channels; channel reduction sequential. *)
Definition Conv4d_p0_k1_s2_par_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num))))) : comm :=
  let half := (m - 1 + 0) / 2 + 1 in
  seqfor (fun b: fin batch => parfor (output|{b}) (fun num o => seqfor (fun i0: fin half => seqfor (fun j0: fin half =>
    new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
      acc_a |:= zero ';
      seqfor (fun c: fin inch =>
        let ii := 2 * (fin2nat i0) in
        let jj := 2 * (fin2nat j0) in
        acc_a |:= add (mul (safe_idx_nat (safe_idx_nat input|[b]|[c] ii) jj) (safe_idx_nat (safe_idx_nat (w|[num]|[c]) 0) 0)) acc_v
      ) ';
      o|{i0}|{j0} |:= add acc_v bias|[num]
    )
  )))).

(* 7x7 conv, padding=3, stride=2 (ImageNet stem): pad-fill and conv loops
   parallel over channels; window reduction sequential. *)
Definition Conv4d_p3_k7_s2_par_comm {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{7} (ary '{7} num)))))
  (bias: exp (ary '{outch} num))
  (output: acc (ary '{batch} (ary '{outch} (ary '{((m - 7 + 2 * 3) / 2 + 1)} (ary '{((m - 7 + 2 * 3) / 2 + 1)} num))))) : comm :=
  let half := (m - 7 + 2 * 3) / 2 + 1 in
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => parfor (pad_a|{b}) (fun c po => seqfor (fun i: fin (m + 6) => seqfor (fun j: fin (m + 6) =>
      If (BLt (fin2nat i) 3)
      (po|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (3 + m))
        (If (BLt (fin2nat j) 3)
          (po|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (3 + m))
            (po|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - 3)) (fin2nat j - 3),
             po|{i}|{j} |:= zero)),
         po|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => parfor (output|{b}) (fun num o => seqfor (fun i0: fin half => seqfor (fun j0: fin half =>
      new (fun acc_tmp => let (acc_a, acc_v) := acc_tmp in
        acc_a |:= zero ';
        seqfor (fun c: fin inch => seqfor (fun i1: fin 7 => seqfor (fun j1: fin 7 =>
          let ii := 2 * (fin2nat i0) + (fin2nat i1) in
          let jj := 2 * (fin2nat j0) + (fin2nat j1) in
          acc_a |:= add (mul (safe_idx_nat (safe_idx_nat pad_v|[b]|[c] ii) jj) w|[num]|[c]|[i1]|[j1]) acc_v
        ))) ';
        o|{i0}|{j0} |:= add acc_v bias|[num]
      )
    ))))
  ).

(* BatchNorm4d (inference): parallel over channels. *)
Definition BatchNorm4d_par_comm {batch channel n1 n2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (mean var gamma beta: exp (ary '{channel} num))
  (eps: exp num)
  (output: acc (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) : comm :=
  seqfor (fun b => parfor (output|{b}) (fun c o => seqfor (fun i => seqfor (fun j =>
    let x := sub input|[b]|[c]|[i]|[j] mean|[c] in
    let norm := div x (sqrt (add var|[c] eps)) in
    o|{i}|{j} |:= add (mul norm gamma|[c]) beta|[c])))).

(* ReLU4d: parallel over channels. *)
Definition ReLU4d_par_comm {batch filernum m1 m2}
  (input: exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b => parfor (output|{b}) (fun num o => seqfor (fun i0 => seqfor (fun i1 =>
    If (leExp input|[b]|[num]|[i0]|[i1] zero)
      (o|{i0}|{i1} |:= zero,
       o|{i0}|{i1} |:= input|[b]|[num]|[i0]|[i1]))))).

(* Add4d (residual add): parallel over channels. *)
Definition Add4d_par_comm {batch channel n1 n2}
  (x y: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (output: acc (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num))))) : comm :=
  seqfor (fun b => parfor (output|{b}) (fun c o => seqfor (fun i => seqfor (fun j =>
    o|{i}|{j} |:= add x|[b]|[c]|[i]|[j] y|[b]|[c]|[i]|[j])))).

(* Max pooling k x k stride s padding p: pad-fill and pooling loops parallel
   over channels; window max scan sequential. *)
Definition MaxPool4d_pad_par_comm {batch channel m k s p}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m} (ary '{m} num)))))
  (output: acc (ary '{batch} (ary '{channel} (ary '{((m - k + 2 * p) / s + 1)} (ary '{((m - k + 2 * p) / s + 1)} num))))) : comm :=
  let outm := (m - k + 2 * p) / s + 1 in
  let padm := m + 2 * p in
  new (fun pad_tmp => let (pad_a, pad_v) := pad_tmp in
    seqfor (fun b: fin batch => parfor (pad_a|{b}) (fun c po => seqfor (fun i: fin padm => seqfor (fun j: fin padm =>
      If (BLt (fin2nat i) p)
      (po|{i}|{j} |:= zero,
       If (BLt (fin2nat i) (p + m))
        (If (BLt (fin2nat j) p)
          (po|{i}|{j} |:= zero,
           If (BLt (fin2nat j) (p + m))
            (po|{i}|{j} |:= safe_idx_nat (safe_idx_nat input|[b]|[c] (fin2nat i - p)) (fin2nat j - p),
             po|{i}|{j} |:= zero)),
         po|{i}|{j} |:= zero))
    )))) ';
    seqfor (fun b: fin batch => parfor (output|{b}) (fun c o => seqfor (fun i0: fin outm => seqfor (fun j0: fin outm =>
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
        o|{i0}|{j0} |:= acc_v
      )
    ))))
  ).

(* Global average pooling: parallel over channels; the spatial sum reduction
   stays sequential (loopacc). *)
Definition GlobalAvgPool4d_par_comm {batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{channel} num))) : comm :=
  seqfor (fun b => parfor (output|{b}) (fun c o =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      acc_a |:= zero ';
      seqfor (fun k : fin (m1 * m2) =>
        let i := Nat.div (fin2nat k) m2 in
        let j := Nat.modulo (fin2nat k) m2 in
        acc_a |:= add (safe_idx_nat (safe_idx_nat input|[b]|[c] i) j) acc_v
      ) ';
      o |:= div_n acc_v (m1 * m2)
    )
  )).

(* Linear (fully connected): parallel over output units; dot-product
   reduction sequential (loopacc). *)
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

(* -------------------- Parallel BasicBlocks -------------------- *)

(* Identity BasicBlock, parallel variant of [ResNet_BB_id_comm]. *)
Definition ResNet_BB_id_par_comm {batch ch m}
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
  @Conv4d_p1_k3_par_comm batch ch ch m input w1 b1 conv1_out ';
  @BatchNorm4d_par_comm batch ch m m (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_par_comm batch ch m m (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_par_comm batch ch ch m (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_par_comm batch ch m m (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @Add4d_par_comm batch ch m m (vrd bn2_s) input add_out ';
  @ReLU4d_par_comm batch ch m m (vrd add_s) add_out.

(* Projection-shortcut BasicBlock, parallel variant of [ResNet_BB_proj_comm]. *)
Definition ResNet_BB_proj_par_comm {batch inch outch m}
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
  @Conv4d_p0_k1_s2_par_comm batch inch outch m input shortcut_w shortcut_b shortcut_out ';
  @BatchNorm4d_par_comm batch outch ((m - 1 + 0) / 2 + 1) ((m - 1 + 0) / 2 + 1)
    (vrd shortcut_s) shortcut_mean shortcut_var shortcut_gamma shortcut_beta eps shortcut_out ';
  @Conv4d_p1_k3_s2_par_comm batch inch outch m input w1 b1 conv1_out ';
  @BatchNorm4d_par_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd conv1_s) mean1 var1 gamma1 beta1 eps bn1_out ';
  @ReLU4d_par_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1) (vrd bn1_s) relu1_out ';
  @Conv4d_p1_k3_par_comm batch outch outch ((m - 3 + 2 * 1) / 2 + 1) (vrd relu1_s) w2 b2 conv2_out ';
  @BatchNorm4d_par_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd conv2_s) mean2 var2 gamma2 beta2 eps bn2_out ';
  @Add4d_par_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1)
    (vrd bn2_s) (vrd shortcut_s) add_out ';
  @ReLU4d_par_comm batch outch ((m - 3 + 2 * 1) / 2 + 1) ((m - 3 + 2 * 1) / 2 + 1) (vrd add_s) add_out.

(* -------------------- The parallel whole-net AST -------------------- *)

(* Same buffers/weights as [CNN_Examples_ResNet18.resnet18_comm]; only the
   layer combinators are replaced by their parallel variants. *)
Definition resnet18_par_comm : comm :=
  @Conv4d_p3_k7_s2_par_comm 1 3 64 224 resnet18_input resnet18_conv1_w resnet18_conv1_b resnet18_conv1_out ';
  @BatchNorm4d_par_comm 1 64 112 112 (vrd "conv1_out") resnet18_bn1_mean resnet18_bn1_var resnet18_bn1_gamma resnet18_bn1_beta resnet18_eps resnet18_bn1_out ';
  @ReLU4d_par_comm 1 64 112 112 (vrd "bn1_out") resnet18_relu1_out ';
  @MaxPool4d_pad_par_comm 1 64 112 3 2 1 (vrd "relu1_out") resnet18_pool_out ';

  @ResNet_BB_id_par_comm 1 64 56
    (vrd "pool_out")
    resnet18_l1_b1_w1 resnet18_l1_b1_b1 resnet18_l1_b1_w2 resnet18_l1_b1_b2
    resnet18_l1_b1_bn1_mean resnet18_l1_b1_bn1_var resnet18_l1_b1_bn1_gamma resnet18_l1_b1_bn1_beta
    resnet18_l1_b1_bn2_mean resnet18_l1_b1_bn2_var resnet18_l1_b1_bn2_gamma resnet18_l1_b1_bn2_beta
    resnet18_eps
    resnet18_l1_b1_conv1_out resnet18_l1_b1_bn1_out resnet18_l1_b1_relu1_out
    resnet18_l1_b1_conv2_out resnet18_l1_b1_bn2_out resnet18_l1_b1_add_out
    "l1_b1_conv1_out" "l1_b1_bn1_out" "l1_b1_relu1_out" "l1_b1_conv2_out" "l1_b1_bn2_out" "l1_b1_add_out" ';

  @ResNet_BB_id_par_comm 1 64 56
    (vrd "l1_b1_add_out")
    resnet18_l1_b2_w1 resnet18_l1_b2_b1 resnet18_l1_b2_w2 resnet18_l1_b2_b2
    resnet18_l1_b2_bn1_mean resnet18_l1_b2_bn1_var resnet18_l1_b2_bn1_gamma resnet18_l1_b2_bn1_beta
    resnet18_l1_b2_bn2_mean resnet18_l1_b2_bn2_var resnet18_l1_b2_bn2_gamma resnet18_l1_b2_bn2_beta
    resnet18_eps
    resnet18_l1_b2_conv1_out resnet18_l1_b2_bn1_out resnet18_l1_b2_relu1_out
    resnet18_l1_b2_conv2_out resnet18_l1_b2_bn2_out resnet18_l1_b2_add_out
    "l1_b2_conv1_out" "l1_b2_bn1_out" "l1_b2_relu1_out" "l1_b2_conv2_out" "l1_b2_bn2_out" "l1_b2_add_out" ';

  @ResNet_BB_proj_par_comm 1 64 128 56
    (vrd "l1_b2_add_out")
    resnet18_l2_b1_w1 resnet18_l2_b1_b1 resnet18_l2_b1_w2 resnet18_l2_b1_b2
    resnet18_l2_b1_bn1_mean resnet18_l2_b1_bn1_var resnet18_l2_b1_bn1_gamma resnet18_l2_b1_bn1_beta
    resnet18_l2_b1_bn2_mean resnet18_l2_b1_bn2_var resnet18_l2_b1_bn2_gamma resnet18_l2_b1_bn2_beta
    resnet18_eps
    resnet18_l2_b1_conv1_out resnet18_l2_b1_bn1_out resnet18_l2_b1_relu1_out
    resnet18_l2_b1_conv2_out resnet18_l2_b1_bn2_out resnet18_l2_b1_add_out
    resnet18_l2_b1_shortcut_out
    resnet18_l2_b1_shortcut_w resnet18_l2_b1_shortcut_b
    resnet18_l2_b1_shortcut_mean resnet18_l2_b1_shortcut_var
    resnet18_l2_b1_shortcut_gamma resnet18_l2_b1_shortcut_beta
    "l2_b1_shortcut_out" "l2_b1_conv1_out" "l2_b1_bn1_out" "l2_b1_relu1_out"
    "l2_b1_conv2_out" "l2_b1_bn2_out" "l2_b1_add_out" ';

  @ResNet_BB_id_par_comm 1 128 28
    (vrd "l2_b1_add_out")
    resnet18_l2_b2_w1 resnet18_l2_b2_b1 resnet18_l2_b2_w2 resnet18_l2_b2_b2
    resnet18_l2_b2_bn1_mean resnet18_l2_b2_bn1_var resnet18_l2_b2_bn1_gamma resnet18_l2_b2_bn1_beta
    resnet18_l2_b2_bn2_mean resnet18_l2_b2_bn2_var resnet18_l2_b2_bn2_gamma resnet18_l2_b2_bn2_beta
    resnet18_eps
    resnet18_l2_b2_conv1_out resnet18_l2_b2_bn1_out resnet18_l2_b2_relu1_out
    resnet18_l2_b2_conv2_out resnet18_l2_b2_bn2_out resnet18_l2_b2_add_out
    "l2_b2_conv1_out" "l2_b2_bn1_out" "l2_b2_relu1_out" "l2_b2_conv2_out" "l2_b2_bn2_out" "l2_b2_add_out" ';

  @ResNet_BB_proj_par_comm 1 128 256 28
    (vrd "l2_b2_add_out")
    resnet18_l3_b1_w1 resnet18_l3_b1_b1 resnet18_l3_b1_w2 resnet18_l3_b1_b2
    resnet18_l3_b1_bn1_mean resnet18_l3_b1_bn1_var resnet18_l3_b1_bn1_gamma resnet18_l3_b1_bn1_beta
    resnet18_l3_b1_bn2_mean resnet18_l3_b1_bn2_var resnet18_l3_b1_bn2_gamma resnet18_l3_b1_bn2_beta
    resnet18_eps
    resnet18_l3_b1_conv1_out resnet18_l3_b1_bn1_out resnet18_l3_b1_relu1_out
    resnet18_l3_b1_conv2_out resnet18_l3_b1_bn2_out resnet18_l3_b1_add_out
    resnet18_l3_b1_shortcut_out
    resnet18_l3_b1_shortcut_w resnet18_l3_b1_shortcut_b
    resnet18_l3_b1_shortcut_mean resnet18_l3_b1_shortcut_var
    resnet18_l3_b1_shortcut_gamma resnet18_l3_b1_shortcut_beta
    "l3_b1_shortcut_out" "l3_b1_conv1_out" "l3_b1_bn1_out" "l3_b1_relu1_out"
    "l3_b1_conv2_out" "l3_b1_bn2_out" "l3_b1_add_out" ';

  @ResNet_BB_id_par_comm 1 256 14
    (vrd "l3_b1_add_out")
    resnet18_l3_b2_w1 resnet18_l3_b2_b1 resnet18_l3_b2_w2 resnet18_l3_b2_b2
    resnet18_l3_b2_bn1_mean resnet18_l3_b2_bn1_var resnet18_l3_b2_bn1_gamma resnet18_l3_b2_bn1_beta
    resnet18_l3_b2_bn2_mean resnet18_l3_b2_bn2_var resnet18_l3_b2_bn2_gamma resnet18_l3_b2_bn2_beta
    resnet18_eps
    resnet18_l3_b2_conv1_out resnet18_l3_b2_bn1_out resnet18_l3_b2_relu1_out
    resnet18_l3_b2_conv2_out resnet18_l3_b2_bn2_out resnet18_l3_b2_add_out
    "l3_b2_conv1_out" "l3_b2_bn1_out" "l3_b2_relu1_out" "l3_b2_conv2_out" "l3_b2_bn2_out" "l3_b2_add_out" ';

  @ResNet_BB_proj_par_comm 1 256 512 14
    (vrd "l3_b2_add_out")
    resnet18_l4_b1_w1 resnet18_l4_b1_b1 resnet18_l4_b1_w2 resnet18_l4_b1_b2
    resnet18_l4_b1_bn1_mean resnet18_l4_b1_bn1_var resnet18_l4_b1_bn1_gamma resnet18_l4_b1_bn1_beta
    resnet18_l4_b1_bn2_mean resnet18_l4_b1_bn2_var resnet18_l4_b1_bn2_gamma resnet18_l4_b1_bn2_beta
    resnet18_eps
    resnet18_l4_b1_conv1_out resnet18_l4_b1_bn1_out resnet18_l4_b1_relu1_out
    resnet18_l4_b1_conv2_out resnet18_l4_b1_bn2_out resnet18_l4_b1_add_out
    resnet18_l4_b1_shortcut_out
    resnet18_l4_b1_shortcut_w resnet18_l4_b1_shortcut_b
    resnet18_l4_b1_shortcut_mean resnet18_l4_b1_shortcut_var
    resnet18_l4_b1_shortcut_gamma resnet18_l4_b1_shortcut_beta
    "l4_b1_shortcut_out" "l4_b1_conv1_out" "l4_b1_bn1_out" "l4_b1_relu1_out"
    "l4_b1_conv2_out" "l4_b1_bn2_out" "l4_b1_add_out" ';

  @ResNet_BB_id_par_comm 1 512 7
    (vrd "l4_b1_add_out")
    resnet18_l4_b2_w1 resnet18_l4_b2_b1 resnet18_l4_b2_w2 resnet18_l4_b2_b2
    resnet18_l4_b2_bn1_mean resnet18_l4_b2_bn1_var resnet18_l4_b2_bn1_gamma resnet18_l4_b2_bn1_beta
    resnet18_l4_b2_bn2_mean resnet18_l4_b2_bn2_var resnet18_l4_b2_bn2_gamma resnet18_l4_b2_bn2_beta
    resnet18_eps
    resnet18_l4_b2_conv1_out resnet18_l4_b2_bn1_out resnet18_l4_b2_relu1_out
    resnet18_l4_b2_conv2_out resnet18_l4_b2_bn2_out resnet18_l4_b2_add_out
    "l4_b2_conv1_out" "l4_b2_bn1_out" "l4_b2_relu1_out" "l4_b2_conv2_out" "l4_b2_bn2_out" "l4_b2_add_out" ';

  @GlobalAvgPool4d_par_comm 1 512 7 7 (vrd "l4_b2_add_out") resnet18_avgpool_out ';
  @Linear2d_par_comm 1 512 1000 resnet18_fc_w resnet18_fc_b (vrd "avgpool_out") resnet18_output.

(* -------------------- Correctness: par = seq -------------------- *)

(* Each layer is eval-equal to its sequential counterpart BY CONVERSION:
   [eval_aux] interprets both [CG.parfor] and [CG.seqfor] as [PCG.seqfor]
   (see the analogous discussion in [LeNet5_Par]).  The equalities are proved
   PER LAYER / PER BLOCK: a single whole-net [reflexivity] makes the
   conversion machinery iota-expand every concrete [PCG.seqfor] and does not
   terminate in practice. *)

Lemma conv4d_p1_k3_par_eval : forall batch inch outch m input w bias output rho,
  eval (@Conv4d_p1_k3_par_comm batch inch outch m input w bias output) rho =
  eval (@Conv4d_p1_k3_comm batch inch outch m input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma conv4d_p1_k3_s2_par_eval : forall batch inch outch m input w bias output rho,
  eval (@Conv4d_p1_k3_s2_par_comm batch inch outch m input w bias output) rho =
  eval (@Conv4d_p1_k3_s2_comm batch inch outch m input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma conv4d_p0_k1_s2_par_eval : forall batch inch outch m input w bias output rho,
  eval (@Conv4d_p0_k1_s2_par_comm batch inch outch m input w bias output) rho =
  eval (@Conv4d_p0_k1_s2_comm batch inch outch m input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma conv4d_p3_k7_s2_par_eval : forall batch inch outch m input w bias output rho,
  eval (@Conv4d_p3_k7_s2_par_comm batch inch outch m input w bias output) rho =
  eval (@Conv4d_p3_k7_s2_comm batch inch outch m input w bias output) rho.
Proof. intros. reflexivity. Qed.

Lemma batchnorm4d_par_eval : forall batch channel n1 n2 input mean var gamma beta eps output rho,
  eval (@BatchNorm4d_par_comm batch channel n1 n2 input mean var gamma beta eps output) rho =
  eval (@BatchNorm4d_comm batch channel n1 n2 input mean var gamma beta eps output) rho.
Proof. intros. reflexivity. Qed.

Lemma relu4d_par_eval : forall batch filernum m1 m2 input output rho,
  eval (@ReLU4d_par_comm batch filernum m1 m2 input output) rho =
  eval (@ReLU4d_comm batch filernum m1 m2 input output) rho.
Proof. intros. reflexivity. Qed.

Lemma add4d_par_eval : forall batch channel n1 n2 x y output rho,
  eval (@Add4d_par_comm batch channel n1 n2 x y output) rho =
  eval (@Add4d_comm batch channel n1 n2 x y output) rho.
Proof. intros. reflexivity. Qed.

Lemma maxpool4d_pad_par_eval : forall batch channel m k s p input output rho,
  eval (@MaxPool4d_pad_par_comm batch channel m k s p input output) rho =
  eval (@MaxPool4d_pad_comm batch channel m k s p input output) rho.
Proof. intros. reflexivity. Qed.

Lemma globalavgpool4d_par_eval : forall batch channel m1 m2 input output rho,
  eval (@GlobalAvgPool4d_par_comm batch channel m1 m2 input output) rho =
  eval (@GlobalAvgPool4d_comm batch channel m1 m2 input output) rho.
Proof. intros. reflexivity. Qed.

Lemma linear2d_par_eval : forall batch m outnum w b input output rho,
  eval (@Linear2d_par_comm batch m outnum w b input output) rho =
  eval (@Linear2d_comm batch m outnum w b input output) rho.
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

(* Block-level equalities: the 7 (resp. 9) layers of a BasicBlock composed
   with [eval_seq_congr]. *)
Lemma bb_id_par_eval : forall batch ch m input w1 b1 w2 b2
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out add_out
    conv1_s bn1_s relu1_s conv2_s bn2_s add_s rho,
  eval (@ResNet_BB_id_par_comm batch ch m input w1 b1 w2 b2
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out add_out
    conv1_s bn1_s relu1_s conv2_s bn2_s add_s) rho =
  eval (@ResNet_BB_id_comm batch ch m input w1 b1 w2 b2
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out add_out
    conv1_s bn1_s relu1_s conv2_s bn2_s add_s) rho.
Proof.
  intros. unfold ResNet_BB_id_par_comm, ResNet_BB_id_comm.
  apply eval_seq_congr; [ intros r; apply conv4d_p1_k3_par_eval |].
  intros r. apply eval_seq_congr; [ intros r0; apply batchnorm4d_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply relu4d_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply conv4d_p1_k3_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply batchnorm4d_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply add4d_par_eval |].
  intros r4. apply relu4d_par_eval.
Qed.

Lemma bb_proj_par_eval : forall batch inch outch m input w1 b1 w2 b2
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out add_out
    shortcut_out shortcut_w shortcut_b
    shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s add_s rho,
  eval (@ResNet_BB_proj_par_comm batch inch outch m input w1 b1 w2 b2
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out add_out
    shortcut_out shortcut_w shortcut_b
    shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s add_s) rho =
  eval (@ResNet_BB_proj_comm batch inch outch m input w1 b1 w2 b2
    mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps
    conv1_out bn1_out relu1_out conv2_out bn2_out add_out
    shortcut_out shortcut_w shortcut_b
    shortcut_mean shortcut_var shortcut_gamma shortcut_beta
    shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s add_s) rho.
Proof.
  intros. unfold ResNet_BB_proj_par_comm, ResNet_BB_proj_comm.
  apply eval_seq_congr; [ intros r; apply conv4d_p0_k1_s2_par_eval |].
  intros r. apply eval_seq_congr; [ intros r0; apply batchnorm4d_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply conv4d_p1_k3_s2_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply batchnorm4d_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply relu4d_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply conv4d_p1_k3_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; apply batchnorm4d_par_eval |].
  intros r5. apply eval_seq_congr; [ intros r6; apply add4d_par_eval |].
  intros r6. apply relu4d_par_eval.
Qed.

(* The parallel net has the same denotation as the sequential net, hence the
   [Bridge_ResNet18] chain to route A ([ResNet18_DPIA.A_ResNet18], BatchNorm
   bridge at batch = 1) applies to it. *)
Theorem resnet18_par_eval_eq : forall rho,
  eval resnet18_par_comm rho = eval resnet18_comm rho.
Proof.
  intros rho. unfold resnet18_par_comm, resnet18_comm.
  apply eval_seq_congr; [ intros r; apply conv4d_p3_k7_s2_par_eval |].
  intros r. apply eval_seq_congr; [ intros r0; apply batchnorm4d_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply relu4d_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply maxpool4d_pad_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; apply bb_id_par_eval |].
  intros r3. apply eval_seq_congr; [ intros r4; apply bb_id_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; apply bb_proj_par_eval |].
  intros r5. apply eval_seq_congr; [ intros r6; apply bb_id_par_eval |].
  intros r6. apply eval_seq_congr; [ intros r7; apply bb_proj_par_eval |].
  intros r7. apply eval_seq_congr; [ intros r8; apply bb_id_par_eval |].
  intros r8. apply eval_seq_congr; [ intros r9; apply bb_proj_par_eval |].
  intros r9. apply eval_seq_congr; [ intros r10; apply bb_id_par_eval |].
  intros r10. apply eval_seq_congr; [ intros r11; apply globalavgpool4d_par_eval |].
  intros r11. apply linear2d_par_eval.
Qed.

(* -------------------- Extraction for the streaming printer -------------------- *)

Extraction "resnet18_par_comm.ml" resnet18_par_comm.
Extraction "resnet18_seq_comm.ml" resnet18_comm.
