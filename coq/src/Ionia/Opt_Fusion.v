(* G0 优化规则层：融合（fusion）规则（路线 A / DPIA 规则层）。

   在 Ionia.DPIA_Rules 的语义模型（comm := env -> env，
   env := path -> option (exp num)）上建立三类融合重写规则，全部为
   Leibniz 等式或观察点等式，全部 Qed 收尾，仅依赖标准经典公理
   （functional extensionality / proof irrelevance / classic）。

   1. map 融合（最一般形式）：逐元素生产者-消费者缓冲消除 [map_fusion]
      —— 先 mkvSeql 把 f 写进临时缓冲、再逐元素 bind_read 读回经 g 改写
      输出的两段式命令，在临时缓冲新鲜（StructUndefined）、输出与缓冲路径
      不相交、且只观察输出路径（in_acc p a）时，等价于直接
      A(a, mkvSeq (fun i => g (f i)))。
      关键引理：
      - [read_exp_mkvSeql]：生产者循环结束后读第 i 格恰得 f i
        （经 Proof_CodeGen.access_seqfor_ary_eq_general，即
         LeNet5_DPIA.bind_read_replace 赖以成立的 access_assign 族的
         seqfor 推广）；
      - [consumer_fusion]：消费者循环内的 bind_read 逐格替换为直接值
        （bind_read_replace 族的循环级推广）；
      - [access_assign_disjoint] / [seqfor_read_exp_stable]：
        消费者写输出不污染临时缓冲的读（不相交性前提显式）。
   2. Conv4d + ReLU4d 融合（应用级，路线 A 算子）：
      [A_Conv4d_ReLU4d]：A(output, ReLU4d (Conv4d p s bias w input))
        = ConvReLU4d_fused_comm p s bias w input output，
      融合核把 ReLU 内联进卷积输出赋值（suml 归约的续延里带 if 分支），
      消除中间特征图缓冲；
      [Conv4d_ReLU4d_buffer_elim] / [Conv4d_ReLU4d_comm_buffer_elim]：
      "写临时缓冲 + bind_read 读改写"的两段式 = 融合核。
   3. mkvSeq 链融合一般规则：[mkvSeq_chain_fusion] / [A_mkvSeq_chain]
      —— 连续两次逐元素变换 = 一次复合变换。
   加分项：[lenet5_conv1_relu1_fusion] —— LeNet-5 conv1+relu1 片段
      融合前后的等式（Conv3d_comm 写临时缓冲 + bind_read + ReLU3d_comm
      ≡ 值传递直写 A(output, ReLU3d (Conv3d ...))）。

   注：本文件 Require 了 LeNet5_Functional（其 LeNet5_Utils 把 "|" 注册为
   关键字，会破坏 [| ] / [|{ }] 记号的解析），因此全文按
   Ops_Elementwise / Ops_Conv 的约定使用显式 idx / idxAcc。 *)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Eqdep_dec.
Require Import Coq.Logic.Classical_Prop.
Import ListNotations.

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
Require Import Ionia.Ops_Elementwise.
Require Import Ionia.Ops_Conv.
From Stdlib Require Import Lia.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* 1. mkvSeq 链融合（函数层）：连续两次逐元素变换 = 一次复合变换                  *)
(* -------------------------------------------------------------------------- *)

(* 先造 mkvSeq f 再逐元素读回施加 g，与一次复合 mkvSeq (g ∘ f) 相等。 *)
Lemma mkvSeq_chain_fusion : forall (n:nat) (d:data)
    (f : fin n -> exp d) (g : exp d -> exp d),
  mkvSeq (fun i => g (idx (mkvSeq f) i)) = mkvSeq (fun i => g (f i)).
Proof.
  intros n d f g. f_equal.
  apply functional_extensionality. intro i.
  destruct n.
  - inversion i; lia.
  - f_equal. rewrite idx_mkvSeq by lia. reflexivity.
Qed.

(* A-规则形式：可直接作为 rewrite 规则使用。 *)
Lemma A_mkvSeq_chain : forall (n:nat) (d:data)
    (f : fin n -> exp d) (g : exp d -> exp d) (a : acc (ary '{n} d)),
  A(a, mkvSeq (fun i => g (idx (mkvSeq f) i))) = A(a, mkvSeq (fun i => g (f i))).
Proof.
  intros. rewrite mkvSeq_chain_fusion. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2. map 融合：逐元素生产者-消费者缓冲消除                                      *)
(* -------------------------------------------------------------------------- *)

(* 向不相交的累加器 b 写入，不改变对 c 的读取（access 层级）。
   这是 assign_not_in_acc 的 access 推广。 *)
Lemma access_assign_disjoint : forall (d2:data) (c : acc d2) (d1:data) (b : acc d1)
    (e : exp d1) (rho : env),
  (forall q, in_acc q b -> ~ in_acc q c) ->
  access (assign b e rho) c = access rho c.
Proof.
  intros d2; induction d2 as [| n0 m d2' IHd]; intros c d1 b e rho Hdisj.
  - rewrite !access_num. apply assign_not_in_acc. intro Hc.
    exact (Hdisj c Hc eq_refl).
  - rewrite !access_ary. apply mkoptvec_dependence. intro i.
    apply IHd. intros q Hb Hci.
    exact (Hdisj q Hb (ex_intro _ i Hci)).
Qed.

(* read_exp 是 access 的缺省包装：access 相等则 read_exp 相等。
   注意 read_exp 是对 d 结构递归的 fixpoint，一般 d 下 fix 不约，
   必须按 d 分情形后才能 unfold。 *)
Lemma read_exp_congr : forall (d:data) (rho1 rho2 : env) (a : acc d),
  access rho1 a = access rho2 a -> read_exp rho1 a = read_exp rho2 a.
Proof.
  intros d; destruct d; intros rho1 rho2 a H; unfold read_exp; rewrite H; reflexivity.
Qed.

(* read_exp 层级的不相交写入保持。 *)
Lemma read_exp_assign_disjoint : forall (d2:data) (c : acc d2) (d1:data) (b : acc d1)
    (e : exp d1) (rho : env),
  (forall q, in_acc q b -> ~ in_acc q c) ->
  read_exp (assign b e rho) c = read_exp rho c.
Proof.
  intros d2 c d1 b e rho Hdisj.
  apply read_exp_congr. apply access_assign_disjoint. exact Hdisj.
Qed.

(* 若每步命令都不改变对 t 的读取，则整个 seqfor 也不改变。 *)
Lemma seqfor_read_exp_stable : forall (m:nat) (c : fin m -> comm) (d:data)
    (t : acc d) (rho : env),
  (forall i rho', read_exp (c i rho') t = read_exp rho' t) ->
  read_exp (seqfor c rho) t = read_exp rho t.
Proof.
  intros m; induction m as [| m' IHm]; intros c d t rho H.
  - reflexivity.
  - rewrite seqfor_Sn. unfold seq.
    rewrite H. apply IHm. intros i rho'. apply H.
Qed.

(* read_exp 是 access 的缺省包装：access 命中 Some 时读回即得。 *)
Lemma read_exp_of_access : forall (d:data) (rho : env) (a : acc d) (e : exp d),
  access rho a = Some e -> read_exp rho a = e.
Proof.
  intros d; destruct d; intros rho a e H; unfold read_exp; rewrite H; reflexivity.
Qed.

(* 生产者循环（mkvSeql 把 f 逐格写进以 p 为根的临时缓冲）结束后，
   读第 i 格恰得 f i。
   这是 bind_read_replace（LeNet5_DPIA:274）赖以成立的 read_exp_assign 的
   循环级推广：核心由 access_seqfor_ary_eq_general（Proof_CodeGen）给出。 *)
Lemma read_exp_mkvSeql : forall (n:nat) (d:data) (f : fin n -> exp d)
    (p : path) (rho : env) (i : fin n),
  n > 0 ->
  read_exp (mkvSeql (fun j o => A(o, f j)) (@acc' (ary '{n} d) p) rho)
           (idxAcc (@acc' (ary '{n} d) p) i)
  = f i.
Proof.
  intros n d f p rho i Hn. apply read_exp_of_access.
  replace (idxAcc (@acc' (ary '{n} d) p) i) with (@acc' d (AryIdx i p)).
  2: { unfold idxAcc. rewrite acc'_ary. rewrite v_idx_mk_vec. reflexivity. }
  unfold mkvSeql, A. cbv beta iota.
  assert (Hprod : seqfor (fun j : fin n => assign (idxAcc (@acc' (ary '{n} d) p) j) (f j))
                = seqfor (fun j : fin n => assign (@acc' d (AryIdx j p)) (idx (mkvSeq f) j))).
  { apply seqfor_extensionality. intro j. cbv beta iota.
    unfold idxAcc. rewrite acc'_ary. rewrite v_idx_mk_vec.
    rewrite idx_mkvSeq by lia. reflexivity. }
  rewrite Hprod.
  replace (f i) with (idx (mkvSeq f) i).
  2: { apply idx_mkvSeq. exact Hn. }
  apply (@access_seqfor_ary_eq_general d p rho n n (fun j : fin n => j) (mkvSeq f)).
  - intros j k Hjk. exact Hjk.
  - intros p1 p2 e' x' H12. apply access_assign_neq. exact H12.
  - intros p1 e' x'. apply access_assign_eq. reflexivity.
Qed.

(* 消费者循环融合：若读侧第 i 格在 rho 中已是 f i，且写侧每格与读侧每格
   路径不相交，则"逐格 bind_read 读回再经 g 改写"的循环等价于直接写
   g (f i) 的循环。 这是 bind_read_replace 族的循环级推广。 *)
Lemma consumer_fusion : forall (n:nat) (d:data)
    (f : fin n -> exp d) (g : exp d -> exp d)
    (tacc wacc : fin n -> acc d) (rho : env),
  (forall i, read_exp rho (tacc i) = f i) ->
  (forall i j q, in_acc q (wacc i) -> ~ in_acc q (tacc j)) ->
  seqfor (fun i => bind_read (tacc i) (fun v => wacc i |:= g v)) rho
  = seqfor (fun i => wacc i |:= g (f i)) rho.
Proof.
  intros n; induction n as [| n' IHn]; intros d f g tacc wacc rho Hread Hdisj.
  - reflexivity.
  - rewrite !seqfor_Sn. cbv beta. unfold seq.
    assert (HIH : seqfor (fun i : fin n' => bind_read (tacc FS[i]) (fun v => wacc FS[i] |:= g v)) rho
                = seqfor (fun i : fin n' => wacc FS[i] |:= g (f FS[i])) rho).
    { apply (IHn d (fun i => f FS[i]) g (fun i => tacc FS[i]) (fun i => wacc FS[i]) rho).
      - intro i. apply Hread.
      - intros i j q Hw Hc. exact (Hdisj FS[i] FS[j] q Hw Hc). }
    rewrite HIH.
    unfold bind_read. cbv beta.
    assert (Hst : read_exp (seqfor (fun i : fin n' => wacc FS[i] |:= g (f FS[i])) rho) (tacc '[n'])
                = read_exp rho (tacc '[n'])).
    { apply seqfor_read_exp_stable. intros i rho'. cbv beta.
      apply read_exp_assign_disjoint.
      intros q Hw Hc. exact (Hdisj FS[i] '[n'] q Hw Hc). }
    rewrite Hst. rewrite (Hread '[n']). reflexivity.
Qed.

(* map 融合的命令等式（共享生产者前缀形式）：
   两段式 = 写 g (f i) 的直接循环。 *)
Lemma map_fusion_seq : forall (n:nat) (d:data)
    (f : fin n -> exp d) (g : exp d -> exp d)
    (tmp_path : path) (a : acc (ary '{n} d)),
  n > 0 ->
  (forall q, in_acc q a -> ~ in_acc q (@acc' (ary '{n} d) tmp_path)) ->
  seq (mkvSeql (fun i o => A(o, f i)) (@acc' (ary '{n} d) tmp_path))
      (seqfor (fun i => bind_read (idxAcc (@acc' (ary '{n} d) tmp_path) i)
                              (fun v => idxAcc a i |:= g v)))
  = seq (mkvSeql (fun i o => A(o, f i)) (@acc' (ary '{n} d) tmp_path))
        (mkvSeql (fun i o => A(o, g (f i))) a).
Proof.
  intros n d f g tmp_path a Hn Hdisj.
  apply functional_extensionality. intro rho. unfold seq.
  assert (Hcons :
    seqfor (fun i : fin n => bind_read (idxAcc (@acc' (ary '{n} d) tmp_path) i)
                               (fun v => idxAcc a i |:= g v))
           (mkvSeql (fun i o => A(o, f i)) (@acc' (ary '{n} d) tmp_path) rho)
    = seqfor (fun i : fin n => idxAcc a i |:= g (f i))
             (mkvSeql (fun i o => A(o, f i)) (@acc' (ary '{n} d) tmp_path) rho)).
  { apply (@consumer_fusion n d f g
             (fun i => idxAcc (@acc' (ary '{n} d) tmp_path) i)
             (fun i => idxAcc a i)).
    - intro i. apply (@read_exp_mkvSeql n d f tmp_path rho i Hn).
    - intros i j q Hw Hc. apply (Hdisj q).
      + exists i. exact Hw.
      + exists j. exact Hc. }
  rewrite Hcons. reflexivity.
Qed.

(* map 融合规则（最一般形式）：带 new 的两段式程序，在临时缓冲新鲜、
   输出与缓冲路径不相交、只观察输出路径 p 的前提下，等价于
   A(a, mkvSeq (fun i => g (f i)))。
   注：由于只观察输出路径，assign_pure_independent 直接给出结论；
   StructUndefined（freshness）前提按课题要求显式保留——观察整个环境
   或做 new 清理时需要它。 *)
Theorem map_fusion : forall (n:nat) (d:data)
    (f : fin n -> exp d) (g : exp d -> exp d)
    (tmp_path : path) (a : acc (ary '{n} d)) (rho : env) (p : path),
  n > 0 ->
  in_acc p a ->
  @StructUndefined (ary '{n} d) (@acc' (ary '{n} d) tmp_path) rho ->
  (forall q, in_acc q a -> ~ in_acc q (@acc' (ary '{n} d) tmp_path)) ->
  new (fun tmp : acc (ary '{n} d) =>
        seq (mkvSeql (fun i o => A(o, f i)) tmp)
            (seqfor (fun i => bind_read (idxAcc tmp i)
                              (fun v => idxAcc a i |:= g v))))
      (@acc' (ary '{n} d) tmp_path) rho p
  = A(a, mkvSeq (fun i => g (f i))) rho p.
Proof.
  intros n d f g tmp_path a rho p Hn Hp Hfresh Hdisj.
  unfold new. cbv beta.
  rewrite (@map_fusion_seq n d f g tmp_path a Hn Hdisj).
  rewrite <- (@AmkvSeq n d (fun i : fin n => g (f i)) a).
  unfold seq, A. apply assign_pure_independent. exact Hp.
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. Conv4d + ReLU4d 融合（路线 A 应用级）                                       *)
(* -------------------------------------------------------------------------- *)

(* 融合核的逐输出格命令：suml 归约的续延里直接带 ReLU 分支，
   卷积结果不再写进中间特征图缓冲。 *)
Definition ConvReLU4dCell_comm {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (b : fin batch)
  (cout : fin filernum)
  (i0 : fin ((m1 - n1 + 2 * p) / s + 1))
  (j0 : fin ((m2 - n2 + 2 * p) / s + 1))
  (output_cell : acc num)
  : comm :=
  suml (mkvSeq (fun c : fin channel =>
        sum (mkvSeq (fun i1 : fin n1 =>
          sum (mkvSeq (fun j1 : fin n2 =>
            mul (pad_idx2d p (idx (idx input b) c)
                           (fin2nat i0 * s + fin2nat i1)
                           (fin2nat j0 * s + fin2nat j1))
                (idx (idx (idx (idx w cout) c) i1) j1)))))))
       (fun r : exp num =>
          output_cell |:= (if leExp (add r (idx bias cout)) zero
                             then zero
                             else add r (idx bias cout)))
       output_cell.

Definition ConvReLU4d_fused_comm {batch m1 m2 n1 n2 channel filernum : nat} (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  : comm :=
  mkvSeql (fun b ob => mkvSeql (fun cout oc =>
    mkvSeql (fun i0 o0 => mkvSeql (fun j0 o1 =>
      ConvReLU4dCell_comm p s bias w input b cout i0 j0 o1) o0) oc) ob) output.

(* 标量层关键引理：relu (sum + bias) 的直接赋值 = suml 归约骨架 + 末尾续延里
   做 relu。 因为 C(sum xs, c) 定义上就是 c (sum xs)，直接走
   DPIA_Rules.C_sum_post_acc。 *)
Lemma A_relu_add_sum : forall (n:nat) (xs : exp (ary '{n} num)) (bc : exp num)
    (a : acc num),
  A(a, if leExp (add (sum xs) bc) zero then zero else add (sum xs) bc)
  = suml xs (fun r : exp num =>
      a |:= (if leExp (add r bc) zero then zero else add r bc)) a.
Proof.
  intros n xs bc a.
  change (A(a, if leExp (add (sum xs) bc) zero then zero else add (sum xs) bc))
    with (C(sum xs, fun r : exp num =>
            a |:= (if leExp (add r bc) zero then zero else add r bc))).
  apply C_sum_post_acc.
Qed.

(* 应用级融合规则：ReLU4d ∘ Conv4d 的直接赋值 = 融合核命令。
   证明形态照 Ops_Conv.A_Conv4d：AmkvSeq×4 + seqfor_extensionality 下钻到
   输出格，idx_mkvSeq×4 把 Conv4d 的 mkvSeq 链展开成 Conv4dCell，
   末尾用 A_relu_add_sum 把 relu 内联进 suml 续延。 *)
Theorem A_Conv4d_ReLU4d : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hb : batch > 0) (Hf : filernum > 0)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num))))),
  A(output, ReLU4d (Conv4d p s bias w input))
  = ConvReLU4d_fused_comm p s bias w input output.
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s Hb Hf bias w input output.
  unfold ReLU4d, ConvReLU4d_fused_comm, ConvReLU4dCell_comm, Conv4d.
  rewrite AmkvSeq. apply seqfor_extensionality. intro b.
  rewrite AmkvSeq. apply seqfor_extensionality. intro cout.
  rewrite AmkvSeq. apply seqfor_extensionality. intro i0.
  rewrite AmkvSeq. apply seqfor_extensionality. intro j0.
  cbv beta.
  rewrite !idx_mkvSeq by lia.
  unfold Conv4dCell.
  rewrite A_relu_add_sum. reflexivity.
Qed.

(* 两段式（A 写临时缓冲 + bind_read 读回再 A-ReLU4d）= 融合核：
   bind_read_replace 把读替换为值传递，再用应用级规则。 *)
Theorem Conv4d_ReLU4d_buffer_elim : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hb : batch > 0) (Hf : filernum > 0)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  (tmp_path : path),
  seq (A(@acc' (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) tmp_path,
        Conv4d p s bias w input))
      (bind_read (@acc' (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) tmp_path)
                 (fun e => A(output, ReLU4d e)))
  = seq (A(@acc' (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) tmp_path,
        Conv4d p s bias w input))
        (ConvReLU4d_fused_comm p s bias w input output).
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s Hb Hf bias w input output tmp_path.
  rewrite bind_read_replace.
  rewrite A_Conv4d_ReLU4d by assumption.
  reflexivity.
Qed.

(* 生成代码形态的两段式（Conv4d_comm 写缓冲 + bind_read + ReLU4d_comm 读改写）
   = 融合核：先借 A_Conv4d 折回 A 形式，再值传递替换，再内联 ReLU。 *)
Theorem Conv4d_ReLU4d_comm_buffer_elim : forall (batch m1 m2 n1 n2 channel filernum p s : nat)
  (Hb : batch > 0) (Hf : filernum > 0)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))))
  (tmp_path : path),
  seq (Conv4d_comm p s bias w input
        (@acc' (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) tmp_path))
      (bind_read (@acc' (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) tmp_path)
                 (fun e => ReLU4d_comm e output))
  = seq (Conv4d_comm p s bias w input
          (@acc' (ary '{batch} (ary '{filernum}
                (ary '{((m1 - n1 + 2 * p) / s + 1)}
                 (ary '{((m2 - n2 + 2 * p) / s + 1)} num)))) tmp_path))
        (ConvReLU4d_fused_comm p s bias w input output).
Proof.
  intros batch m1 m2 n1 n2 channel filernum p s Hb Hf bias w input output tmp_path.
  rewrite <- A_Conv4d. rewrite bind_read_replace. rewrite <- A_ReLU4d.
  rewrite A_Conv4d_ReLU4d by assumption. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. 加分项：LeNet-5 conv1+relu1 片段的融合前后等式                              *)
(* -------------------------------------------------------------------------- *)

(* 融合前：Conv3d_comm 写临时特征图缓冲，bind_read 读回后 ReLU3d_comm 写输出；
   融合后：卷积结果直接值传递（值语义下的"内联"），等式右侧正是
   lenet5_comm 第一层经 bind_read_replace 后的 DPIA 范式。 *)
Example lenet5_conv1_relu1_fusion : forall
  (input : exp (ary '{1} (ary '{28} (ary '{28} num))))
  (c1_w : exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))))
  (c1_b : exp (ary '{6} num))
  (tmp_path : path)
  (output : acc (ary '{6} (ary '{28} (ary '{28} num)))),
  seq (Conv3d_comm (p:=2) H5 c1_w c1_b input
        (@acc' (ary '{6} (ary '{28} (ary '{28} num))) tmp_path))
      (bind_read (@acc' (ary '{6} (ary '{28} (ary '{28} num))) tmp_path)
                 (fun e => ReLU3d_comm e output))
  = seq (A(@acc' (ary '{6} (ary '{28} (ary '{28} num))) tmp_path,
           Conv3d (p:=2) H5 c1_w c1_b input))
        (A(output, ReLU3d (Conv3d (p:=2) H5 c1_w c1_b input))).
Proof.
  intros. rewrite <- A_Conv3d. rewrite bind_read_replace. rewrite <- A_ReLU3d.
  reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions mkvSeq_chain_fusion.
Print Assumptions A_mkvSeq_chain.
Print Assumptions map_fusion.
Print Assumptions A_Conv4d_ReLU4d.
Print Assumptions Conv4d_ReLU4d_buffer_elim.
Print Assumptions Conv4d_ReLU4d_comm_buffer_elim.
Print Assumptions lenet5_conv1_relu1_fusion.
