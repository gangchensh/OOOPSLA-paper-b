(* Core CNN operator imperative ASTs.

   This file contains the [*_comm] combinators for the operators whose semantic
   equivalence to the functional specifications is proved (or will be proved) in
   [Ionia.Operators_Sem_Equiv.v].  Splitting these definitions out of
   [Ionia.CNN_Examples_Base.v] removes the circular dependency that otherwise
   prevents [Operators_Sem_Equiv.v] from importing them.

   The definitions here use exactly the same notations and combinators as
   [CNN_Examples_Base.v]; downstream files can continue to import
   [CNN_Examples_Base.v], which re-exports this module. *)

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

(* -------------------- Linear1d -------------------- *)
Definition Linear1d_comm {m outnum} (w: exp (ary '{outnum} (ary '{m} num)))
  (b: exp (ary '{outnum} num)) (input: exp (ary '{m} num))
  (output: acc (ary '{outnum} num)) : comm :=
  seqfor (fun out =>
    @loopacc num (fun tmp =>
      let w_acc := vwt tmp in
      let v := vrd tmp in
      (w_acc |:= zero) ';
      seqfor (fun i => w_acc |:= add (mul input|[i] w|[out]|[i]) v) ';
      output|{out} |:= add v b|[out])).

(* The Leibniz equality for Linear1d is not a syntactic identity because the
   imperative code uses [loopacc] while the reference uses a functional sum.
   Its semantic equivalence is proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- Softmax1d -------------------- *)
Definition Softmax1d_comm {n} (input: exp (ary '{n} num)) (output: acc (ary '{n} num)) : comm :=
  @loopacc num (fun tmp =>
    let w := vwt tmp in
    let v := vrd tmp in
    (w |:= zero) ';
    seqfor (fun i => w |:= add (pExp (input|[i])) v) ';
    seqfor (fun j => output|{j} |:= div (pExp (input|[j])) v)).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- ReLU4d -------------------- *)
Definition ReLU4d_comm {batch filernum m1 m2}
  (input: exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))) : comm :=
  seqfor (fun b => seqfor (fun num => seqfor (fun i0 => seqfor (fun i1 =>
    If (leExp input|[b]|[num]|[i0]|[i1] zero)
      (output|{b}|{num}|{i0}|{i1} |:= zero,
       output|{b}|{num}|{i0}|{i1} |:= input|[b]|[num]|[i0]|[i1]))))).

(* The AST-level Leibniz theorem [ReLU4d_equiv] has been moved to
   [Ionia.legacy.CG_golden_tests] (outside the main build); the semantic
   equivalence is proved directly below as [ReLU4d_equiv_sem]. *)

(* Local copy of [CNN_Examples_Base.exp_independent_of_acc_weaken_ary]
   (this file is imported by [CNN_Examples_Base], so it cannot use that one). *)
Lemma exp_independent_of_acc_weaken_ary :
  forall n d d' (e : exp d') (a : acc (ary '{n} d)) (i : fin n),
    exp_independent_of_acc e a ->
    exp_independent_of_acc e (a |{ i}).
Proof.
  intros n d d' e a i Hin p Hp. apply Hin. apply in_acc_ary_inv with (i := i). exact Hp.
Qed.

Theorem ReLU4d_equiv_sem :
  forall batch filernum m1 m2
             (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
             (output : acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
             (rho : PCG.env),
    exp_independent_of_acc input output ->
    (forall b c i0 i1, DE.eval_bexp (fun s => match rho (DE.Var s) with Some r => r | None => R0 end)
                         (leExp input|[b]|[c]|[i0]|[i1] zero) = bexp2bool (leExp input|[b]|[c]|[i0]|[i1] zero)) ->
    eval (A(output, @ReLU4d batch m1 m2 filernum input)) rho =
    eval (@ReLU4d_comm batch filernum m1 m2 input output) rho.
Proof.
  intros batch filernum m1 m2 input output rho Hin Hbeq.
  (* The static/runtime branch agreement lifts to every environment that
     agrees with [rho] outside [output]. *)
  assert (Hbeq' : forall eta,
    (forall q, ~ @PCG.in_acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))) q output -> eta q = rho q) ->
    forall b c i0 i1, DE.eval_bexp (fun s => match eta (DE.Var s) with Some r => r | None => R0 end)
                        (leExp input|[b]|[c]|[i0]|[i1] zero) = bexp2bool (leExp input|[b]|[c]|[i0]|[i1] zero)).
  { intros eta Hagree b c i0 i1. rewrite <- (Hbeq b c i0 i1).
    apply bexp_independent_eval with (a := output).
    - intros p Hp.
      eapply bexp_leExp_zero_independent_of_acc with (a := output).
      + do 3 (apply exp_independent_of_acc_idx). exact Hin.
      + exact Hp.
    - exact Hagree. }
  unfold ReLU4d, ReLU4d_comm.
  rewrite AmkvSeq_sem.
  - unfold mkvSeql. rewrite !eval_seqfor.
    apply seqfor_pointwise_inv
      with (P := fun eta => forall q, ~ @PCG.in_acc (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))) q output -> eta q = rho q);
      [ | intros b eta HP; split ].
    + intros q Hq. reflexivity.
    + cbn beta. rewrite AmkvSeq_sem.
      * unfold mkvSeql. rewrite !eval_seqfor.
        apply seqfor_pointwise_inv
          with (P := fun eta2 => forall q, ~ @PCG.in_acc (ary '{filernum} (ary '{m1} (ary '{m2} num))) q (output|{b}) -> eta2 q = eta q);
          [ | intros c eta2 HP2; split ].
        -- intros q Hq. reflexivity.
        -- cbn beta. rewrite AmkvSeq_sem.
           ++ unfold mkvSeql. rewrite !eval_seqfor.
              apply seqfor_pointwise_inv
                with (P := fun eta3 => forall q, ~ @PCG.in_acc (ary '{m1} (ary '{m2} num)) q (output|{b}|{c}) -> eta3 q = eta2 q);
                [ | intros i0 eta3 HP3; split ].
              ** intros q Hq. reflexivity.
              ** cbn beta. rewrite AmkvSeq_sem.
                 --- unfold mkvSeql. rewrite !eval_seqfor.
                     apply seqfor_If_sem.
                     +++ intros i1 p Hp. cbn beta.
                         eapply bexp_leExp_zero_independent_of_acc with (a := (output|{b}|{c}|{i0})).
                         *** do 3 (apply exp_independent_of_acc_idx).
                             do 3 (apply exp_independent_of_acc_weaken_ary). exact Hin.
                         *** exact Hp.
                     +++ intro i1. apply Hbeq'.
                         intros q Hq. transitivity (eta2 q).
                         *** apply HP3. intro Hc2. apply Hq.
                             eapply in_acc_ary_inv. eapply in_acc_ary_inv. exact Hc2.
                         *** transitivity (eta q).
                             ---- apply HP2. intro Hc1. apply Hq.
                                  eapply in_acc_ary_inv. exact Hc1.
                             ---- apply HP. exact Hq.
                 --- intros i1. apply exp_independent_of_acc_if; intros _;
                     [ apply exp_independent_of_acc_zero
                     | do 4 (apply exp_independent_of_acc_idx);
                       do 3 (apply exp_independent_of_acc_weaken_ary); exact Hin ].
              ** intros q Hq. cbn beta. transitivity (eta3 q).
                 --- apply eval_assign_idx_modifies_only. exact Hq.
                 --- apply HP3. exact Hq.
           ++ intros i0. apply exp_independent_of_acc_mkvSeq. intros i1.
              apply exp_independent_of_acc_if; intros _;
                [ apply exp_independent_of_acc_zero
                | do 4 (apply exp_independent_of_acc_idx);
                  do 2 (apply exp_independent_of_acc_weaken_ary); exact Hin ].
        -- intros q Hq. cbn beta. transitivity (eta2 q).
           ++ apply eval_assign_idx_modifies_only. exact Hq.
           ++ apply HP2. exact Hq.
      * intros c. apply exp_independent_of_acc_mkvSeq. intros i0.
        apply exp_independent_of_acc_mkvSeq. intros i1.
        apply exp_independent_of_acc_if; intros _;
          [ apply exp_independent_of_acc_zero
          | do 4 (apply exp_independent_of_acc_idx);
            apply exp_independent_of_acc_weaken_ary; exact Hin ].
    + intros q Hq. cbn beta. transitivity (eta q).
      * apply eval_assign_idx_modifies_only. exact Hq.
      * apply HP. exact Hq.
  - intros b. apply exp_independent_of_acc_mkvSeq. intros c.
    apply exp_independent_of_acc_mkvSeq. intros i0. apply exp_independent_of_acc_mkvSeq. intros i1.
    apply exp_independent_of_acc_if; intros _;
      [ apply exp_independent_of_acc_zero
      | do 4 (apply exp_independent_of_acc_idx); exact Hin ].
Qed.

(* -------------------- Linear2d -------------------- *)
Definition Linear2d_comm {batch m outnum}
  (w: exp (ary '{outnum} (ary '{m} num)))
  (b: exp (ary '{outnum} num))
  (input: exp (ary '{batch} (ary '{m} num)))
  (output: acc (ary '{batch} (ary '{outnum} num))) : comm :=
  seqfor (fun bi: fin batch => seqfor (fun out: fin outnum =>
    @loopacc num (fun tmp =>
      let w_acc := vwt tmp in
      let v := vrd tmp in
      (w_acc |:= zero) ';
      seqfor (fun i => w_acc |:= add (mul input|[bi]|[i] w|[out]|[i]) v) ';
      output|{bi}|{out} |:= add v b|[out]))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- Softmax2d -------------------- *)
Definition Softmax2d_comm {batch m}
  (input: exp (ary '{batch} (ary '{m} num)))
  (output: acc (ary '{batch} (ary '{m} num))) : comm :=
  seqfor (fun bi: fin batch =>
    @loopacc num (fun tmp =>
      let w := vwt tmp in
      let v := vrd tmp in
      (w |:= zero) ';
      seqfor (fun i => w |:= add (pExp (input|[bi]|[i])) v) ';
      seqfor (fun j => output|{bi}|{j} |:= div (pExp (input|[bi]|[j])) v))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- Log_Softmax2d -------------------- *)
Definition Log_Softmax2d_comm {batch m}
  (input: exp (ary '{batch} (ary '{m} num)))
  (output: acc (ary '{batch} (ary '{m} num))) : comm :=
  seqfor (fun bi: fin batch =>
    @loopacc num (fun tmp =>
      let w := vwt tmp in
      let v := vrd tmp in
      (w |:= zero) ';
      seqfor (fun i => w |:= add (pExp (input|[bi]|[i])) v) ';
      seqfor (fun j => output|{bi}|{j} |:= (log (div (pExp (input|[bi]|[j])) v))))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- GlobalAvgPool4d -------------------- *)
(* Global average pooling over spatial dimensions.
   The two nested sums are flattened into a single loop over m1*m2; this
   avoids a nested [loopacc] and matches the semantic-combinator machinery. *)
Definition GlobalAvgPool4d_comm {batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (output: acc (ary '{batch} (ary '{channel} num))) : comm :=
  seqfor (fun b => seqfor (fun c =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      acc_a |:= zero ';
      seqfor (fun k : fin (m1 * m2) =>
        let i := Nat.div (fin2nat k) m2 in
        let j := Nat.modulo (fin2nat k) m2 in
        acc_a |:= add (safe_idx_nat (safe_idx_nat input|[b]|[c] i) j) acc_v
      ) ';
      output|{b}|{c} |:= div_n acc_v (m1 * m2)
    )
  )).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- Maxpool2d / Avgpool2d / Maxpool3d / Maxpool4d ------- *)
(* Generic loopacc-based imperative forms of the pooling operators.  Unlike
   the concrete [new]-based comms in [CNN_Examples_Base.v] /
   [CNN_Examples_LeNet5.v] / [CNN_Examples_MiniAlexNet.v] (which are
   code-generation artifacts: under [eval_aux] the value placeholder of [new]
   is instantiated with the initialisation expression, so their [eval] does
   not model the accumulator), these use [loopacc] with a genuine accumulator
   read [vrd tmp], so their [eval] semantics matches the generated C code.
   The k x k window is flattened into a single loop over [k * k], mirroring
   [GlobalAvgPool4d_comm].  The accumulator starts at [zero], matching the
   zero-based functional [CD.max]/[CD.sum]. *)

Definition Maxpool2d_comm {m1 m2 : nat} (k : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{(m1/k)} (ary '{(m2/k)} num))) : comm :=
  seqfor (fun i0 : fin (m1/k) => seqfor (fun j0 : fin (m2/k) =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      acc_a |:= zero ';
      seqfor (fun kk : fin (k * k) =>
        If (gtExp (safe_idx_nat (safe_idx_nat input
                     (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                     (fin2nat j0 * k + Nat.modulo (fin2nat kk) k)) acc_v)
           (acc_a |:= safe_idx_nat (safe_idx_nat input
                        (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                        (fin2nat j0 * k + Nat.modulo (fin2nat kk) k),
            acc_a |:= acc_v)) ';
      output|{i0}|{j0} |:= acc_v))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

Definition Avgpool2d_comm {m1 m2 : nat} (k : nat)
  (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{(m1/k)} (ary '{(m2/k)} num))) : comm :=
  seqfor (fun i0 : fin (m1/k) => seqfor (fun i1 : fin (m2/k) =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      acc_a |:= zero ';
      seqfor (fun kk : fin (k * k) =>
        acc_a |:= add (safe_idx_nat (safe_idx_nat input
                         (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                         (fin2nat i1 * k + Nat.modulo (fin2nat kk) k)) acc_v) ';
      output|{i0}|{i1} |:= div_n acc_v (k * k)))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

Definition Maxpool3d_comm {filernum m1 m2 : nat} (k : nat)
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num)))) : comm :=
  seqfor (fun c : fin filernum => seqfor (fun i0 : fin (m1/k) => seqfor (fun i1 : fin (m2/k) =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      acc_a |:= zero ';
      seqfor (fun kk : fin (k * k) =>
        If (gtExp (safe_idx_nat (safe_idx_nat input|[c]
                     (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                     (fin2nat i1 * k + Nat.modulo (fin2nat kk) k)) acc_v)
           (acc_a |:= safe_idx_nat (safe_idx_nat input|[c]
                        (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                        (fin2nat i1 * k + Nat.modulo (fin2nat kk) k),
            acc_a |:= acc_v)) ';
      output|{c}|{i0}|{i1} |:= acc_v)))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

Definition Maxpool4d_comm {batch filernum m1 m2 : nat} (k : nat)
  (input : exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  (output : acc (ary '{batch} (ary '{filernum} (ary '{(m1/k)} (ary '{(m2/k)} num))))) : comm :=
  seqfor (fun b : fin batch => seqfor (fun c : fin filernum =>
    seqfor (fun i0 : fin (m1/k) => seqfor (fun i1 : fin (m2/k) =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      acc_a |:= zero ';
      seqfor (fun kk : fin (k * k) =>
        If (gtExp (safe_idx_nat (safe_idx_nat input|[b]|[c]
                     (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                     (fin2nat i1 * k + Nat.modulo (fin2nat kk) k)) acc_v)
           (acc_a |:= safe_idx_nat (safe_idx_nat input|[b]|[c]
                        (fin2nat i0 * k + Nat.div (fin2nat kk) k))
                        (fin2nat i1 * k + Nat.modulo (fin2nat kk) k),
            acc_a |:= acc_v)) ';
      output|{b}|{c}|{i0}|{i1} |:= acc_v))))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)

(* -------------------- Conv3d -------------------- *)
(* Generic loopacc-based 3-D convolution.  The channel x kernel_height x
   kernel_width window is flattened into a single loop over
   [channel * n1 * n2], avoiding a nested [loopacc] and matching the
   semantic-combinator machinery. *)

Lemma conv3d_flat_c_bound {channel n1 n2} (k : fin (channel * n1 * n2)) :
  Nat.div (fin2nat k) (n1 * n2) < channel.
Proof.
  destruct k as [k Hk]. simpl.
  apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm, Nat.mul_assoc. exact Hk.
Qed.

Lemma conv3d_flat_i1_bound {channel n1 n2} (k : fin (channel * n1 * n2)) :
  Nat.div (Nat.modulo (fin2nat k) (n1 * n2)) n2 < n1.
Proof.
  destruct k as [k Hk]. simpl.
  apply Nat.div_lt_upper_bound; [lia |].
  rewrite Nat.mul_comm. apply Nat.mod_upper_bound. lia.
Qed.

Lemma conv3d_flat_j1_bound {channel n1 n2} (k : fin (channel * n1 * n2)) :
  Nat.modulo (fin2nat k) n2 < n2.
Proof.
  destruct k as [k Hk]. simpl. apply Nat.mod_upper_bound. lia.
Qed.

Definition Conv3d_comm {m1 m2 n1 n2 channel filernum}
  (p s : nat)
  (bias : exp (ary '{filernum} num))
  (w : exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{((m1 - n1 + 2*p)/s + 1)} (ary '{((m2 - n2 + 2*p)/s + 1)} num)))) : comm :=
  seqfor (fun fnum : fin filernum => seqfor (fun i0 : fin ((m1 - n1 + 2*p)/s + 1) => seqfor (fun j0 : fin ((m2 - n2 + 2*p)/s + 1) =>
    @loopacc num (fun tmp =>
      let acc_a := vwt tmp in
      let acc_v := vrd tmp in
      (acc_a |:= zero) ';
      seqfor (fun k : fin (channel * n1 * n2) =>
        let c := Nat.div (fin2nat k) (n1 * n2) in
        let i1 := Nat.div (Nat.modulo (fin2nat k) (n1 * n2)) n2 in
        let j1 := Nat.modulo (fin2nat k) n2 in
        acc_a |:= add (mul (safe_idx_nat (safe_idx_nat (Padding3d p input)|[nat2fin (conv3d_flat_c_bound k)]
                                             (fin2nat i0 * s + i1))
                                     (fin2nat j0 * s + j1))
                           w|[fnum]|[nat2fin (conv3d_flat_c_bound k)]|[nat2fin (conv3d_flat_i1_bound k)]|[nat2fin (conv3d_flat_j1_bound k)])
                       acc_v)
      ';
      output|{fnum}|{i0}|{j0} |:= add acc_v bias|[fnum]
    )
  ))).

(* Semantic equivalence proved in [Ionia.Operators_Sem_Equiv.v]. *)
