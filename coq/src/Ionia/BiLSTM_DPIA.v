(* BiLSTM end-to-end DPIA proof — milestone N1b of the NLP/LLM extension
   plan (doc/NLP与LLM扩展开发规划_20260911.md), in the route-A R-based
   expression model.

   Network (all sizes symbolic: sequence T, input dx, hidden dh, classes nc):

     forward  LSTM over xs                (Ionia.Ops_RNN, A_LSTMSeq)
     backward LSTM over the REVERSED xs   ([revseq] index reversal)
     Concat1d of the two final hidden states  (dh+dh features)
     Linear1d -> Softmax1d                (nc classes)

   The new semantic content is the reverse-fold machinery:

     [revseq]        sequence reversal by index map i |-> T-1-i;
     [vcons]         cons on snoc vectors;
     [reduce_vcons]  reduce op init (x :: v) = reduce op (op x init) v;
     [revseq_snoc]   revseq (v, x) = x :: revseq v;
     [bfold]         the BACKWARD recurrence (first element outermost):
                     bfold op init [x0..x_{n-1}] = op x0 (op x1 (... op x_{n-1} init));
     [reduce_revseq_bfold]  THE reverse-fold lemma:
                     forward fold of the reversed sequence = backward fold
                     of the original sequence,
                     reduce op init (revseq v) = bfold op n init v;
     [LSTMSeq_rev]   its direct LSTM instance.

   The end-to-end [A_BiLSTM] follows the same buffer/bind_read discipline
   as [A_TextCNN] (Ionia.TextCNN_DPIA). *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
Import Proof_CodeGen.
(* LSTM cells and the sequence fold rule. *)
Require Import Ionia.Ops_RNN.
(* [Concat1d]. *)
Require Import Ionia.TextCNN_DPIA.
(* [bind_read] elimination; [Linear1d]/[Softmax1d]. *)
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.LeNet5_Imperative.
Require Import Ionia.LeNet5_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Sequence reversal                                                           *)
(* -------------------------------------------------------------------------- *)

(* In-range reverse index: i < T implies T-1-i < T. *)
Lemma rev_bound : forall (T : nat) (i : fin T), (T - 1 - fin2nat i < T)%nat.
Proof. intros T i. pose proof (fin_proof i). lia. Qed.

Definition revidx {T : nat} (i : fin T) : fin T := nat2fin (rev_bound i).

Lemma fin2nat_revidx : forall (T : nat) (i : fin T),
  fin2nat (revidx i) = T - 1 - fin2nat i.
Proof. intros. unfold revidx. apply fin2nat_nat2fin. Qed.

(* Reversed sequence: (revseq xs)[i] = xs[T-1-i]. *)
Definition revseq {T : nat} {s : data} (xs : exp (ary '{T} s))
  : exp (ary '{T} s) :=
  mkvSeq (fun i : fin T => idx xs (revidx i)).

(* -------------------------------------------------------------------------- *)
(* Cons on snoc vectors and its interaction with [reduce]                      *)
(* -------------------------------------------------------------------------- *)

Fixpoint vcons {A : Set} (x : A) (n : nat)
  : vector A n -> vector A (S n) :=
  match n return (vector A n -> vector A (S n)) with
  | 0 => fun _ => (tt, x)
  | S n' => fun v => (vcons x n' (fst v), snd v)
  end.

(* Pointwise read of a cons: index 0 is the new head, index i+1 is v[i]. *)
Lemma v_nth_vcons : forall (n : nat) (A : Set) (x : A) (v : vector A n)
  (i : nat) (d0 : A),
  (i < S n)%nat ->
  v_nth d0 (vcons x n v) i = (if (i =? 0)%nat then x else v_nth d0 v (i - 1)).
Proof.
  induction n as [| n' IHn]; intros A x v i d0 Hi.
  - destruct v. destruct i as [| i']; [reflexivity | exfalso; lia].
  - destruct v as [v' y].
    change (vcons x (S n') (v', y)) with (vcons x n' v', y).
    rewrite v_nth_Sn_simpl.
    destruct (i =? S n')%nat eqn:Ei.
    + apply Nat.eqb_eq in Ei. subst i.
      replace (S n' - 1)%nat with n' by lia.
      destruct (S n' =? 0)%nat eqn:E0; [discriminate |].
      rewrite v_nth_x. reflexivity.
    + rewrite (IHn A x v' i d0) by (apply Nat.eqb_neq in Ei; lia).
      destruct (i =? 0)%nat eqn:E0.
      * reflexivity.
      * rewrite v_nth_Sn by
          (apply Nat.eqb_neq in Ei; apply Nat.eqb_neq in E0; lia).
        reflexivity.
Qed.

(* The same in [idx] form. *)
Lemma idx_vcons : forall (n : nat) (s : data) (x : exp s)
  (v : exp (ary '{n} s)) (i : fin (S n)),
  idx (vcons x n v) i =
  (if (fin2nat i =? 0)%nat then x else v_nth (exp_default s) v (fin2nat i - 1)).
Proof.
  intros. unfold idx, v_idx. apply v_nth_vcons. apply fin_proof.
Qed.

(* Cons-then-fold pushes the consed element onto the accumulator first. *)
Lemma reduce_vcons : forall (n : nat) (s t : data)
  (op : exp s -> exp t -> exp t) (init : exp t) (x : exp s)
  (v : exp (ary '{n} s)),
  reduce op init (vcons x n v) = reduce op (op x init) v.
Proof.
  induction n as [| n' IHn]; intros s t op init x v.
  - destruct v. reflexivity.
  - destruct v as [v' y].
    change (vcons x (S n') (v', y)) with (vcons x n' v', y).
    rewrite reduce_Sn. rewrite IHn. rewrite reduce_Sn. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* The reverse-fold lemma                                                      *)
(* -------------------------------------------------------------------------- *)

(* revseq of a snoc is a cons of the revseq. *)
Lemma revseq_snoc : forall (n : nat) (s : data)
  (v : exp (ary '{n} s)) (x : exp s),
  revseq ((v, x) : exp (ary '{S n} s)) = vcons x n (revseq v).
Proof.
  intros n s v x.
  apply (proj2 (@vector_eq_v_nth (exp s) (S n)
             (revseq ((v, x) : exp (ary '{S n} s))) (vcons x n (revseq v))
             (exp_default s))).
  intro i.
  change (v_nth (exp_default s) (revseq ((v, x) : exp (ary '{S n} s))) i)
    with (idx (revseq ((v, x) : exp (ary '{S n} s))) i).
  change (v_nth (exp_default s) (vcons x n (revseq v)) i)
    with (idx (vcons x n (revseq v)) i).
  unfold revseq at 1. rewrite idx_mkvSeq by lia. cbv beta.
  rewrite idx_vcons.
  unfold idx, v_idx. rewrite fin2nat_revidx.
  (* [v_nth_Sn_simpl] cannot fire here: the vector's type index is
     [fle2nat (fle_self (S n))], which keyed matching does not reduce to
     [S n]; [change] goes through full conversion. *)
  change (v_nth (exp_default s) ((v, x) : exp (ary '{S n} s)) (S n - 1 - fin2nat i))
    with (if (S n - 1 - fin2nat i =? n)%nat then x
          else v_nth (exp_default s) v (S n - 1 - fin2nat i)).
  destruct (fin2nat i =? 0)%nat eqn:E0.
  - (* head: both sides are x *)
    apply Nat.eqb_eq in E0. rewrite E0.
    replace (S n - 1 - 0)%nat with n by lia.
    rewrite Nat.eqb_refl. reflexivity.
  - (* tail: both sides read v[n - fin2nat i] *)
    apply Nat.eqb_neq in E0.
    pose proof (fin_proof i) as Hi.
    assert (Hlt : fin2nat i - 1 < n) by lia.
    assert (Hne : (S n - 1 - fin2nat i =? n)%nat = false).
    { apply Nat.eqb_neq. lia. }
    rewrite Hne.
    unfold revseq.
    replace (v_nth (exp_default s)
              (mkvSeq (fun i0 : fin n => idx v (revidx i0))) (fin2nat i - 1))
      with (idx (mkvSeq (fun i0 : fin n => idx v (revidx i0))) (nat2fin Hlt)).
    2: { unfold idx, v_idx. rewrite fin2nat_nat2fin. reflexivity. }
    rewrite idx_mkvSeq by lia.
    unfold idx, v_idx. rewrite fin2nat_revidx. rewrite fin2nat_nat2fin.
    replace (n - 1 - (fin2nat i - 1))%nat with (n - fin2nat i) by lia.
    replace (S n - 1 - fin2nat i)%nat with (n - fin2nat i) by lia.
    reflexivity.
Qed.

(* The backward recurrence as a snoc recursion: the last element is folded
   onto the accumulator first, so the first element ends up outermost:
   bfold op init [x0..x_{n-1}] = op x0 (op x1 (... (op x_{n-1} init))). *)
Fixpoint bfold {s t : data} (op : exp s -> exp t -> exp t) (n : nat)
  : exp t -> exp (ary '{n} s) -> exp t :=
  match n return (exp t -> exp (ary '{n} s) -> exp t) with
  | 0 => fun init _ => init
  | S n' => fun init v => bfold op n' (op (snd v) init) (fst v)
  end.

(* THE reverse-fold lemma: folding the reversed sequence forward equals
   the backward recurrence over the original sequence. *)
Lemma reduce_revseq_bfold : forall (n : nat) (s t : data)
  (op : exp s -> exp t -> exp t) (init : exp t) (v : exp (ary '{n} s)),
  reduce op init (revseq v) = bfold op n init v.
Proof.
  induction n as [| n' IHn]; intros s t op init v.
  - destruct v. reflexivity.
  - destruct v as [v' x].
    rewrite revseq_snoc. rewrite reduce_vcons.
    change (bfold op (S n') init (v', x)) with (bfold op n' (op x init) v').
    apply IHn.
Qed.

(* Direct LSTM instance: the backward LSTM over the reversed input is the
   backward recurrence over the original input. *)
Lemma LSTMSeq_rev : forall (T dx dh : nat) (ps : LSTMParams dx dh)
  (st0 : exp (ary '{2} (ary '{dh} num)))
  (xs : exp (ary '{T} (ary '{dx} num))),
  LSTMSeq ps st0 (revseq xs) = bfold (LSTMCell ps) T st0 xs.
Proof. intros. unfold LSTMSeq. apply reduce_revseq_bfold. Qed.

(* -------------------------------------------------------------------------- *)
(* BiLSTM network                                                              *)
(* -------------------------------------------------------------------------- *)

Section BiLSTMNet.

  Context (T dx dh nc : nat).
  Context (psF psB : LSTMParams dx dh)
          (c0F h0F c0B h0B : exp (ary '{dh} num))
          (wo : exp (ary '{nc} (ary '{dh + dh} num))) (bo : exp (ary '{nc} num))
          (xs : exp (ary '{T} (ary '{dx} num))).

  (* ---------------- Functional network (opaque stage wrappers) ---------- *)

  Definition bi_fwd : exp (ary '{2} (ary '{dh} num)) :=
    LSTMSeq psF (lstm_state0 c0F h0F) xs.
  Definition bi_bwd : exp (ary '{2} (ary '{dh} num)) :=
    LSTMSeq psB (lstm_state0 c0B h0B) (revseq xs).
  Definition bi_h : exp (ary '{dh + dh} num) :=
    Concat1d (idx bi_fwd st_h) (idx bi_bwd st_h).
  Definition bi_logit : exp (ary '{nc} num) := Linear1d wo bo bi_h.
  Definition bi_soft : exp (ary '{nc} num) := Softmax1d bi_logit.

  Lemma bi_fwd_body : bi_fwd = LSTMSeq psF (lstm_state0 c0F h0F) xs.
  Proof. reflexivity. Qed.
  Lemma bi_bwd_body : bi_bwd = LSTMSeq psB (lstm_state0 c0B h0B) (revseq xs).
  Proof. reflexivity. Qed.
  Lemma bi_h_body : bi_h = Concat1d (idx bi_fwd st_h) (idx bi_bwd st_h).
  Proof. reflexivity. Qed.
  Lemma bi_logit_body : bi_logit = Linear1d wo bo bi_h. Proof. reflexivity. Qed.
  Lemma bi_soft_body : bi_soft = Softmax1d bi_logit. Proof. reflexivity. Qed.

  Opaque bi_fwd bi_bwd bi_h bi_logit bi_soft.

  Definition BiLSTM : exp (ary '{nc} num) := bi_soft.

  (* ---------------- Imperative network (buffer-layered) ----------------- *)

  Definition bilstm_comm (output : acc (ary '{nc} num)) : comm :=
new (fun tF => LSTMSeq_comm psF (lstm_state0 c0F h0F) xs tF ';
bind_read tF (fun eF =>
new (fun tB => LSTMSeq_comm psB (lstm_state0 c0B h0B) (revseq xs) tB ';
bind_read tB (fun eB =>
new (fun tH => Concat1d_comm (idx eF st_h) (idx eB st_h) tH ';
new (fun tL => bind_read tH (fun eH => Linear1d_comm wo bo eH tL) ';
bind_read tL (fun eL => Softmax1d_comm eL output)
) (acc' (Var "bl"))
) (acc' (Var "bh"))
)) (acc' (Var "bB"))
)) (acc' (Var "bF")).

  (* ---------------- Direct (DPIA-normal) form ---------------------------- *)

  Definition bilstm_direct (output : acc (ary '{nc} num)) : comm :=
    A(acc' (Var "bF"), bi_fwd) ';
    A(acc' (Var "bB"), bi_bwd) ';
    A(acc' (Var "bh"), bi_h) ';
    A(acc' (Var "bl"), bi_logit) ';
    A(output, bi_soft).

  (* ---------------- Freshness ------------------------------------------- *)

  Definition bilstm_fresh (output : acc (ary '{nc} num)) (rho : env) : Prop :=
    StructUndefined (acc' (Var "bF") : acc (ary '{2} (ary '{dh} num))) rho /\
    StructUndefined (acc' (Var "bB") : acc (ary '{2} (ary '{dh} num))) rho /\
    StructUndefined (acc' (Var "bh") : acc (ary '{dh + dh} num)) rho /\
    StructUndefined (acc' (Var "bl") : acc (ary '{nc} num)) rho /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "bF") : acc (ary '{2} (ary '{dh} num)))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "bB") : acc (ary '{2} (ary '{dh} num)))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "bh") : acc (ary '{dh + dh} num))) /\
    (forall p, in_acc p output -> ~ in_acc p (acc' (Var "bl") : acc (ary '{nc} num))).

  (* ---------------- End-to-end proof ------------------------------------ *)

  Lemma bilstm_comm_eq_direct :
    forall (output : acc (ary '{nc} num)),
    bilstm_comm output = bilstm_direct output.
  Proof.
    intros.
    unfold bilstm_comm, bilstm_direct, new.
    cbv beta.
    rewrite <- A_LSTMSeq.
    rewrite <- bi_fwd_body.
    rewrite bind_read_replace.
    rewrite <- A_LSTMSeq.
    rewrite <- bi_bwd_body.
    rewrite bind_read_replace.
    rewrite <- A_Concat1d.
    rewrite <- bi_h_body.
    rewrite bind_read_replace_seq.
    rewrite <- A_Linear1d.
    rewrite <- bi_logit_body.
    rewrite bind_read_replace.
    rewrite <- A_Softmax1d.
    rewrite <- bi_soft_body.
    reflexivity.
  Qed.

  Lemma A_BiLSTM_direct :
    forall (output : acc (ary '{nc} num)) (rho : env) (p : path),
    in_acc p output ->
    bilstm_fresh output rho ->
    bilstm_direct output rho p = A(output, BiLSTM) rho p.
  Proof.
    intros.
    unfold bilstm_direct, A. cbv beta.
    etransitivity.
    - apply assign_pure_independent with (rho2 := rho). apply H.
    - unfold BiLSTM. reflexivity.
  Qed.

  (* End-to-end DPIA correctness of BiLSTM: under freshness of the
     temporary buffers, the imperative network observed at an output path
     computes the functional [BiLSTM]. *)
  Theorem A_BiLSTM :
    forall (output : acc (ary '{nc} num)) (rho : env) (p : path),
    in_acc p output ->
    bilstm_fresh output rho ->
    bilstm_comm output rho p = A(output, BiLSTM) rho p.
  Proof.
    intros. rewrite bilstm_comm_eq_direct.
    apply A_BiLSTM_direct; assumption.
  Qed.

End BiLSTMNet.

(* -------------------------------------------------------------------------- *)
(* Concrete instance: T = 8, dx = 2, dh = 2, nc = 3 (fin-8 scale)             *)
(* -------------------------------------------------------------------------- *)

Definition bi_i0_8 : fin 8 := @nat2fin 8 0 (ltac:(lia)).
Definition bi_i7_8 : fin 8 := @nat2fin 8 7 (ltac:(lia)).

Section Small_8_2_2_3.

  Context (psFs psBs : LSTMParams 2 2)
          (c0Fs h0Fs c0Bs h0Bs : exp (ary '{2} num))
          (wos : exp (ary '{3} (ary '{4} num))) (bos : exp (ary '{3} num))
          (xss : exp (ary '{8} (ary '{2} num)))
          (outs : acc (ary '{3} num)).

  (* Shape check: the symbolic network and its command instantiate at the
     small size. *)
  Definition BiLSTM_8_2_2_3 : exp (ary '{3} num) :=
    @BiLSTM 8 2 2 3 psFs psBs c0Fs h0Fs c0Bs h0Bs wos bos xss.

  Definition bilstm_comm_8_2_2_3 : comm :=
    @bilstm_comm 8 2 2 3 psFs psBs c0Fs h0Fs c0Bs h0Bs wos bos xss outs.

End Small_8_2_2_3.

(* [vm_compute]/conversion spot checks of the reverse machinery. *)

(* revseq reads the sequence backwards: (revseq xs)[0] = xs[7] at T=8. *)
Example check_revseq_first :
  forall (xs8 : exp (ary '{8} num)),
  idx (revseq xs8) bi_i0_8 = idx xs8 bi_i7_8.
Proof.
  intros. unfold revseq. rewrite idx_mkvSeq by lia.
  f_equal. apply fin2nat_inj. rewrite fin2nat_revidx. reflexivity.
Qed.

(* The backward recurrence on two elements: first element outermost. *)
Example check_bfold_unroll2 :
  forall (s t : data) (op : exp s -> exp t -> exp t) (init : exp t)
    (a b : exp s),
  bfold op 2 init (((tt, a), b) : exp (ary '{2} s)) = op a (op b init).
Proof. reflexivity. Qed.

(* The reverse-fold lemma at n=2, computationally: forward fold of the
   reversed pair = backward recurrence of the pair. *)
Example check_reduce_revseq2 :
  forall (s t : data) (op : exp s -> exp t -> exp t) (init : exp t)
    (a b : exp s),
  reduce op init (revseq (((tt, a), b) : exp (ary '{2} s))) = op a (op b init).
Proof.
  intros. rewrite reduce_revseq_bfold. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                 *)
(* -------------------------------------------------------------------------- *)

Print Assumptions revseq_snoc.
Print Assumptions reduce_revseq_bfold.
Print Assumptions LSTMSeq_rev.
Print Assumptions A_BiLSTM.
