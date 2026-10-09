(* ========================================================================= *)
(* Opt_ParGranularity.v                                                      *)
(*                                                                           *)
(* G0 optimisation-rule layer: PARALLEL-GRANULARITY rules                    *)
(* (strip-mining / loop coarsening) for the DPIA semantic model.             *)
(*                                                                           *)
(* Motivation (M7 measurements).  The OpenMP backend forks one parallel      *)
(* task per iteration; when the per-iteration work is tiny the fork/join     *)
(* overhead dominates: LeNet-5 OpenMP at 16 threads ran 443x SLOWER than     *)
(* sequential, and AlexNet regresses beyond 8 threads.  The fix is           *)
(* coarsening: pack p micro-iterations into one parallel block, so that      *)
(* only n blocks are scheduled in parallel and each block runs p iterations  *)
(* sequentially.  This file proves that the (n, p) split is semantics-       *)
(* preserving, turning granularity selection into a pure engineering         *)
(* decision.                                                                 *)
(*                                                                           *)
(* Hardware correspondence:                                                  *)
(*   n*p = total iteration count of the parallel loop;                       *)
(*   n   = number of parallel blocks (chosen ~ #cores / #OpenMP threads);    *)
(*   p   = iterations per block, i.e. per-thread chunk size                  *)
(*         (engineering rule of thumb: p ~ ceil(N / #cores), enlarged until  *)
(*         the measured speedup curve passes the M7 knee).                   *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   1. fin arithmetic: [fin_block b i : fin (n*p)] with value b*p+i,        *)
(*      bounds and both injectivity directions.                              *)
(*   2. [seqfor_strip_mine]: seqfor f = seqfor (fun b => seqfor (fun i =>    *)
(*      f (b*p+i))) — a pure reassociation, NO side condition (p > 0 only    *)
(*      to keep the split lemma simple; p = 0 is engineering-irrelevant).    *)
(*      The [seqfor_app] split machinery follows the cast-based proof        *)
(*      pattern of [Operators_Sem_Equiv.seqfor_app]/[seqfor_2d]; this file   *)
(*      is self-contained and does not import that (heavy) module.           *)
(*   3. [parfor_coarsen]: under [non_interfering], a parfor over n*p         *)
(*      iterations equals the blocked form (n parallel blocks of p           *)
(*      sequential iterations), and ANY repacking (arbitrary permutation     *)
(*      of the flat index space) or ANY reordering of the blocks yields      *)
(*      the same environment — the granularity+schedule freedom statement.   *)
(*   4. [parallel_safe_coarsen]: the mkvParl (A-rule) corollary, plus the    *)
(*      hypothesis-free instance on canonical acceptors [acc'], and a        *)
(*      LeNet-5 output-layer instance (10 classes packed as 2 blocks x 5,    *)
(*      the [A(o, f i)] pattern of [LeNet5_Par]/softmax division loop).      *)
(*                                                                           *)
(* Standalone: imports only Proof_CodeGen, DPIA_Rules, Parallel_Safety;      *)
(* modifies nothing; not in _CoqProject.                                     *)
(* ========================================================================= *)

From Stdlib Require Import Arith Lia.
Require Import Logic.FunctionalExtensionality.

Require Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Ionia.DPIA_Rules.
Import DPIA_Rules.
Require Ionia.Parallel_Safety.
Import Parallel_Safety.

(* -------------------------------------------------------------------------- *)
(* 1. fin arithmetic: the block index b*p+i                                   *)
(* -------------------------------------------------------------------------- *)

Lemma fin_block_lt : forall n p (b : fin n) (i : fin p),
  fin2nat b * p + fin2nat i < n * p.
Proof.
  intros n p b i.
  pose proof (fin_proof b) as Hb. pose proof (fin_proof i) as Hi.
  assert (Hle : S (fin2nat b) * p <= n * p) by (apply Nat.mul_le_mono_r; lia).
  rewrite Nat.mul_succ_l in Hle. lia.
Qed.

(* Flattened index of micro-iteration [i] inside block [b]: value b*p+i. *)
Definition fin_block {n p : nat} (b : fin n) (i : fin p) : fin (n * p) :=
  @nat2fin (n * p) (fin2nat b * p + fin2nat i) (fin_block_lt n p b i).

Lemma fin2nat_fin_block : forall n p (b : fin n) (i : fin p),
  fin2nat (@fin_block n p b i) = fin2nat b * p + fin2nat i.
Proof. intros. unfold fin_block. apply fin2nat_nat2fin. Qed.

(* Distinct micro-iterations inside one block stay distinct. *)
Lemma fin_block_neq_r : forall n p (b : fin n) (i i' : fin p),
  i <> i' -> fin_block b i <> fin_block b i'.
Proof.
  intros n p b i i' Hii Heq. apply Hii.
  apply fin2nat_inj.
  assert (Hv := f_equal (@fin2nat (n * p)) Heq).
  rewrite !fin2nat_fin_block in Hv. lia.
Qed.

(* Distinct blocks stay distinct (values b*p+i and b'*p+i' with i,i' < p can
   only agree when b = b'). *)
Lemma fin_block_neq_l : forall n p (b b' : fin n) (i i' : fin p),
  b <> b' -> fin_block b i <> fin_block b' i'.
Proof.
  intros n p b b' i i' Hbb Heq. apply Hbb.
  apply fin2nat_inj.
  assert (Hv := f_equal (@fin2nat (n * p)) Heq).
  rewrite !fin2nat_fin_block in Hv.
  pose proof (fin_proof b) as Hb. pose proof (fin_proof b') as Hb'.
  pose proof (fin_proof i) as Hi. pose proof (fin_proof i') as Hi'.
  destruct (Nat.lt_trichotomy (fin2nat b) (fin2nat b')) as [Hlt | [Heqb | Hgt]].
  - exfalso.
    assert (Hle : S (fin2nat b) * p <= fin2nat b' * p)
      by (apply Nat.mul_le_mono_r; lia).
    rewrite Nat.mul_succ_l in Hle. lia.
  - exact Heqb.
  - exfalso.
    assert (Hle : S (fin2nat b') * p <= fin2nat b * p)
      by (apply Nat.mul_le_mono_r; lia).
    rewrite Nat.mul_succ_l in Hle. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2. Splitting a seqfor at an arbitrary point (cast-based; the proof        *)
(*    pattern follows Operators_Sem_Equiv.seqfor_app, re-derived here so     *)
(*    this file stays self-contained)                                        *)
(* -------------------------------------------------------------------------- *)

Definition fin_shift_l {p q : nat} (k : fin p) : fin (p + q) :=
  @nat2fin (p + q) (fin2nat k)
    (Nat.lt_le_trans _ _ _ (fin_proof k) (Nat.le_add_r p q)).

Definition fin_shift_r {p q : nat} (k : fin q) : fin (p + q) :=
  @nat2fin (p + q) (p + fin2nat k)
    (proj1 (Nat.add_lt_mono_l _ _ p) (fin_proof k)).

Definition fin_cast {n m : nat} (H : n = m) (k : fin n) : fin m :=
  eq_rect n fin k m H.

Lemma fin_cast_nat : forall n m (H : n = m) (k : fin n),
  fin2nat (fin_cast H k) = fin2nat k.
Proof.
  intros. unfold fin_cast. destruct H. reflexivity.
Qed.

Lemma fin2nat_shift_l : forall p q (k : fin p), fin2nat (@fin_shift_l p q k) = fin2nat k.
Proof.
  intros. unfold fin_shift_l. destruct k as [k Hk]. simpl. auto.
Qed.

Lemma fin2nat_shift_r : forall p q (k : fin q), fin2nat (@fin_shift_r p q k) = p + fin2nat k.
Proof.
  intros. unfold fin_shift_r. destruct k as [k Hk]. simpl. auto.
Qed.

Lemma seqfor_fin1 : forall (f : fin 1 -> comm), seqfor f = f '[0].
Proof.
  intros. rewrite seqfor_Sn. simpl. rewrite skip_l. reflexivity.
Qed.

Lemma seqfor_body_cast :
  forall n m (H : n = m) (body : fin n -> comm),
    seqfor body =
    seqfor (fun k : fin m => body (fin_cast (eq_sym H) k)).
Proof.
  intros n m H body.
  apply functional_extensionality; intro rho.
  case H. simpl. reflexivity.
Qed.

Lemma seqfor_app_Sn :
  forall n p q (H : S n = p + q) (body : fin (S n) -> comm),
    q > 0 ->
    seqfor body =
    seq (seqfor (fun k : fin p => body (fin_cast (eq_sym H) (@fin_shift_l p q k))))
        (seqfor (fun k : fin q => body (fin_cast (eq_sym H) (@fin_shift_r p q k)))).
Proof.
  induction n as [| n' IHn']; intros p q H body Hq.
  - (* n = 0, so S 0 = 1 = p + q, q > 0 implies p = 0, q = 1 *)
    assert (Hp : p = 0) by lia. assert (Hq1 : q = 1) by lia.
    subst p q. simpl in H.
    assert (Heq0 : '[0] = fin_cast (eq_sym H) (@fin_shift_r 0 1 '[0])).
    { apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
    apply functional_extensionality; intro rho.
    rewrite seqfor_Sn. cbn [seqfor]. unfold seq. simpl.
    rewrite Heq0 at 1. reflexivity.
  - (* n = S n', so S (S n') = p + q *)
    destruct q as [| q'].
    + inversion Hq.
    + destruct q' as [| q''].
      * (* q = 1, so p = S n' *)
        assert (Hp : p = S n') by lia. subst p.
        apply functional_extensionality; intro rho.
        rewrite seqfor_Sn.
        assert (Heq1 : seqfor (fun i : fin (S n') => body FS[i]) =
                       seqfor (fun k : fin (S n') => body (fin_cast (eq_sym H) (@fin_shift_l (S n') 1 k)))).
        { apply seqfor_extensionality. intro k. f_equal.
          apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        assert (Heq2 : '[S n'] = fin_cast (eq_sym H) (@fin_shift_r (S n') 1 '[0])).
        { apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        rewrite Heq1. rewrite Heq2 at 1.
        cbn [seqfor]. unfold seq. simpl. reflexivity.
      * (* q = S (S q''), so S n' = p + S q'' *)
        assert (Heq : S n' = p + S q'') by lia.
        apply functional_extensionality; intro rho.
        rewrite seqfor_Sn.
        rewrite IHn' with (H := Heq) (body := fun i : fin (S n') => body FS[i]);
          [ | lia ].
        assert (Heq1 : seqfor (fun k : fin p => body FS[fin_cast (eq_sym Heq) (@fin_shift_l p (S q'') k)]) =
                       seqfor (fun k : fin p => body (fin_cast (eq_sym H) (@fin_shift_l p (S (S q'')) k)))).
        { apply seqfor_extensionality. intro k. f_equal.
          apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        assert (Heq2 : seqfor (fun k : fin (S q'') => body FS[fin_cast (eq_sym Heq) (@fin_shift_r p (S q'') k)]) =
                       seqfor (fun k : fin (S q'') => body (fin_cast (eq_sym H) (@fin_shift_r p (S (S q'')) FS[k])))).
        { apply seqfor_extensionality. intro k. f_equal.
          apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        assert (Heq3 : '[S n'] = fin_cast (eq_sym H) (@fin_shift_r p (S (S q'')) '[S q''])).
        { apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto. }
        rewrite Heq1, Heq2, Heq3 at 1.
        rewrite seqfor_Sn.
        cbn [seqfor]. unfold seq. simpl. reflexivity.
Qed.

Lemma seqfor_app :
  forall p q (body : fin (p + q) -> comm),
    q > 0 ->
    seqfor body =
    seq (seqfor (fun k : fin p => body (fin_shift_l k)))
        (seqfor (fun k : fin q => body (fin_shift_r k))).
Proof.
  intros p q body Hq.
  induction q as [| q' IHq'].
  - lia.
  - destruct q' as [| q''].
    + (* q = 1, p + 1 = S p *)
      assert (Heq : p + 1 = S p) by lia.
      assert (Hcast := @seqfor_body_cast (p + 1) (S p) Heq body).
      rewrite Hcast.
      rewrite seqfor_Sn.
      rewrite (seqfor_fin1 (fun k : fin 1 => body (fin_shift_r k))).
      f_equal.
      * apply seqfor_extensionality. intro k. f_equal.
        apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l; auto.
      * f_equal. apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r; auto.
    + (* q = S (S q''), p + S (S q'') = S (p + S q'') *)
      assert (Heq : p + S (S q'') = S (p + S q'')) by lia.
      assert (Hcast := @seqfor_body_cast (p + S (S q'')) (S (p + S q'')) Heq body).
      rewrite Hcast.
      rewrite seqfor_Sn.
      assert (Hind := IHq' (fun i : fin (p + S q'') => body (fin_cast (eq_sym Heq) (fin2finS i))) ltac:(lia)).
      rewrite Hind. rewrite <- seq_assoc.
      f_equal.
      * apply seqfor_extensionality. intro k. f_equal.
        apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_l, ?fin2nat_fin2finS; auto.
      * assert (HR : seqfor (fun k : fin (S (S q'')) => body (fin_shift_r k)) =
                     seq (seqfor (fun i : fin (S q'') => body (fin_shift_r FS[i])))
                         (body (fin_shift_r '[S q'']))).
        { apply seqfor_Sn. }
        rewrite HR.
        f_equal.
        -- apply seqfor_extensionality. intro k. f_equal.
           apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r, ?fin2nat_fin2finS; auto.
        -- f_equal. apply fin_eq; simpl; rewrite ?fin_cast_nat, ?fin2nat_shift_r; auto.
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. Strip-mining: seqfor over n*p as n blocks of p (pure reassociation)    *)
(* -------------------------------------------------------------------------- *)

(* Deliverable 1 (sequential strip-mine).  Note the order: block 0 covers
   indices 0..p-1, block b covers b*p..b*p+p-1; the snoc-fold structure of
   [seqfor] matches because S n' * p = n'*p + p splits off the LAST block. *)
Theorem seqfor_strip_mine : forall n p (Hp : p > 0) (f : fin (n * p) -> comm),
  seqfor f = seqfor (fun b : fin n => seqfor (fun i : fin p => f (fin_block b i))).
Proof.
  induction n as [| n' IHn']; intros p Hp f.
  - reflexivity.
  - assert (Heq : S n' * p = n' * p + p) by (rewrite Nat.mul_succ_l; reflexivity).
    rewrite (@seqfor_body_cast (S n' * p) (n' * p + p) Heq f).
    rewrite (@seqfor_app (n' * p) p (fun k => f (fin_cast (eq_sym Heq) k)) Hp).
    cbv beta.
    rewrite (IHn' p Hp (fun k : fin (n' * p) => f (fin_cast (eq_sym Heq) (fin_shift_l k)))).
    assert (Hsnoc : seqfor (fun b : fin (S n') => seqfor (fun i : fin p => f (fin_block b i)))
            = seq (seqfor (fun b : fin n' => seqfor (fun i : fin p => f (fin_block FS[b] i))))
                  (seqfor (fun i : fin p => f (fin_block '[n'] i)))).
    { rewrite seqfor_Sn. reflexivity. }
    rewrite Hsnoc. f_equal.
    + apply seqfor_extensionality. intro b.
      apply seqfor_extensionality. intro i. cbv beta. f_equal.
      apply fin2nat_inj.
      rewrite fin_cast_nat, fin2nat_shift_l, !fin2nat_fin_block, fin2nat_fin2finS.
      reflexivity.
    + apply seqfor_extensionality. intro i. cbv beta. f_equal.
      apply fin2nat_inj.
      rewrite fin_cast_nat, fin2nat_shift_r, fin2nat_fin_block, fin2nat_ltS.
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. Parallel coarsening (the core theorem)                                 *)
(* -------------------------------------------------------------------------- *)

(* Block bodies of DIFFERENT blocks commute: each block body is a seqfor of
   iterations that pairwise commute with the other block's iterations
   ([fin_block_neq_l] supplies the index distinctness). *)
Lemma block_body_ni : forall n p d (out : acc (ary '{n*p} d))
    (g : fin (n*p) -> acc d -> comm),
  non_interfering (fun k => g k (out|{k})) ->
  non_interfering (fun b : fin n => seqfor (fun i : fin p => g (fin_block b i) (out|{fin_block b i}))).
Proof.
  intros n p d out g Hni b b' rho Hbb.
  apply seqfor_commute. intros j rho'.
  symmetry. apply seqfor_commute. intros i rho''.
  apply Hni. apply fin_block_neq_l. congruence.
Qed.

(* Deliverable 2 (parallel coarsening).  A parfor over n*p micro-iterations
   packed as n parallel blocks of p sequential iterations:
     (1) equals the blocked sequential form (unconditional — parfor IS the
         snoc fold, so this is strip-mining lifted through [parfor_seqfor]);
     (2) under non-interference, equals ANY repacking σ of the flat index
         space (arbitrary packing of iterations into threads);
     (3) under non-interference, equals the blocked form with blocks
         reordered by any permutation τ (arbitrary block-level schedule).  *)
Theorem parfor_coarsen : forall n p d (Hp : p > 0)
    (out : acc (ary '{n*p} d)) (g : fin (n*p) -> acc d -> comm),
  non_interfering (fun k => g k (out|{k})) ->
  parfor out g
  = seqfor (fun b : fin n => seqfor (fun i : fin p => g (fin_block b i) (out|{fin_block b i})))
  /\ (forall σ : fin (n*p) -> fin (n*p), (forall i j, σ i = σ j -> i = j) ->
      forall rho, parfor out g rho
                = seqfor (fun k => g (σ k) (out|{σ k})) rho)
  /\ (forall τ : fin n -> fin n, (forall i j, τ i = τ j -> i = j) ->
      forall rho, parfor out g rho
                = seqfor (fun b : fin n => seqfor (fun i : fin p =>
                    g (fin_block (τ b) i) (out|{fin_block (τ b) i}))) rho).
Proof.
  intros n p d Hp out g Hni. split; [| split].
  - rewrite parfor_seqfor.
    rewrite (seqfor_strip_mine n p Hp (fun k => g k (out|{k}))).
    reflexivity.
  - intros σ Hinj rho. rewrite parfor_seqfor. symmetry.
    apply (seqfor_perm _ _ σ Hni Hinj).
  - intros τ Hinj rho.
    rewrite parfor_seqfor.
    rewrite (seqfor_strip_mine n p Hp (fun k => g k (out|{k}))).
    symmetry.
    apply (seqfor_perm n
             (fun b : fin n => seqfor (fun i : fin p => g (fin_block b i) (out|{fin_block b i})))
             τ).
    + apply block_body_ni. exact Hni.
    + exact Hinj.
Qed.

(* -------------------------------------------------------------------------- *)
(* 5. Granularity selection for the mkvParl (A-rule) pattern                 *)
(* -------------------------------------------------------------------------- *)

(* Deliverable 3 (mkvParl coarsening): the [parallel_safe] umbrella theorem
   lifted to the coarsened loop.  Side condition: write targets out|{k} are
   pairwise separated (same condition as [Parallel_Safety.parallel_safe_A]). *)
Theorem parallel_safe_coarsen : forall n p d (Hp : p > 0) (f : fin (n*p) -> exp d)
    (out : acc (ary '{n*p} d)),
  (forall i j : fin (n*p), i <> j -> acc_disjoint (out|{i}) (out|{j})) ->
  mkvParl (fun k o => A(o, f k)) out
  = seqfor (fun b : fin n => seqfor (fun i : fin p =>
      A(out|{fin_block b i}, f (fin_block b i))))
  /\ (forall σ : fin (n*p) -> fin (n*p), (forall i j, σ i = σ j -> i = j) ->
      forall rho, mkvParl (fun k o => A(o, f k)) out rho
                = seqfor (fun k => A(out|{σ k}, f (σ k))) rho)
  /\ (forall τ : fin n -> fin n, (forall i j, τ i = τ j -> i = j) ->
      forall rho, mkvParl (fun k o => A(o, f k)) out rho
                = seqfor (fun b : fin n => seqfor (fun i : fin p =>
                    A(out|{fin_block (τ b) i}, f (fin_block (τ b) i)))) rho).
Proof.
  intros n p d Hp f out Hdisj.
  assert (Hni : non_interfering (fun k => A(out|{k}, f k))).
  { apply parallel_safe_A. exact Hdisj. }
  destruct (parfor_coarsen n p d Hp out (fun k o => A(o, f k)) Hni) as [H1 [H2 H3]].
  split; [| split].
  - unfold mkvParl. exact H1.
  - intros σ Hinj rho. unfold mkvParl. apply H2. exact Hinj.
  - intros τ Hinj rho. unfold mkvParl. apply H3. exact Hinj.
Qed.

(* Hypothesis-free instance on canonical acceptors [acc']: index positions
   of a canonical array acceptor are separated ([ni_assign_mkv]). *)
Theorem parallel_safe_coarsen_acc' : forall n p d (Hp : p > 0) (f : fin (n*p) -> exp d)
    (a : path),
  mkvParl (fun k o => A(o, f k)) (@acc' (ary '{n*p} d) a)
  = seqfor (fun b : fin n => seqfor (fun i : fin p =>
      A((@acc' (ary '{n*p} d) a)|{fin_block b i}, f (fin_block b i))))
  /\ (forall σ : fin (n*p) -> fin (n*p), (forall i j, σ i = σ j -> i = j) ->
      forall rho, mkvParl (fun k o => A(o, f k)) (@acc' (ary '{n*p} d) a) rho
                = seqfor (fun k => A((@acc' (ary '{n*p} d) a)|{σ k}, f (σ k))) rho)
  /\ (forall τ : fin n -> fin n, (forall i j, τ i = τ j -> i = j) ->
      forall rho, mkvParl (fun k o => A(o, f k)) (@acc' (ary '{n*p} d) a) rho
                = seqfor (fun b : fin n => seqfor (fun i : fin p =>
                    A((@acc' (ary '{n*p} d) a)|{fin_block (τ b) i},
                      f (fin_block (τ b) i)))) rho).
Proof.
  intros n p d Hp f a.
  assert (Hni : non_interfering (fun k => A((@acc' (ary '{n*p} d) a)|{k}, f k))).
  { exact (ni_assign_mkv (n*p) d a f). }
  destruct (parfor_coarsen n p d Hp (@acc' (ary '{n*p} d) a) (fun k o => A(o, f k)) Hni)
    as [H1 [H2 H3]].
  split; [| split].
  - unfold mkvParl. exact H1.
  - intros σ Hinj rho. unfold mkvParl. apply H2. exact Hinj.
  - intros τ Hinj rho. unfold mkvParl. apply H3. exact Hinj.
Qed.

(* LeNet-5 application instance: the output-layer parallelization point
   (10 classes; the [A(o, f i)]-shaped body, e.g. the softmax division loop
   [o |:= div (pExp in|[j]) v] of [LeNet5_Par]).  The 10 iterations may be
   packed as 2 parallel blocks of 5 — or any other (n, p) with n*p = 10;
   the theorem family above makes the choice correctness-transparent. *)
Example lenet5_output_coarsen : forall (f : fin 10 -> exp num) (a : path),
  mkvParl (fun k o => A(o, f k)) (@acc' (ary '{10} num) a)
  = seqfor (fun b : fin 2 => seqfor (fun i : fin 5 =>
      A((@acc' (ary '{10} num) a)|{fin_block b i}, f (fin_block b i)))).
Proof.
  intros f a.
  destruct (parallel_safe_coarsen_acc' 2 5 num ltac:(lia) f a) as [H1 _].
  exact H1.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions seqfor_strip_mine.
Print Assumptions parfor_coarsen.
Print Assumptions parallel_safe_coarsen.
Print Assumptions parallel_safe_coarsen_acc'.
Print Assumptions lenet5_output_coarsen.
