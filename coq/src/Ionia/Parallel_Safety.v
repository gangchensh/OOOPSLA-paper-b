(* ========================================================================= *)
(* Parallel_Safety.v                                                         *)
(*                                                                           *)
(* P4: Parallelization theorems for the DPIA semantic model.                 *)
(*                                                                           *)
(* [DPIA_Rules.parfor_seqfor] shows [parfor a p = seqfor (fun i => p i       *)
(* (a|{i}))]: the parallel combinator is *defined* as a snoc-order fold, so  *)
(* "parallel = sequential" is a trivial corollary of the definition.  What   *)
(* that equality does NOT justify is the actual execution model of           *)
(* OpenMP/CUDA backends: iterations may run in ANY order, concurrently, with *)
(* the iteration bodies interleaved by the scheduler.  This file closes that *)
(* gap:                                                                      *)
(*                                                                           *)
(*   non_interfering p  :=  iterations pairwise commute on environments;     *)
(*   seqfor_perm        :=  under non-interference, ANY permutation σ of     *)
(*                          the iteration space yields the same environment: *)
(*                          seqfor (fun i => p (σ i)) = seqfor p;            *)
(*   schedule_safe      :=  any complete schedule (a list of iteration       *)
(*                          indices forming a permutation of [fin_enum n])   *)
(*                          executed in that order yields [seqfor p].        *)
(*                                                                           *)
(* This is the mechanized counterpart of the separating-product argument in  *)
(* the DPIA literature (cf. Atkey's strategy-preserving compilation, §5:     *)
(* parallel for is sound because the iterations write to separated regions   *)
(* of the store).  Here separation is witnessed by [acc_disjoint] on the     *)
(* leaf-path sets [in_acc] of the target acceptors, and commutation of       *)
(* separated assignments is proved once and for all                          *)
(* ([assign_disjoint_commute]) by induction on the data type.                *)
(*                                                                           *)
(* Schedules vs. interleavings.  A fine-grained interleaving of the          *)
(* *instructions* of different iteration bodies is, in this model, covered   *)
(* as follows: each iteration body [p i] is an atomic environment            *)
(* transformer, so any complete interleaved execution that runs every        *)
(* iteration exactly once to completion is observationally one of the        *)
(* schedules quantified over in [schedule_safe] (the order in which the      *)
(* atomic bodies commit).  Fine-grained interleaving *inside* non-atomic     *)
(* bodies is sound exactly when the bodies' internal steps commute as well;  *)
(* for bodies built from separated [assign]s this follows by iterating       *)
(* [assign_disjoint_commute] (see [ni_assign]).                              *)
(*                                                                           *)
(* Trust boundary (explicitly NOT modeled):                                  *)
(*   - hardware weak-memory effects (store buffers, non-atomic cache         *)
(*     lines): the model assumes sequentially-consistent atomic commits of   *)
(*     each iteration body;                                                  *)
(*   - bodies with *shared* temporaries: [Proof_CodeGen.new] performs no     *)
(*     cleanup and the caller supplies the temporary acceptor, so two        *)
(*     iterations of e.g. the LeNet-5 conv/pool bodies share temp paths.     *)
(*     For those, full-environment permutation invariance is FALSE (the      *)
(*     residual temp value depends on commit order); only the restriction    *)
(*     to the output region is preserved.  Mechanizing that observational    *)
(*     refinement is future work; the purely output-directed bodies          *)
(*     (mkvPar/A(o, f i) pattern, ReLU1d-style If-of-assigns, softmax        *)
(*     division loop) are fully covered here.                                *)
(*                                                                           *)
(* This file is standalone: it modifies nothing and is not in _CoqProject.   *)
(* ========================================================================= *)

From Stdlib Require Import List Arith Lia Sorting.Permutation FinFun.
Import ListNotations.

Require Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Ionia.DPIA_Rules.
Import DPIA_Rules.

(* -------------------------------------------------------------------------- *)
(* 1. The non-interference predicate                                          *)
(* -------------------------------------------------------------------------- *)

(* Iterations [p i] and [p j] commute on every environment.  This is the
   pointwise form used by [seqfor_for_rev_equiv]; comm-level commutation
   lemmas ([assign_assign_neq], [assign_disjoint_commute]) feed it directly. *)
Definition non_interfering {n:nat} (p : fin n -> comm) : Prop :=
  forall i j rho, i <> j -> p i (p j rho) = p j (p i rho).

(* -------------------------------------------------------------------------- *)
(* 2. Schedules: lists of iteration indices                                   *)
(* -------------------------------------------------------------------------- *)

(* Execute the iteration bodies in the order given by the list. *)
Fixpoint seqfor_list {n:nat} (l : list (fin n)) (p : fin n -> comm) : comm :=
  match l with
  | [] => skip
  | i :: l' => p i '; seqfor_list l' p
  end.

(* The canonical enumeration of [fin n] in increasing order, matching the
   snoc-fold structure of [seqfor]: [0; 1; ...; n-1] as elements of fin n. *)
Fixpoint fin_enum (n:nat) : list (fin n) :=
  match n with
  | O => []
  | S n' => map fin2finS (fin_enum n') ++ (ltS n' :: nil)
  end.

Lemma fin_enum_length : forall n, length (fin_enum n) = n.
Proof.
  induction n as [|n IHn]; simpl; auto.
  rewrite length_app, length_map, IHn. simpl. lia.
Qed.

Lemma fin2nat_ltS : forall n, fin2nat (ltS n) = n.
Proof.
  intros n. unfold ltS. rewrite fin2nat_exist. reflexivity.
Qed.

Lemma fin2finS_injective : forall n (i j : fin n), FS[i] = FS[j] -> i = j.
Proof.
  intros n i j H. apply fin2nat_inj.
  assert (H2 : fin2nat (FS[i]) = fin2nat (FS[j])) by (rewrite H; reflexivity).
  rewrite !fin2nat_fin2finS in H2. exact H2.
Qed.

Lemma fin_enum_In : forall n (i : fin n), In i (fin_enum n).
Proof.
  induction n as [|n IHn]; intros i.
  - destruct i as [x Hx]. exfalso. lia.
  - destruct (Nat.eq_dec (fin2nat i) n) as [E|E].
    + assert (Hi : i = ltS n).
      { apply fin2nat_inj. rewrite fin2nat_ltS. exact E. }
      rewrite Hi. simpl. apply in_or_app. right. simpl. auto.
    + assert (Hi : i = FS[finS2fin i E]).
      { symmetry. apply finS2fin_fin2finS. }
      rewrite Hi at 1. simpl. apply in_or_app. left.
      apply in_map. apply IHn.
Qed.

Lemma fin_enum_NoDup : forall n, NoDup (fin_enum n).
Proof.
  induction n as [|n IHn]; simpl.
  - constructor.
  - apply NoDup_app.
    + apply Injective_map_NoDup; auto.
      intros i j H. exact (fin2finS_injective _ _ _ H).
    + constructor; auto. constructor.
    + intros a Ha Hin.
      apply in_map_iff in Ha. destruct Ha as [j [Haj _]].
      destruct Hin as [Hin|Hfalse]; [| contradiction].
      rewrite <- Hin in Haj.
      assert (H1 : fin2nat (FS[j]) = n).
      { rewrite Haj. apply fin2nat_ltS. }
      rewrite fin2nat_fin2finS in H1.
      pose proof (fin_correct j). lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. seqfor as execution of the canonical schedule                           *)
(* -------------------------------------------------------------------------- *)

Lemma seqfor_list_app : forall n (l1 : list (fin n)),
  forall (l2 : list (fin n)) (p : fin n -> comm) rho,
  seqfor_list (l1 ++ l2) p rho = seqfor_list l2 p (seqfor_list l1 p rho).
Proof.
  intros n l1. induction l1 as [|i l1 IH]; intros l2 p rho.
  - reflexivity.
  - simpl. unfold seq. simpl. apply IH.
Qed.

Lemma seqfor_list_map : forall m n (l : list (fin m)),
  forall (σ : fin m -> fin n) (p : fin n -> comm) rho,
  seqfor_list (map σ l) p rho = seqfor_list l (fun i => p (σ i)) rho.
Proof.
  intros m n l. induction l as [|i l IH]; intros σ p rho.
  - reflexivity.
  - simpl. unfold seq. simpl. apply IH.
Qed.

Lemma seqfor_fin_enum : forall n (p : fin n -> comm) rho,
  seqfor p rho = seqfor_list (fin_enum n) p rho.
Proof.
  induction n as [|n IHn]; intros p rho.
  - reflexivity.
  - rewrite seqfor_Sn. unfold seq at 1.
    change (fin_enum (S n)) with (map fin2finS (fin_enum n) ++ (ltS n :: nil)).
    rewrite seqfor_list_app.
    rewrite seqfor_list_map.
    rewrite <- (IHn (fun i => p FS[i]) rho).
    reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. Permutation invariance (the core theorem)                               *)
(* -------------------------------------------------------------------------- *)

(* Executing the bodies in any permuted order gives the same environment.
   Proof: induction on the [Permutation] derivation; the swap case is exactly
   the non-interference hypothesis (adjacent swaps generate all
   permutations). *)
Lemma seqfor_list_perm : forall n (p : fin n -> comm),
  non_interfering p ->
  forall l l', Permutation l l' ->
  forall rho, seqfor_list l p rho = seqfor_list l' p rho.
Proof.
  intros n p Hni l l' Hperm.
  induction Hperm; intros rho.
  - reflexivity.
  - simpl. unfold seq. simpl. rewrite IHHperm. reflexivity.
  - simpl. unfold seq. simpl.
    destruct (fin_eq_dec x y) as [E|E].
    + subst y. reflexivity.
    + rewrite (Hni x y rho E). reflexivity.
  - rewrite IHHperm1, IHHperm2. reflexivity.
Qed.

(* An injective endomap on [fin n] is surjective (pigeonhole on the canonical
   enumeration), hence [map σ (fin_enum n)] is a permutation of [fin_enum n]. *)
Lemma map_fin_enum_permutation : forall n (σ : fin n -> fin n),
  (forall i j, σ i = σ j -> i = j) ->
  Permutation (map σ (fin_enum n)) (fin_enum n).
Proof.
  intros n σ Hinj.
  apply NoDup_Permutation.
  - apply Injective_map_NoDup.
    + exact Hinj.
    + apply fin_enum_NoDup.
  - apply fin_enum_NoDup.
  - intros x. split.
    + intros _. apply fin_enum_In.
    + intros _.
      assert (Hincl : incl (fin_enum n) (map σ (fin_enum n))).
      { apply NoDup_length_incl.
        - apply Injective_map_NoDup; auto. apply fin_enum_NoDup.
        - rewrite length_map, fin_enum_length. apply le_n.
        - intros a _. apply fin_enum_In. }
      apply Hincl. apply fin_enum_In.
Qed.

(* Main theorem P4: under non-interference, iterating along any permutation
   of the index set yields the sequential fold. *)
Theorem seqfor_perm : forall n (p : fin n -> comm) (σ : fin n -> fin n),
  non_interfering p ->
  (forall i j, σ i = σ j -> i = j) ->
  forall rho, seqfor (fun i => p (σ i)) rho = seqfor p rho.
Proof.
  intros n p σ Hni Hinj rho.
  rewrite (seqfor_fin_enum n (fun i => p (σ i)) rho).
  rewrite (seqfor_fin_enum n p rho).
  rewrite <- (seqfor_list_map n n (fin_enum n) σ p rho).
  apply seqfor_list_perm; auto.
  apply map_fin_enum_permutation; auto.
Qed.

(* Schedule form of the same result: any complete execution order (each
   iteration exactly once) is a permutation of [fin_enum n], hence safe.
   Together with the remark in the header (atomic bodies commit in some
   order), this is the interleaving theorem of item 3. *)
Theorem schedule_safe : forall n (p : fin n -> comm) (l : list (fin n)),
  non_interfering p ->
  Permutation l (fin_enum n) ->
  forall rho, seqfor_list l p rho = seqfor p rho.
Proof.
  intros n p l Hni Hperm rho.
  rewrite (seqfor_list_perm n p Hni l (fin_enum n) Hperm rho).
  symmetry. apply seqfor_fin_enum.
Qed.

(* -------------------------------------------------------------------------- *)
(* 5. Separation: disjoint assignments commute                                *)
(* -------------------------------------------------------------------------- *)

(* Two acceptors are separated when their leaf path sets are disjoint. *)
Definition acc_disjoint {d1 d2:data} (a1 : acc d1) (a2 : acc d2) : Prop :=
  forall p q, in_acc p a1 -> in_acc q a2 -> p <> q.

Lemma in_acc_idx : forall (n:nat) (m:fle n) (d:data)
    (a : acc (@ary n m d)) (i : fin (fle2nat m)) p,
  in_acc p (a|{i}) -> in_acc p a.
Proof.
  intros n m d a i p H.
  exact (ex_intro (fun i0 => in_acc p (a|{i0})) i H).
Qed.

(* The key semantic fact: assignments to separated acceptors commute, at ANY
   pair of data types.  Induction on d1 (with a nested induction on d2 at the
   base case); array assignments are unfolded into [seqfor] of sub-assignments
   ([assign_ary]) and commuted past the other command with [seqfor_commute]. *)
Lemma assign_disjoint_commute : forall d1 d2 (a1 : acc d1) (a2 : acc d2)
    (e1 : exp d1) (e2 : exp d2) rho,
  acc_disjoint a1 a2 ->
  assign a2 e2 (assign a1 e1 rho) = assign a1 e1 (assign a2 e2 rho).
Proof.
  induction d1 as [|n1 m1 d1 IHd1].
  - (* d1 = num: a1 is a leaf path; nested induction on d2 *)
    intros d2. induction d2 as [|n2 m2 d2 IHd2]; intros a1 a2 e1 e2 rho Hdisj.
    + (* num / num: pointwise update_permute *)
      simpl. apply update_permute.
      apply (Hdisj a1 a2); reflexivity.
    + (* num / ary: commute the single update past the seqfor *)
      rewrite assign_ary. symmetry. apply seqfor_commute.
      intros i rho'. symmetry. apply IHd2.
      intros p q Hp Hq. apply (Hdisj p q Hp).
      apply in_acc_idx with (i := i). exact Hq.
  - (* d1 = ary: unfold to seqfor and commute past c2 *)
    intros d2 a1 a2 e1 e2 rho Hdisj.
    rewrite assign_ary. apply seqfor_commute.
    intros i rho'. apply IHd1.
    intros p q Hp Hq. apply (Hdisj p q); auto.
    apply in_acc_idx with (i := i). exact Hp.
Qed.

(* Typical parallel loop bodies [fun i => assign (g i) (f i)] are
   non-interfering as soon as the write targets are pairwise separated. *)
Lemma ni_assign : forall n d (g : fin n -> acc d) (f : fin n -> exp d),
  (forall i j, i <> j -> acc_disjoint (g i) (g j)) ->
  non_interfering (fun i => assign (g i) (f i)).
Proof.
  intros n d g f Hdisj i j rho Hij.
  apply assign_disjoint_commute. apply Hdisj.
  intros H. apply Hij. symmetry. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* 6. Canonical acceptors [acc'] occupy separated index positions             *)
(* -------------------------------------------------------------------------- *)

Fixpoint path_size (p : path) : nat :=
  match p with
  | Var _ => 1
  | AryIdx _ q => S (path_size q)
  end.

(* [wraps a b]: [b] is [a] extended by a (possibly empty) chain of [AryIdx]
   constructors on top.  Leaf paths of [acc' d pa] are exactly the [AryIdx]-
   extensions of [pa] ([acc'_leaf_wraps]). *)
Inductive wraps (a : path) : path -> Prop :=
  | wraps_refl : wraps a a
  | wraps_cons : forall (n:nat) (i:fin n) (q:path),
      wraps a q -> wraps a (@AryIdx n i q).

Lemma wraps_trans : forall a b, wraps a b -> forall c, wraps b c -> wraps a c.
Proof.
  intros a b H c H2. induction H2; auto.
  constructor. auto.
Qed.

Lemma wraps_size : forall a b, wraps a b -> path_size a <= path_size b.
Proof.
  intros a b H. induction H; simpl; lia.
Qed.

Lemma wraps_size_eq : forall a b, wraps a b -> path_size a = path_size b -> a = b.
Proof.
  intros a b H. induction H; intros Hsize; auto.
  exfalso. pose proof (wraps_size _ _ H). simpl in Hsize. lia.
Qed.

(* Two [AryIdx]-extensions of the same path are comparable. *)
Lemma wraps_comparable : forall a p, wraps a p ->
  forall b, wraps b p -> wraps a b \/ wraps b a.
Proof.
  intros a p Ha. induction Ha; intros b Hb.
  - right. exact Hb.
  - inversion Hb as [| n0 i0 q0 Hq0 Heq]; subst.
    + left. apply wraps_cons. exact Ha.
    + destruct (IHHa b Hq0) as [Hab|Hba].
      * left. exact Hab.
      * right. exact Hba.
Qed.

Lemma acc'_leaf_wraps : forall d (pa : path) p,
  in_acc p (@acc' d pa) -> wraps pa p.
Proof.
  induction d as [|n m d IHd]; intros pa p Hin.
  - assert (H : pa = p) by exact Hin.
    subst p. constructor.
  - assert (Hin' : exists i, in_acc p ((@acc' (@ary n m d) pa)|{i})) by exact Hin.
    destruct Hin' as [i Hin'].
    assert (Hconv : (@acc' (@ary n m d) pa)|{i} = @acc' d (AryIdx i pa)).
    { unfold idxAcc. simpl. rewrite v_idx_mk_vec. reflexivity. }
    rewrite Hconv in Hin'.
    apply IHd in Hin'.
    eapply wraps_trans; [| exact Hin'].
    apply wraps_cons. constructor.
Qed.

(* Leaves of [acc' d1 (AryIdx i a)] and [acc' d2 (AryIdx j a)] never collide
   when [i <> j]: a common leaf would be an [AryIdx]-extension of both roots,
   the two roots are comparable, and having equal sizes they would be equal,
   forcing [i = j]. *)
Lemma acc'_AryIdx_disjoint : forall d1 d2 n (i j : fin n) (a : path),
  i <> j ->
  acc_disjoint (@acc' d1 (@AryIdx n i a)) (@acc' d2 (@AryIdx n j a)).
Proof.
  intros d1 d2 n i j a Hij p q Hp Hq Heq.
  apply acc'_leaf_wraps in Hp. apply acc'_leaf_wraps in Hq.
  subst q.
  destruct (wraps_comparable _ _ Hp _ Hq) as [H|H].
  - apply wraps_size_eq in H; [| simpl; reflexivity ].
    apply AryIdx_eq in H. destruct H as [_ [Hfin _]].
    apply Hij. apply fin2nat_inj. exact Hfin.
  - apply wraps_size_eq in H; [| simpl; reflexivity ].
    apply AryIdx_eq in H. destruct H as [_ [Hfin _]].
    apply Hij. apply fin2nat_inj. symmetry. exact Hfin.
Qed.

(* Bodies writing distinct index positions of a canonical array acceptor are
   non-interfering. *)
Lemma ni_assign_mkv : forall n d (a : path) (f : fin n -> exp d),
  non_interfering (fun i => @assign d ((@acc' (ary '{n} d) a)|{i}) (f i)).
Proof.
  intros n d a f i j rho Hij.
  assert (Hconv : forall k, (@acc' (ary '{n} d) a)|{k} = @acc' d (@AryIdx n k a)).
  { intro k. unfold idxAcc. simpl. rewrite v_idx_mk_vec. reflexivity. }
  rewrite !Hconv.
  apply assign_disjoint_commute.
  apply acc'_AryIdx_disjoint. intros H. apply Hij. symmetry. exact H.
Qed.

(* -------------------------------------------------------------------------- *)
(* 7. Application: parallel safety of the mkvPar pattern                      *)
(* -------------------------------------------------------------------------- *)

(* The umbrella theorem: a non-interfering mkv body may be executed
   sequentially ([mkvSeql]), in any permuted order, or along any complete
   schedule — all agree with [mkvParl]. *)
Theorem parallel_safe : forall n d (f : fin n -> acc d -> comm)
    (out : acc (ary '{n} d)),
  non_interfering (fun i => f i (out|{i})) ->
  (mkvParl f out = mkvSeql f out)
  /\ (forall σ : fin n -> fin n, (forall i j, σ i = σ j -> i = j) ->
      forall rho, mkvParl f out rho = seqfor (fun i => f (σ i) (out|{σ i})) rho)
  /\ (forall l : list (fin n), Permutation l (fin_enum n) ->
      forall rho, mkvParl f out rho = seqfor_list l (fun i => f i (out|{i})) rho).
Proof.
  intros n d f out Hni. split; [| split].
  - unfold mkvParl, mkvSeql. apply parfor_seqfor.
  - intros σ Hinj rho. unfold mkvParl. rewrite parfor_seqfor.
    symmetry. apply (seqfor_perm n (fun i => f i (out|{i})) σ Hni Hinj rho).
  - intros l Hperm rho. unfold mkvParl. rewrite parfor_seqfor.
    symmetry. apply (schedule_safe n (fun i => f i (out|{i})) l Hni Hperm rho).
Qed.

(* Non-interference of the DPIA A-rule pattern [fun i o => A(o, f i)] — the
   shape produced by [AmkvPar] — reduces to separation of the write targets.
   This is the pattern of the LeNet-5 parallelization points with purely
   output-directed bodies (softmax division loop [o |:= div (pExp in|[j]) v]
   is literally [A(o, f j)]; elementwise ReLU is its [If] variant below). *)
Theorem parallel_safe_A : forall n d (f : fin n -> exp d) (out : acc (ary '{n} d)),
  (forall i j, i <> j -> acc_disjoint (out|{i}) (out|{j})) ->
  non_interfering (fun i => A(out|{i}, f i)).
Proof.
  intros n d f out Hdisj.
  apply ni_assign. exact Hdisj.
Qed.

(* Fully closed instance for canonical acceptors: no hypotheses remain. *)
Theorem parallel_safe_acc' : forall n d (f : fin n -> exp d) (a : path),
  (mkvParl (fun i o => A(o, f i)) (@acc' (ary '{n} d) a)
   = mkvSeql (fun i o => A(o, f i)) (@acc' (ary '{n} d) a))
  /\ (forall σ : fin n -> fin n, (forall i j, σ i = σ j -> i = j) ->
      forall rho, mkvParl (fun i o => A(o, f i)) (@acc' (ary '{n} d) a) rho
                = seqfor (fun i => A((@acc' (ary '{n} d) a)|{σ i}, f (σ i))) rho)
  /\ (forall l : list (fin n), Permutation l (fin_enum n) ->
      forall rho, mkvParl (fun i o => A(o, f i)) (@acc' (ary '{n} d) a) rho
                = seqfor_list l (fun i => A((@acc' (ary '{n} d) a)|{i}, f i)) rho).
Proof.
  intros n d f a.
  assert (Hni : non_interfering (fun i => A((@acc' (ary '{n} d) a)|{i}, f i))).
  { apply parallel_safe_A.
    intros i j Hij.
    assert (Hconv : forall k, (@acc' (ary '{n} d) a)|{k} = @acc' d (@AryIdx n k a)).
    { intro k. unfold idxAcc. simpl. rewrite v_idx_mk_vec. reflexivity. }
    rewrite !Hconv. apply acc'_AryIdx_disjoint. exact Hij. }
  pose proof (parallel_safe n d (fun i o => A(o, f i)) (@acc' (ary '{n} d) a) Hni)
    as [H1 [H2 H3]].
  split; [| split].
  - exact H1.
  - exact H2.
  - exact H3.
Qed.

(* -------------------------------------------------------------------------- *)
(* 8. LeNet-5 ReLU1d-style bodies: [If] of two assignments to [out|{i}]       *)
(* -------------------------------------------------------------------------- *)

(* At [num] type each branch is a single [update], so non-interference is
   just [update_permute]; the side condition is index-position distinctness
   of the output acceptor (for [vwt]-generated acceptors this holds by
   distinctness of the indexed names; for [acc'] it is proved below). *)
Lemma ni_If_assign_num : forall n (out : acc (ary '{n} num))
    (b : fin n -> bool) (e1 e2 : fin n -> exp num),
  (forall i j : fin n, i <> j -> out|{i} <> out|{j}) ->
  non_interfering (fun i => If (b i) (out|{i} |:= e1 i) (out|{i} |:= e2 i)).
Proof.
  intros n out b e1 e2 Hneq i j rho Hij.
  unfold If. destruct (b i); destruct (b j); simpl;
  apply update_permute; apply Hneq; congruence.
Qed.

(* Permutation safety of [parfor] with a ReLU1d-shaped body (matches
   [LeNet5_Par.ReLU1d_par_comm]; the softmax division loop is the
   [parallel_safe_A] instance). *)
Theorem relu1d_pattern_safe : forall n (out : acc (ary '{n} num))
    (b : fin n -> bool) (e1 e2 : fin n -> exp num),
  (forall i j : fin n, i <> j -> out|{i} <> out|{j}) ->
  forall (σ : fin n -> fin n), (forall i j, σ i = σ j -> i = j) ->
  forall rho,
    parfor out (fun i o => If (b i) (o |:= e1 i) (o |:= e2 i)) rho
    = seqfor (fun i => If (b (σ i)) (out|{σ i} |:= e1 (σ i)) (out|{σ i} |:= e2 (σ i))) rho.
Proof.
  intros n out b e1 e2 Hneq σ Hinj rho.
  rewrite parfor_seqfor. symmetry.
  apply (seqfor_perm n (fun i => If (b i) (out|{i} |:= e1 i) (out|{i} |:= e2 i)) σ);
  auto.
  apply ni_If_assign_num; auto.
Qed.

Lemma AryIdx_neq : forall n (i j : fin n) (a : path),
  i <> j -> @AryIdx n i a <> @AryIdx n j a.
Proof.
  intros n i j a Hij Heq.
  apply AryIdx_eq in Heq. destruct Heq as [_ [Hfin _]].
  apply Hij. apply fin2nat_inj. exact Hfin.
Qed.

(* Closed instance for canonical acceptors: no hypotheses remain. *)
Theorem relu1d_pattern_safe_acc' : forall n (a : path)
    (b : fin n -> bool) (e1 e2 : fin n -> exp num) (σ : fin n -> fin n),
  (forall i j, σ i = σ j -> i = j) ->
  forall rho,
    parfor (@acc' (ary '{n} num) a) (fun i o => If (b i) (o |:= e1 i) (o |:= e2 i)) rho
    = seqfor (fun i => If (b (σ i))
        ((@acc' (ary '{n} num) a)|{σ i} |:= e1 (σ i))
        ((@acc' (ary '{n} num) a)|{σ i} |:= e2 (σ i))) rho.
Proof.
  intros n a b e1 e2 σ Hinj rho.
  apply relu1d_pattern_safe; auto.
  intros i j Hij.
  assert (Hconv : forall k, (@acc' (ary '{n} num) a)|{k} = @AryIdx n k a).
  { intro k. unfold idxAcc. simpl. rewrite v_idx_mk_vec. reflexivity. }
  rewrite !Hconv. apply AryIdx_neq. exact Hij.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions seqfor_perm.
Print Assumptions schedule_safe.
Print Assumptions assign_disjoint_commute.
Print Assumptions parallel_safe.
Print Assumptions parallel_safe_acc'.
Print Assumptions relu1d_pattern_safe_acc'.
