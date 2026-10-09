(* ========================================================================= *)
(* Opt_HierPar.v                                                             *)
(*                                                                           *)
(* Ventus adaptation V2b (proof side): mechanization of the three-level      *)
(* OpenCL parallelism design of Zhang Xiaoli's thesis §4.7                   *)
(* (mapGlobal/mapWorkgroup/mapLocal, parforGlobal/Workgroup/Local) as        *)
(* rewrite RULES of the route-A DPIA semantic model.  In the thesis these    *)
(* rules were never machine-proved; here they fall out of [AmkvPar] +        *)
(* [seqfor_strip_mine] + [seqfor_perm].                                      *)
(*                                                                           *)
(* Correspondence with the Ventus hardware model (see                        *)
(* hw_adapt/02_Ventus适配分析.md §1-§2):                                     *)
(*   - grid level      <-> CTA scheduler / workgroup id (get_group_id);      *)
(*   - workgroup level <-> warp group inside an SM (get_local_id);           *)
(*   - lane level      <-> lane/vid.v: each thread runs its chunk            *)
(*                         SEQUENTIALLY (SIMT lockstep within a warp is a    *)
(*                         scheduling detail; the model's seqfor covers any  *)
(*                         execution order by [seqfor_perm] under            *)
(*                         non-interference);                                *)
(*   - NO shuffle/gather/reduction instructions in the Ventus ISA:           *)
(*     cross-lane communication is only possible via LDS + workgroup         *)
(*     barrier.  Hence the reduction is implemented in the standard          *)
(*     no-shuffle form: thread-local sequential reduction into per-lane      *)
(*     LDS slots, (barrier), then a combination phase over the slots.        *)
(*   - workgroup-level barrier: in this sequentially-consistent environment  *)
(*     model the barrier is observational [skip]: the two-phase composition  *)
(*     (write phase fully precedes the combine phase) IS the barrier         *)
(*     semantics.  The OpenCL printer backend maps the phase boundary to     *)
(*     barrier(CLK_LOCAL_MEM_FENCE).                                         *)
(*   - LDS scratch slots are modeled as W distinguished leaf paths           *)
(*     [lds|{w}]; the main theorem is observational: equality holds on       *)
(*     every path OUTSIDE the LDS scratch region (same trust-boundary        *)
(*     discipline as Parallel_Safety.v: scratch contents differ, outputs     *)
(*     agree).                                                               *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   1. [fin_block3]: two-level index decomposition of fin (G*(W*L)) with    *)
(*      injectivity facts.                                                   *)
(*   2. [mkvParl3]: the three-level combinator (grid parfor x workgroup      *)
(*      parfor x lane seqfor, up to [parfor_seqfor]); [mkvParl3_strip]       *)
(*      (unconditional, two strip-mines), [AmkvPar3] (the rule theorem),     *)
(*      [mkvParl3_flat_perm] / [mkvParl3_grid_perm] (schedule freedom),      *)
(*      [hierpar_safe_acc'] (hypothesis-free canonical-acceptor instance).   *)
(*   3. [ffold]: snoc-order value fold over [fin n]; [ffold_app] (pure       *)
(*      reassociation, no side conditions), [ffold_acc] (accumulator shift,  *)
(*      associativity + left unit), [ffold_chunk] (block decomposition,      *)
(*      associativity + left unit — NO commutativity needed for the          *)
(*      order-respecting LDS decomposition).                                 *)
(*   4. [efold]/[ffold_perm]: under commutativity, ANY permutation of the    *)
(*      combination order (in particular any tree reduction shape) yields    *)
(*      the same value.                                                      *)
(*   5. Pure LDS reduction: [lds_chunk_reduce]                               *)
(*      (reduce op init xs = two-level fold of per-lane chunk folds) and     *)
(*      [lds_chunk_reduce_perm] (lane-combination order freedom).            *)
(*   6. Imperative LDS reduction: [lds_lane]/[lds_write_phase]/[lds_reduce]; *)
(*      [lds_write_schedule]/[lds_write_perm] (write-phase schedule freedom  *)
(*      via [schedule_safe]/[seqfor_perm]); [lds_reduce_correct]             *)
(*      (lds_reduce = reducel outside the LDS scratch); [lds_sum_correct]    *)
(*      (closed instance for add: lds_reduce add zero = suml).               *)
(*                                                                           *)
(* Standalone: imports Proof_CodeGen, DPIA_Rules, Parallel_Safety,           *)
(* Opt_ParGranularity; modifies nothing; NOT in _CoqProject (compiled        *)
(* standalone per task instruction).                                         *)
(* ========================================================================= *)

From Stdlib Require Import List Arith Lia Sorting.Permutation Reals.
Require Import Logic.FunctionalExtensionality.

Require Ionia.Proof_CodeGen.
Import Proof_CodeGen.
Require Ionia.DPIA_Rules.
Import DPIA_Rules.
Require Ionia.Parallel_Safety.
Import Parallel_Safety.
Require Ionia.Opt_ParGranularity.
Import Opt_ParGranularity.

(* -------------------------------------------------------------------------- *)
(* 1. Two-level index decomposition: fin G x fin W x fin L ~ fin (G*(W*L))   *)
(* -------------------------------------------------------------------------- *)

(* Flat index of lane [l] of workgroup [w] of grid block [g]:
   value g*(W*L) + (w*L + l).  Composed directly from [fin_block]. *)
Definition fin_block3 {G W L : nat} (g : fin G) (w : fin W) (l : fin L)
  : fin (G * (W * L)) :=
  fin_block g (fin_block w l).

Lemma fin2nat_fin_block3 : forall G W L (g : fin G) (w : fin W) (l : fin L),
  fin2nat (@fin_block3 G W L g w l)
  = fin2nat g * (W * L) + (fin2nat w * L + fin2nat l).
Proof.
  intros. unfold fin_block3. rewrite !fin2nat_fin_block. reflexivity.
Qed.

(* Injectivity, level by level. *)
Lemma fin_block3_neq_g : forall G W L (g g' : fin G) (w w' : fin W) (l l' : fin L),
  g <> g' -> @fin_block3 G W L g w l <> @fin_block3 G W L g' w' l'.
Proof.
  intros G W L g g' w w' l l' Hg. unfold fin_block3.
  apply fin_block_neq_l. exact Hg.
Qed.

Lemma fin_block3_neq_w : forall G W L (g : fin G) (w w' : fin W) (l l' : fin L),
  w <> w' -> @fin_block3 G W L g w l <> @fin_block3 G W L g w' l'.
Proof.
  intros G W L g w w' l l' Hw. unfold fin_block3.
  apply fin_block_neq_r. apply fin_block_neq_l. exact Hw.
Qed.

Lemma fin_block3_neq_l : forall G W L (g : fin G) (w : fin W) (l l' : fin L),
  l <> l' -> @fin_block3 G W L g w l <> @fin_block3 G W L g w l'.
Proof.
  intros G W L g w l l' Hl. unfold fin_block3.
  apply fin_block_neq_r. apply fin_block_neq_r. exact Hl.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2. The three-level combinator and the rule theorem                        *)
(* -------------------------------------------------------------------------- *)

(* [mkvParl3 f out]: three-level parallel construction over the flat output
   array.  Outermost two levels are the parforGlobal/parforWorkgroup levels
   (each is literally a parfor body up to [parfor_seqfor]); the innermost
   seqfor is the per-lane sequential chunk. *)
Definition mkvParl3 {G W L : nat} {d : data}
  (f : fin (G * (W * L)) -> acc d -> comm) (out : acc (ary '{G * (W * L)} d))
  : comm :=
  seqfor (fun g : fin G =>
    seqfor (fun w : fin W =>
      seqfor (fun l : fin L => f (fin_block3 g w l) (out|{fin_block3 g w l})))).

(* Unconditional: the three-level nest IS the flat parfor (two strip-mines;
   parfor is defined as the snoc fold, so no side condition beyond the
   positivity needed by [seqfor_strip_mine]). *)
Theorem mkvParl3_strip : forall G W L (HW : W > 0) (HL : L > 0) (d : data)
    (f : fin (G * (W * L)) -> acc d -> comm) (out : acc (ary '{G * (W * L)} d)),
  mkvParl3 f out = parfor out f.
Proof.
  intros G W L HW HL d f out.
  assert (HWL : W * L > 0) by (destruct W; [lia|]; destruct L; [lia|]; simpl; lia).
  unfold mkvParl3. rewrite parfor_seqfor.
  rewrite (seqfor_strip_mine G (W * L) HWL (fun k => f k (out|{k}))).
  apply seqfor_extensionality. intro g. cbv beta.
  rewrite (seqfor_strip_mine W L HL (fun i : fin (W * L) => f (fin_block g i) (out|{fin_block g i}))).
  reflexivity.
Qed.

(* Deliverable 2 (the three-level rule): the DPIA A-rule for [mkvPar]
   instantiated to the grid/workgroup/lane decomposition. *)
Theorem AmkvPar3 : forall G W L (HW : W > 0) (HL : L > 0) (d : data)
    (f : fin (G * (W * L)) -> exp d) (a : acc (ary '{G * (W * L)} d)),
  A(a, mkvPar f) = mkvParl3 (fun k o => A(o, f k)) a.
Proof.
  intros G W L HW HL d f a.
  rewrite AmkvPar. unfold mkvParl. symmetry.
  apply (mkvParl3_strip G W L HW HL d (fun k o => A(o, f k)) a).
Qed.

(* Schedule freedom, flat form: under non-interference of the flat bodies,
   the three-level construction equals the bodies executed along ANY
   permutation of the flat index space (arbitrary work-item-to-thread
   assignment). *)
Theorem mkvParl3_flat_perm : forall G W L (HW : W > 0) (HL : L > 0) (d : data)
    (f : fin (G * (W * L)) -> acc d -> comm) (out : acc (ary '{G * (W * L)} d)),
  non_interfering (fun k => f k (out|{k})) ->
  forall (σ : fin (G * (W * L)) -> fin (G * (W * L))),
    (forall i j, σ i = σ j -> i = j) ->
  forall rho, mkvParl3 f out rho = seqfor (fun k => f (σ k) (out|{σ k})) rho.
Proof.
  intros G W L HW HL d f out Hni σ Hinj rho.
  rewrite (mkvParl3_strip G W L HW HL d f out). rewrite parfor_seqfor.
  symmetry. apply (seqfor_perm _ _ σ Hni Hinj).
Qed.

(* Schedule freedom, grid form: the G workgroup-blocks may execute in any
   order (arbitrary CTA schedule); the workgroup/lane structure inside each
   block is preserved. *)
Theorem mkvParl3_grid_perm : forall G W L (HW : W > 0) (HL : L > 0) (d : data)
    (f : fin (G * (W * L)) -> acc d -> comm) (out : acc (ary '{G * (W * L)} d)),
  non_interfering (fun k => f k (out|{k})) ->
  forall (τ : fin G -> fin G),
    (forall i j, τ i = τ j -> i = j) ->
  forall rho, mkvParl3 f out rho
            = seqfor (fun g : fin G =>
                seqfor (fun w : fin W =>
                  seqfor (fun l : fin L =>
                    f (fin_block3 (τ g) w l) (out|{fin_block3 (τ g) w l})))) rho.
Proof.
  intros G W L HW HL d f out Hni τ Hinj rho.
  assert (Hstrip : forall g0 : fin G,
    seqfor (fun w : fin W => seqfor (fun l : fin L =>
              f (fin_block3 g0 w l) (out|{fin_block3 g0 w l})))
    = seqfor (fun i : fin (W * L) => f (fin_block g0 i) (out|{fin_block g0 i}))).
  { intro g0. symmetry.
    rewrite (seqfor_strip_mine W L HL
               (fun i : fin (W * L) => f (fin_block g0 i) (out|{fin_block g0 i}))).
    reflexivity. }
  assert (E1 : seqfor (fun g : fin G =>
                 seqfor (fun w : fin W => seqfor (fun l : fin L =>
                   f (fin_block3 g w l) (out|{fin_block3 g w l}))))
             = seqfor (fun g : fin G =>
                 seqfor (fun i : fin (W * L) => f (fin_block g i) (out|{fin_block g i})))).
  { apply seqfor_extensionality. intro g. apply Hstrip. }
  assert (E2 : seqfor (fun g : fin G =>
                 seqfor (fun i : fin (W * L) =>
                   f (fin_block (τ g) i) (out|{fin_block (τ g) i}))) rho
             = seqfor (fun g : fin G =>
                 seqfor (fun i : fin (W * L) =>
                   f (fin_block g i) (out|{fin_block g i}))) rho).
  { apply (seqfor_perm G
             (fun g : fin G => seqfor (fun i : fin (W * L) =>
               f (fin_block g i) (out|{fin_block g i}))) τ).
    - apply (block_body_ni G (W * L) d out f Hni).
    - exact Hinj. }
  assert (E3 : seqfor (fun g : fin G =>
                 seqfor (fun i : fin (W * L) =>
                   f (fin_block (τ g) i) (out|{fin_block (τ g) i})))
             = seqfor (fun g : fin G =>
                 seqfor (fun w : fin W => seqfor (fun l : fin L =>
                   f (fin_block3 (τ g) w l) (out|{fin_block3 (τ g) w l}))))).
  { apply seqfor_extensionality. intro g. symmetry. apply Hstrip. }
  unfold mkvParl3. rewrite E1. rewrite <- E3. symmetry. exact E2.
Qed.

(* Hypothesis-free instance on canonical acceptors [acc']: distinct index
   positions are separated ([ni_assign_mkv]), so the flat schedule freedom
   holds unconditionally. *)
Theorem hierpar_safe_acc' : forall G W L (HW : W > 0) (HL : L > 0) (d : data)
    (f : fin (G * (W * L)) -> exp d) (a : path)
    (σ : fin (G * (W * L)) -> fin (G * (W * L))),
  (forall i j, σ i = σ j -> i = j) ->
  forall rho,
    mkvParl3 (fun k o => A(o, f k)) (@acc' (ary '{G * (W * L)} d) a) rho
    = seqfor (fun k => A((@acc' (ary '{G * (W * L)} d) a)|{σ k}, f (σ k))) rho.
Proof.
  intros G W L HW HL d f a σ Hinj rho.
  apply (mkvParl3_flat_perm G W L HW HL d (fun k o => A(o, f k))
           (@acc' (ary '{G * (W * L)} d) a)); auto.
  exact (ni_assign_mkv (G * (W * L)) d a f).
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. ffold: snoc-order value fold over [fin n] (the value-level analogue    *)
(*    of [seqfor]; matches [v_reduce]'s fold direction)                      *)
(* -------------------------------------------------------------------------- *)

Fixpoint ffold {n : nat} (op : R -> R -> R) (init : R) : (fin n -> R) -> R :=
  match n return (fin n -> R) -> R with
  | O => fun _ => init
  | S n' => fun g => op (g (ltS n')) (ffold op init (fun i : fin n' => g FS[i]))
  end.

Lemma ffold_Sn : forall n (op : R -> R -> R) (init : R) (g : fin (S n) -> R),
  ffold op init g = op (g '[n]) (ffold op init (fun i : fin n => g FS[i])).
Proof. reflexivity. Qed.

Lemma ffold_ext : forall n (op : R -> R -> R) (init : R) (g1 g2 : fin n -> R),
  (forall i, g1 i = g2 i) -> ffold op init g1 = ffold op init g2.
Proof.
  induction n as [|n IHn]; intros op init g1 g2 H.
  - reflexivity.
  - rewrite !ffold_Sn. rewrite (H '[n]). f_equal.
    apply IHn. intro i. apply H.
Qed.

(* Reindexing along a value-preserving map between equal-sized index types. *)
Lemma ffold_reindex : forall n m (H : n = m) (op : R -> R -> R) (init : R)
    (h : fin m -> R) (r : fin n -> fin m),
  (forall i, fin2nat (r i) = fin2nat i) ->
  ffold op init h = ffold op init (fun i => h (r i)).
Proof.
  intros n m H op init h r Hr. destruct H.
  apply ffold_ext. intro i. f_equal. apply fin_eq'. symmetry. apply Hr.
Qed.

(* Splitting the fold at p + q: pure reassociation, no side conditions
   (value-level analogue of [Opt_ParGranularity.seqfor_app]). *)
Lemma ffold_app : forall p q (op : R -> R -> R) (init : R)
    (h : fin (p + q) -> R),
  ffold op init h
  = ffold op (ffold op init (fun k : fin p => h (fin_shift_l k)))
             (fun k : fin q => h (fin_shift_r k)).
Proof.
  intros p q. induction q as [|q' IHq']; intros op init h.
  - (* q = 0 *)
    simpl.
    apply (ffold_reindex p (p + 0) (eq_sym (Nat.add_0_r p)) op init h
             (fun k => fin_shift_l k)).
    intro k. apply fin2nat_shift_l.
  - (* q = S q': cast h to fin (S (p + q')) via Nat.add_succ_r *)
    rewrite (ffold_reindex (S (p + q')) (p + S q') (eq_sym (Nat.add_succ_r p q'))
               op init h (fun k => fin_cast (eq_sym (Nat.add_succ_r p q')) k)).
    2: { intro k. apply fin_cast_nat. }
    rewrite (ffold_Sn (p + q') op init
               (fun k : fin (S (p + q')) => h (fin_cast (eq_sym (Nat.add_succ_r p q')) k))).
    rewrite (IHq' op init
               (fun i : fin (p + q') => h (fin_cast (eq_sym (Nat.add_succ_r p q')) FS[i]))).
    rewrite (ffold_Sn q' op (ffold op init (fun k : fin p => h (fin_shift_l k)))
               (fun k : fin (S q') => h (fin_shift_r k))).
    f_equal.
    + f_equal. apply fin_eq'.
      rewrite fin_cast_nat, fin2nat_ltS, fin2nat_shift_r, fin2nat_ltS.
      reflexivity.
    + assert (HAC : ffold op init
                      (fun k : fin p => h (fin_cast (eq_sym (Nat.add_succ_r p q')) FS[fin_shift_l k]))
                  = ffold op init (fun k : fin p => h (fin_shift_l k))).
      { apply ffold_ext. intro k. f_equal. apply fin_eq'.
        rewrite fin_cast_nat, fin2nat_fin2finS, !fin2nat_shift_l. reflexivity. }
      rewrite HAC. apply ffold_ext. intro k. f_equal. apply fin_eq'.
      rewrite fin_cast_nat, fin2nat_fin2finS, !fin2nat_shift_r, fin2nat_fin2finS.
      reflexivity.
Qed.

(* Accumulator shift: starting a fold from ACC equals combining the
   init-started fold with ACC afterwards.  Needs associativity (in the
   direction [op a (op b c) = op (op a b) c], matching [Rplus_assoc]) and
   the LEFT unit. *)
Lemma ffold_acc : forall n (op : R -> R -> R) (init : R) (g : fin n -> R) (ACC : R),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op init a = a) ->
  ffold op ACC g = op (ffold op init g) ACC.
Proof.
  induction n as [|n IHn]; intros op init g ACC Hass Hunit.
  - simpl. symmetry. apply Hunit.
  - rewrite ffold_Sn.
    rewrite (IHn op init (fun i : fin n => g FS[i]) ACC Hass Hunit).
    rewrite ffold_Sn. rewrite Hass. reflexivity.
Qed.

(* Block decomposition: folding the flat W*L indices equals folding the W
   per-block folds.  Associativity + left unit only — the ORDER of elements
   is respected, so commutativity is not needed (this is exactly the
   no-shuffle LDS decomposition: lane-local sequential fold, then in-order
   combination of the partials). *)
Theorem ffold_chunk : forall W L (op : R -> R -> R) (init : R)
    (g : fin (W * L) -> R),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op init a = a) ->
  ffold op init g
  = ffold op init (fun w : fin W => ffold op init (fun l : fin L => g (fin_block w l))).
Proof.
  induction W as [|W' IHW']; intros L op init g Hass Hunit.
  - reflexivity.
  - assert (Heq : S W' * L = W' * L + L) by (rewrite Nat.mul_succ_l; reflexivity).
    rewrite (ffold_reindex (W' * L + L) (S W' * L) (eq_sym Heq) op init g
               (fun k => fin_cast (eq_sym Heq) k)).
    2: { intro k. apply fin_cast_nat. }
    rewrite (ffold_app (W' * L) L op init (fun k => g (fin_cast (eq_sym Heq) k))).
    rewrite (ffold_acc L op init
               (fun k : fin L => g (fin_cast (eq_sym Heq) (fin_shift_r k)))
               (ffold op init (fun k : fin (W' * L) => g (fin_cast (eq_sym Heq) (fin_shift_l k))))
               Hass Hunit).
    rewrite (IHW' L op init
               (fun k : fin (W' * L) => g (fin_cast (eq_sym Heq) (fin_shift_l k))) Hass Hunit).
    rewrite (ffold_Sn W' op init
               (fun w : fin (S W') => ffold op init (fun l : fin L => g (fin_block w l)))).
    f_equal.
    + (* last block: indices W'*L + l = fin_block '[W'] l *)
      apply ffold_ext. intro l. f_equal. apply fin_eq'.
      rewrite fin_cast_nat, fin2nat_shift_r, fin2nat_fin_block, fin2nat_ltS.
      reflexivity.
    + (* prefix blocks: block w of the prefix = block (FS w) of the whole *)
      apply ffold_ext. intro w. apply ffold_ext. intro l.
      f_equal. apply fin_eq'.
      rewrite fin_cast_nat, fin2nat_shift_l, !fin2nat_fin_block, fin2nat_fin2finS.
      reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. Combination-order freedom (tree reductions) under commutativity        *)
(* -------------------------------------------------------------------------- *)

(* List fold matching [ffold]'s operand order. *)
Definition efold (op : R -> R -> R) (init : R) (l : list R) : R :=
  fold_right (fun x acc => op x acc) init l.

Lemma efold_cons : forall (op : R -> R -> R) (init : R) x l,
  efold op init (x :: l) = op x (efold op init l).
Proof. reflexivity. Qed.

Lemma efold_perm : forall (op : R -> R -> R) (init : R),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a b, op a b = op b a) ->
  forall l l', Permutation l l' -> efold op init l = efold op init l'.
Proof.
  intros op init Hass Hcomm l l' H. induction H.
  - reflexivity.
  - rewrite !efold_cons. rewrite IHPermutation. reflexivity.
  - rewrite !efold_cons.
    rewrite (Hass y x (efold op init l)), (Hcomm y x), <- (Hass x y (efold op init l)).
    reflexivity.
  - rewrite IHPermutation1, IHPermutation2. reflexivity.
Qed.

Lemma ffold_eq_efold : forall n (op : R -> R -> R) (init : R) (g : fin n -> R),
  ffold op init g = efold op init (map g (rev (fin_enum n))).
Proof.
  induction n as [|n IHn]; intros op init g.
  - reflexivity.
  - rewrite ffold_Sn.
    change (fin_enum (S n)) with (map fin2finS (fin_enum n) ++ (ltS n :: nil)).
    rewrite rev_unit. rewrite <- map_rev.
    cbn [map]. rewrite map_map. rewrite efold_cons.
    rewrite <- (IHn op init (fun i : fin n => g FS[i])).
    reflexivity.
Qed.

(* Under commutativity, folding along ANY permutation of the index set gives
   the same value: this is the soundness of the LDS tree-reduction shape
   (any balanced in-workgroup tree is a particular combination order). *)
Theorem ffold_perm : forall n (op : R -> R -> R) (init : R) (g : fin n -> R)
    (σ : fin n -> fin n),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a b, op a b = op b a) ->
  (forall i j, σ i = σ j -> i = j) ->
  ffold op init (fun i => g (σ i)) = ffold op init g.
Proof.
  intros n op init g σ Hass Hcomm Hinj.
  rewrite !ffold_eq_efold. apply efold_perm; auto.
  assert (Hlist : map (fun i => g (σ i)) (rev (fin_enum n))
                = map g (rev (map σ (fin_enum n)))).
  { rewrite <- map_map. f_equal. apply map_rev. }
  rewrite Hlist. apply Permutation_map.
  eapply Permutation_trans.
  - symmetry. apply Permutation_rev.
  - eapply Permutation_trans.
    + apply map_fin_enum_permutation. exact Hinj.
    + apply Permutation_rev.
Qed.

(* -------------------------------------------------------------------------- *)
(* 5. Pure LDS reduction: reduce = two-level fold of per-lane chunk folds    *)
(* -------------------------------------------------------------------------- *)

Lemma vreduce_mk_vec : forall n (op : R -> R -> R) (init : R) (g : fin n -> R),
  v_reduce op init (mk_vec g) = ffold op init g.
Proof.
  induction n as [|n IHn]; intros op init g.
  - reflexivity.
  - rewrite mk_vec_Sn. rewrite v_reduce_Sn. rewrite IHn. rewrite ffold_Sn.
    try (f_equal; f_equal; apply fin_eq';
         rewrite fin2nat_exist, fin2nat_ltS; reflexivity).
Qed.

Lemma reduce_mkvSeq : forall n (op : exp num -> exp num -> exp num)
    (init : exp num) (g : fin n -> exp num),
  reduce op init (mkvSeq g) = ffold op init g.
Proof.
  intros n op init g. unfold reduce, mkvSeq. apply vreduce_mk_vec.
Qed.

(* Deliverable 3 (pure core): the flat reduction over W*L elements equals
   the two-level "lane-local fold + cross-lane fold" decomposition.
   Associativity + left unit only — the standard no-shuffle LDS reduction
   keeps the operand order, so commutativity is not required. *)
Theorem lds_chunk_reduce : forall W L (op : exp num -> exp num -> exp num)
    (init : exp num) (xs : exp (ary '{W * L} num)),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op init a = a) ->
  reduce op init xs
  = ffold op init (fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block w l])).
Proof.
  intros W L op init xs Hass Hunit.
  assert (Hxs : xs = mkvSeq (fun k : fin (W * L) => xs|[k])).
  { unfold mkvSeq. symmetry.
    transitivity (mk_vec (fun x : fin (W * L) => v_nth (exp_default num) xs x)).
    - apply mk_vec_eq. intro i. reflexivity.
    - apply (mk_vec_bij_fin _ (exp_default num) xs). }
  rewrite Hxs at 1. rewrite reduce_mkvSeq.
  apply (ffold_chunk W L op init (fun k : fin (W * L) => xs|[k]) Hass Hunit).
Qed.

(* With commutativity, the W lane partials may be combined in ANY order
   (any tree shape), still yielding the flat reduction. *)
Theorem lds_chunk_reduce_perm : forall W L (op : exp num -> exp num -> exp num)
    (init : exp num) (xs : exp (ary '{W * L} num)) (σ : fin W -> fin W),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op init a = a) ->
  (forall a b, op a b = op b a) ->
  (forall i j, σ i = σ j -> i = j) ->
  reduce op init xs
  = ffold op init (fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block (σ w) l])).
Proof.
  intros W L op init xs σ Hass Hunit Hcomm Hinj.
  rewrite (lds_chunk_reduce W L op init xs Hass Hunit).
  symmetry.
  apply (ffold_perm W op init
           (fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block w l]))
           σ Hass Hcomm Hinj).
Qed.

(* Closed instance for [add]: hypotheses discharged from the Reals library. *)
Lemma add_assocA : forall a b c : R, add a (add b c) = add (add a b) c.
Proof. intros. unfold add. rewrite Rplus_assoc. reflexivity. Qed.

Lemma add_zero_lA : forall a : R, add zero a = a.
Proof. intro. unfold add, zero. apply Rplus_0_l. Qed.

Lemma add_commA : forall a b : R, add a b = add b a.
Proof. intros. unfold add. apply Rplus_comm. Qed.

Theorem lds_sum_chunk : forall W L (xs : exp (ary '{W * L} num)),
  sum xs
  = ffold add zero (fun w : fin W => ffold add zero (fun l : fin L => xs|[fin_block w l])).
Proof.
  intros W L xs. unfold sum.
  apply (lds_chunk_reduce W L add zero xs add_assocA add_zero_lA).
Qed.

(* -------------------------------------------------------------------------- *)
(* 6. Imperative LDS reduction                                               *)
(* -------------------------------------------------------------------------- *)

(* --- reading scalar cells after updates --------------------------------- *)

Lemma read_exp_num : forall (rho : env) (p : acc num),
  read_exp rho p = match rho p with Some e => e | None => zero end.
Proof. reflexivity. Qed.

Lemma read_exp_update_eq : forall (rho : env) (p : acc num) (e : R),
  read_exp (update rho p e) p = e.
Proof. intros. rewrite read_exp_num, update_eq. reflexivity. Qed.

Lemma read_exp_update_neq : forall (rho : env) (p q : acc num) (e : R),
  p <> q -> read_exp (update rho p e) q = read_exp rho q.
Proof. intros. rewrite !read_exp_num, update_neq; auto. Qed.

(* Sequential accumulation loop into a scalar cell, value-characterized. *)
(* Plain-path variant of [DPIA_Rules.assign_update_num] (the [acc']-wrapped
   form does not rewrite-match bare paths, since [acc'] does not reduce
   under keyed unification). *)
Lemma assign_update_path : forall (p : acc num) (e1 : R) (f : R -> R),
  (p |:= e1) '; (fun rho => (p |:= f (read_exp rho p)) rho) = p |:= f e1.
Proof.
  intros p e1 f. apply functional_extensionality. intro rho.
  unfold seq. cbv beta. rewrite !assign_num.
  rewrite read_exp_update_eq. apply update_shadow.
Qed.

Lemma seqfor_acc_fold : forall n (op : R -> R -> R) (init : R) (g : fin n -> R)
    (p : acc num),
  (p |:= init) '; seqfor (fun i : fin n => fun rho =>
    (p |:= op (g i) (read_exp rho p)) rho)
  = p |:= ffold op init g.
Proof.
  induction n as [|n IHn]; intros op init g p.
  - rewrite seqfor_0. rewrite skip_r. reflexivity.
  - rewrite seqfor_Sn. rewrite seq_assoc.
    rewrite (IHn op init (fun i : fin n => g FS[i]) p).
    rewrite (assign_update_path p (ffold op init (fun i : fin n => g FS[i]))
               (fun old => op (g '[n]) old)).
    cbv beta. rewrite (ffold_Sn n op init g). reflexivity.
Qed.

(* Lane body: thread [w] sequentially folds its L-element chunk into its
   LDS slot [a] (thread-private sequential reduction, the only intra-thread
   phase). *)
Definition lds_lane {W L : nat} (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (w : fin W) (a : acc num) : comm :=
  (a |:= init) '; seqfor (fun l : fin L => fun rho =>
    (a |:= op (xs|[fin_block w l]) (read_exp rho a)) rho).

Lemma lds_lane_eq : forall W L (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (w : fin W) (a : acc num),
  lds_lane op init xs w a
  = a |:= ffold op init (fun l : fin L => xs|[fin_block w l]).
Proof.
  intros. unfold lds_lane. apply seqfor_acc_fold.
Qed.

(* Write phase: all lanes store their partials into the LDS scratch array
   [lds] (one leaf path per lane).  Lanes are pairwise non-interfering, so
   this phase may execute in ANY order ([lds_write_schedule] below). *)
Definition lds_write_phase {W L : nat} (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (lds : acc (ary '{W} num)) : comm :=
  seqfor (fun w : fin W => lds_lane op init xs w (lds|{w})).

(* Combine phase (after the workgroup barrier): fold the LDS partials into
   [tmp]. *)
Definition lds_combine {W : nat} (op : R -> R -> R) (init : R)
    (lds : acc (ary '{W} num)) (tmp : acc num) : comm :=
  (tmp |:= init) '; seqfor (fun w : fin W => fun rho =>
    (tmp |:= op (read_exp rho (lds|{w})) (read_exp rho tmp)) rho).

(* The full LDS reduction command: write phase, (barrier — observational
   [skip] in this SC model, see the file header), combine phase, pass the
   result to the continuation. *)
Definition lds_reduce {W L : nat} (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (cont : R -> comm)
    (lds : acc (ary '{W} num)) (tmp : acc num) : comm :=
  lds_write_phase op init xs lds '; (lds_combine op init lds tmp
    '; (fun rho => cont (read_exp rho tmp) rho)).

(* --- value/frame facts about a seqfor of scalar assigns ----------------- *)

Lemma seqfor_assigns_val : forall W (paths : fin W -> acc num) (vals : fin W -> R),
  (forall w w', w <> w' -> paths w <> paths w') ->
  forall rho w,
    read_exp (seqfor (fun w' : fin W => assign (paths w') (vals w')) rho) (paths w)
    = vals w.
Proof.
  induction W as [|W' IHW']; intros paths vals Hpaths rho w.
  - destruct w as [x Hx]. exfalso. lia.
  - rewrite seqfor_Sn. unfold seq. cbv beta.
    destruct (fin_eq_dec w '[W']) as [E|E].
    + subst w. rewrite assign_num. rewrite read_exp_update_eq. reflexivity.
    + assert (Hv : fin2nat w <> W').
      { intro Hc. apply E. apply fin_eq'. rewrite Hc. apply fin2nat_ltS. }
      rewrite assign_num. rewrite read_exp_update_neq.
      2: { apply Hpaths. intro Hc. apply E. symmetry. exact Hc. }
      pose proof (IHW' (fun i => paths FS[i]) (fun i => vals FS[i])
                    ltac:(intros i j Hij; apply Hpaths; intro Heq; apply Hij;
                          exact (fin2finS_injective _ _ _ Heq))
                    rho (finS2fin w Hv)) as IH.
      cbv beta in IH. rewrite finS2fin_fin2finS in IH. exact IH.
Qed.

Lemma seqfor_assigns_frame : forall W (paths : fin W -> acc num) (vals : fin W -> R)
    rho q,
  (forall w, q <> paths w) ->
  seqfor (fun w : fin W => assign (paths w) (vals w)) rho q = rho q.
Proof.
  induction W as [|W' IHW']; intros paths vals rho q Hq.
  - reflexivity.
  - rewrite seqfor_Sn. unfold seq. cbv beta.
    rewrite assign_num. rewrite update_neq.
    2: { intro Hc. apply (Hq '[W']). symmetry. exact Hc. }
    apply IHW'. intro w. apply Hq.
Qed.

(* --- combine phase value ------------------------------------------------ *)

(* Generalized over the slot-path family so induction on W goes through. *)
Lemma seqfor_combine_val : forall W (op : R -> R -> R) (init : R)
    (paths : fin W -> acc num) (c : fin W -> R) (tmp : acc num) rho,
  (forall w, tmp <> paths w) ->
  (forall w, read_exp rho (paths w) = c w) ->
  ((tmp |:= init) '; seqfor (fun w : fin W => fun rho' =>
     (tmp |:= op (read_exp rho' (paths w)) (read_exp rho' tmp)) rho')) rho
  = update rho tmp (ffold op init c).
Proof.
  induction W as [|W' IHW']; intros op init paths c tmp rho Htmp Hc.
  - rewrite seqfor_0. rewrite skip_r. rewrite assign_num. reflexivity.
  - rewrite seqfor_Sn. rewrite seq_assoc. unfold seq at 1. cbv beta.
    rewrite (IHW' op init (fun i => paths FS[i]) (fun i => c FS[i]) tmp rho).
    2: { intro w. apply Htmp. }
    2: { intro w. apply Hc. }
    rewrite assign_num. rewrite read_exp_update_eq.
    rewrite (read_exp_update_neq _ _ _ _ (Htmp '[W'])).
    rewrite (Hc '[W']). rewrite update_shadow.
    rewrite (ffold_Sn W' op init c). reflexivity.
Qed.

Lemma lds_combine_val : forall W (op : R -> R -> R) (init : R)
    (lds : acc (ary '{W} num)) (c : fin W -> R) (tmp : acc num) rho,
  (forall w, tmp <> lds|{w}) ->
  (forall w, read_exp rho (lds|{w}) = c w) ->
  lds_combine op init lds tmp rho = update rho tmp (ffold op init c).
Proof.
  intros. unfold lds_combine. apply seqfor_combine_val; auto.
Qed.

(* --- write phase: value, frame, non-interference, schedule freedom ------ *)

Lemma lds_write_eq : forall W L (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (lds : acc (ary '{W} num)),
  lds_write_phase op init xs lds
  = seqfor (fun w : fin W =>
      lds|{w} |:= ffold op init (fun l : fin L => xs|[fin_block w l])).
Proof.
  intros. unfold lds_write_phase.
  apply seqfor_extensionality. intro w. apply lds_lane_eq.
Qed.

Lemma lds_write_ni : forall W L (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (lds : acc (ary '{W} num)),
  (forall w w' : fin W, w <> w' -> lds|{w} <> lds|{w'}) ->
  non_interfering (fun w : fin W =>
    lds|{w} |:= ffold op init (fun l : fin L => xs|[fin_block w l])).
Proof.
  intros W L op init xs lds Hlds i j rho Hij.
  apply assign_disjoint_commute.
  intros p q Hp Hq. simpl in Hp, Hq.
  rewrite <- Hp, <- Hq. apply Hlds. intro Hc. apply Hij. symmetry. exact Hc.
Qed.

(* The write phase may execute along ANY complete lane schedule — this is
   the [schedule_safe] application: on hardware the lanes of a workgroup
   commit their LDS partials in arbitrary (warp-interleaved) order. *)
Theorem lds_write_schedule : forall W L (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (lds : acc (ary '{W} num)),
  (forall w w' : fin W, w <> w' -> lds|{w} <> lds|{w'}) ->
  forall (sched : list (fin W)), Permutation sched (fin_enum W) ->
  forall rho,
    lds_write_phase op init xs lds rho
    = seqfor_list sched
        (fun w : fin W => lds|{w} |:= ffold op init (fun l : fin L => xs|[fin_block w l])) rho.
Proof.
  intros W L op init xs lds Hlds sched Hsched rho.
  rewrite lds_write_eq. symmetry.
  apply (schedule_safe W _ sched); auto.
  apply (lds_write_ni W L op init xs lds Hlds).
Qed.

Theorem lds_write_perm : forall W L (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (lds : acc (ary '{W} num)),
  (forall w w' : fin W, w <> w' -> lds|{w} <> lds|{w'}) ->
  forall (σ : fin W -> fin W), (forall i j, σ i = σ j -> i = j) ->
  forall rho,
    lds_write_phase op init xs lds rho
    = seqfor (fun w : fin W =>
        lds|{σ w} |:= ffold op init (fun l : fin L => xs|[fin_block (σ w) l])) rho.
Proof.
  intros W L op init xs lds Hlds σ Hinj rho.
  rewrite lds_write_eq. symmetry.
  apply (seqfor_perm W
           (fun w : fin W => lds|{w} |:= ffold op init (fun l : fin L => xs|[fin_block w l]))
           σ); auto.
  apply (lds_write_ni W L op init xs lds Hlds).
Qed.

(* --- evaluation of the two imperative forms ----------------------------- *)

Lemma reducel_eval : forall n (op : exp num -> exp num -> exp num)
    (init : exp num)
    (xs : exp (ary '{n} num)) (cont : R -> comm) (tmp : acc num) rho,
  reducel op init xs cont tmp rho
  = cont (reduce op init xs) (update rho tmp (reduce op init xs)).
Proof.
  intros n op init xs cont tmp rho.
  unfold reducel, new. cbv beta.
  rewrite seq_assoc.
  change tmp with (@acc' num tmp).
  rewrite (reduce_aux_num n num op init xs tmp).
  unfold seq. rewrite assign_num. cbv beta.
  rewrite read_exp_update_eq. reflexivity.
Qed.

Lemma lds_reduce_eval : forall W L (op : R -> R -> R) (init : R)
    (xs : exp (ary '{W * L} num)) (cont : R -> comm)
    (lds : acc (ary '{W} num)) (tmp : acc num),
  (forall w w' : fin W, w <> w' -> lds|{w} <> lds|{w'}) ->
  (forall w : fin W, tmp <> lds|{w}) ->
  forall rho,
    lds_reduce op init xs cont lds tmp rho
    = cont (ffold op init (fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block w l])))
           (update
              (seqfor (fun w : fin W =>
                 lds|{w} |:= ffold op init (fun l : fin L => xs|[fin_block w l])) rho)
              tmp
              (ffold op init (fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block w l])))).
Proof.
  intros W L op init xs cont lds tmp Hlds Htmp rho.
  set (c := fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block w l])).
  unfold lds_reduce, lds_write_phase.
  assert (Ew : seqfor (fun w : fin W => lds_lane op init xs w (lds|{w}))
             = seqfor (fun w : fin W => lds|{w} |:= c w)).
  { apply seqfor_extensionality. intro w. unfold c. cbv beta. apply lds_lane_eq. }
  rewrite Ew.
  rewrite <- seq_fold.
  set (rho1 := seqfor (fun w : fin W => lds|{w} |:= c w) rho).
  assert (Hread : forall w, read_exp rho1 (lds|{w}) = c w).
  { intro w. unfold rho1. apply (seqfor_assigns_val W (fun w => lds|{w}) c Hlds). }
  rewrite <- seq_fold.
  rewrite (lds_combine_val W op init lds c tmp rho1 Htmp Hread).
  cbv beta. rewrite read_exp_update_eq. reflexivity.
Qed.

(* --- deliverable 3 (main): the LDS reduction implements [reducel] -------- *)

(* Side conditions, read against the hardware:
   - Hassoc/Hunit: the reduction operator is associative with left unit
     (discharged for [add] from the Reals library below);
   - Hlds: distinct LDS slots are distinct paths (true for the printer's
     fresh slot allocation);
   - Htmp: the result cell is not an LDS slot;
   - Hframe: the continuation does not observe the LDS scratch (the
     standard DPIA freshness discipline; cf. [not_using_a] in DPIA_Rules).
   Conclusion: on every path outside the LDS scratch, the LDS reduction
   agrees with the reference [reducel] skeleton. *)
Theorem lds_reduce_correct : forall W L (op : exp num -> exp num -> exp num)
    (init : exp num) (xs : exp (ary '{W * L} num)) (cont : R -> comm)
    (lds : acc (ary '{W} num)) (tmp : acc num),
  (forall a b c, op a (op b c) = op (op a b) c) ->
  (forall a, op init a = a) ->
  (forall w w' : fin W, w <> w' -> lds|{w} <> lds|{w'}) ->
  (forall w : fin W, tmp <> lds|{w}) ->
  (forall e rho1 rho2 q,
     (forall p, (forall w : fin W, p <> lds|{w}) -> rho1 p = rho2 p) ->
     (forall w : fin W, q <> lds|{w}) ->
     cont e rho1 q = cont e rho2 q) ->
  forall rho q, (forall w : fin W, q <> lds|{w}) ->
    lds_reduce op init xs cont lds tmp rho q
    = reducel op init xs cont tmp rho q.
Proof.
  intros W L op init xs cont lds tmp Hass Hunit Hlds Htmp Hframe rho q Hq.
  rewrite (lds_reduce_eval W L op init xs cont lds tmp Hlds Htmp rho).
  rewrite (reducel_eval (W * L) op init xs cont tmp rho).
  assert (Hfe : ffold op init (fun w : fin W => ffold op init (fun l : fin L => xs|[fin_block w l]))
              = reduce op init xs).
  { symmetry. apply (lds_chunk_reduce W L op init xs Hass Hunit). }
  rewrite Hfe. apply Hframe; [| exact Hq].
  intros p Hp.
  destruct (path_eqb tmp p) eqn:E.
  - apply path_eqb_eq in E. subst p. rewrite !update_eq. reflexivity.
  - apply path_eqb_neq in E. rewrite !update_neq; auto.
    apply (seqfor_assigns_frame W (fun w => lds|{w})). exact Hp.
Qed.

(* Closed instance for [add]: the LDS sum implements [suml]. *)
Theorem lds_sum_correct : forall W L
    (xs : exp (ary '{W * L} num)) (cont : R -> comm)
    (lds : acc (ary '{W} num)) (tmp : acc num),
  (forall w w' : fin W, w <> w' -> lds|{w} <> lds|{w'}) ->
  (forall w : fin W, tmp <> lds|{w}) ->
  (forall e rho1 rho2 q,
     (forall p, (forall w : fin W, p <> lds|{w}) -> rho1 p = rho2 p) ->
     (forall w : fin W, q <> lds|{w}) ->
     cont e rho1 q = cont e rho2 q) ->
  forall rho q, (forall w : fin W, q <> lds|{w}) ->
    lds_reduce add zero xs cont lds tmp rho q
    = suml xs cont tmp rho q.
Proof.
  intros W L xs cont lds tmp Hlds Htmp Hframe rho q Hq.
  unfold suml.
  apply (lds_reduce_correct W L add zero xs cont lds tmp); auto.
  - exact add_assocA.
  - exact add_zero_lA.
Qed.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                               *)
(* -------------------------------------------------------------------------- *)

Print Assumptions mkvParl3_strip.
Print Assumptions AmkvPar3.
Print Assumptions mkvParl3_flat_perm.
Print Assumptions mkvParl3_grid_perm.
Print Assumptions hierpar_safe_acc'.
Print Assumptions ffold_chunk.
Print Assumptions ffold_perm.
Print Assumptions lds_chunk_reduce.
Print Assumptions lds_chunk_reduce_perm.
Print Assumptions lds_write_schedule.
Print Assumptions lds_reduce_correct.
Print Assumptions lds_sum_correct.
