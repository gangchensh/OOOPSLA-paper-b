(* Tiling (split/join) rewrite rules for the DPIA rule layer.

   This file adds the G0 tiling rules on top of [DPIA_Rules.v]:

   - Index embeddings [fin_tile_lo]/[fin_tile_hi] and a cast [fin_tile_cast]
     mediate between [fin w] and [fin (p + q)] (needed because [p + S q] is
     not convertible to [S (p + q)] while [seqfor] peels from the end).
   - [seqfor_tile_app]: a sequential loop over [fin w] with [w = p + q]
     decomposes into the prefix loop followed by the suffix loop.
   - [seqfor_split] (core): a sequential loop over [fin (n * m)] equals the
     outer block loop over [fin n] of inner intra-block loops over [fin m],
     with the flat index reconstructed as [idx_2d_to_1d i j] (value i*m+j).
   - [idx_split]/[idx_join]/[join_split]/[split_join]: the type-changing
     reindexing maps [split]/[join] of [Proof_CodeGen.v] are inverse, and
     indexing a split array at (i, j) is indexing the flat array at i*m+j.
   - [mkvSeql_tiled]/[AmkvSeq_tiled]/[AmkvSeq_split]: tiling versions of the
     [AmkvSeq] constructor rule.
   - [reducel_tiled]/[A_reduce_num_tiled]: loop-nest reindexing of the
     reduction skeleton (order preserving; no algebraic side conditions).

   All proofs are [Qed]; only the standard classical axioms already used by
   [DPIA_Rules.v] may appear (proof irrelevance / functional extensionality).
*)

Require Import Logic.FunctionalExtensionality.
Require Import List Reals String Nat Bool Arith Lra Lia.
Require Import Coq.Logic.ProofIrrelevance.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.DPIA_Rules.
Import Proof_CodeGen.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Finite-index embeddings for block decomposition                            *)
(* -------------------------------------------------------------------------- *)

(* Transport a fin along an equality of bounds. *)
Definition fin_tile_cast {a b : nat} (H : a = b) (k : fin a) : fin b :=
  eq_rect a fin k b H.

Lemma fin2nat_tile_cast : forall (a b : nat) (H : a = b) (k : fin a),
  fin2nat (fin_tile_cast H k) = fin2nat k.
Proof. intros a b H k. destruct H. reflexivity. Qed.

(* Prefix embedding: fin p -> fin (p + q), value preserved. *)
Definition fin_tile_lo {p q : nat} (k : fin p) : fin (p + q) :=
  @nat2fin (p + q) (fin2nat k)
    (Nat.lt_le_trans _ _ _ (fin_proof k) (Nat.le_add_r p q)).

Lemma fin2nat_tile_lo : forall (p q : nat) (k : fin p),
  fin2nat (@fin_tile_lo p q k) = fin2nat k.
Proof. intros p q k. destruct k. reflexivity. Qed.

(* Suffix embedding: fin q -> fin (p + q), value shifted by p. *)
Definition fin_tile_hi {p q : nat} (k : fin q) : fin (p + q) :=
  @nat2fin (p + q) (p + fin2nat k)
    (proj1 (Nat.add_lt_mono_l _ _ p) (fin_proof k)).

Lemma fin2nat_tile_hi : forall (p q : nat) (k : fin q),
  fin2nat (@fin_tile_hi p q k) = p + fin2nat k.
Proof. intros p q k. destruct k. reflexivity. Qed.

(* -------------------------------------------------------------------------- *)
(* Loop decomposition lemmas                                                  *)
(* -------------------------------------------------------------------------- *)

(* A loop can be re-indexed along an equality of bounds. *)
Lemma seqfor_tile_cast : forall (a b : nat) (H : a = b) (f : fin a -> comm),
  seqfor f = seqfor (fun k : fin b => f (fin_tile_cast (eq_sym H) k)).
Proof.
  intros a b H f. destruct H. reflexivity.
Qed.

(* A one-step loop is its body at index 0. *)
Lemma seqfor_1 : forall (f : fin 1 -> comm), seqfor f = f '[0].
Proof.
  intros f. rewrite (seqfor_Sn f).
  change (seqfor (fun i : fin 0 => f FS[i])) with skip.
  rewrite skip_l. reflexivity.
Qed.

(* Append split: looping over [w = p + q] is the prefix loop over the first
   [p] indices followed by the suffix loop over the last [q] indices.
   The equation is explicit because [p + S q] does not reduce to [S (p + q)]
   (addition recurses on its left argument), so [seqfor_Sn] cannot fire on
   [fin (p + S q)] directly. *)
Lemma seqfor_tile_app : forall (w p q : nat) (H : w = p + q) (f : fin w -> comm),
  seqfor f =
  seqfor (fun i : fin p => f (fin_tile_cast (eq_sym H) (fin_tile_lo i))) ';
  seqfor (fun j : fin q => f (fin_tile_cast (eq_sym H) (fin_tile_hi j))).
Proof.
  intros w p q. revert w p. induction q as [| q' IHq']; intros w p H f.
  - (* q = 0: the suffix loop is empty *)
    change (seqfor (fun j : fin 0 => f (fin_tile_cast (eq_sym H) (fin_tile_hi j))))
      with skip.
    rewrite skip_r.
    assert (H' : w = p) by (rewrite H; apply Nat.add_0_r).
    rewrite (seqfor_tile_cast H' f).
    apply seqfor_extensionality. intro i. f_equal. apply fin_eq.
    rewrite ?fin2nat_tile_cast, ?fin2nat_tile_lo. reflexivity.
  - (* q = S q': expose the last flat index via w = S (p + q') *)
    assert (H1 : w = S (p + q')) by (rewrite H, Nat.add_succ_r; reflexivity).
    rewrite (seqfor_tile_cast H1 f).
    rewrite (seqfor_Sn (fun k : fin (S (p + q')) => f (fin_tile_cast (eq_sym H1) k))).
    cbv beta.
    rewrite (IHq' (p + q') p eq_refl
               (fun i : fin (p + q') => f (fin_tile_cast (eq_sym H1) FS[i]))).
    cbv beta.
    rewrite (seqfor_Sn (fun j : fin (S q') => f (fin_tile_cast (eq_sym H) (fin_tile_hi j)))).
    cbv beta. rewrite seq_assoc. f_equal.
    + f_equal.
      * apply seqfor_extensionality. intro i. f_equal. apply fin_eq.
        rewrite ?fin2nat_tile_cast, ?fin2nat_fin2finS, ?fin2nat_tile_lo,
                ?fin2nat_fin2finS. reflexivity.
      * apply seqfor_extensionality. intro j. f_equal. apply fin_eq.
        rewrite ?fin2nat_tile_cast, ?fin2nat_fin2finS, ?fin2nat_tile_hi,
                ?fin2nat_fin2finS. reflexivity.
    + f_equal. apply fin_eq.
      rewrite ?fin2nat_tile_cast, ?fin2nat_tile_hi. reflexivity.
Qed.

(* Core loop-tiling theorem: a sequential loop over [fin (n * m)] is the
   outer block loop over [fin n] of inner intra-block loops over [fin m];
   the flat index of block [i], offset [j] is [idx_2d_to_1d i j] (value
   i*m+j).  Proved by induction on [n]: [S n' * m] is convertible to
   [m + n' * m] (multiplication recurses on its left argument), so the
   append split peels off the *first* block and the IH handles the rest. *)
Theorem seqfor_split : forall (n m : nat) (f : fin (n * m) -> comm),
  seqfor f =
  seqfor (fun i : fin n => seqfor (fun j : fin m => f (idx_2d_to_1d i j))).
Proof.
  intros n m f. revert f. induction n as [| n' IHn']; intros f.
  - reflexivity.
  - rewrite (@seqfor_tile_app (S n' * m) m (n' * m) eq_refl f).
    erewrite (IHn').
    cbv beta.
    rewrite (@seqfor_tile_app (S n') 1 n' eq_refl
               (fun i : fin (S n') =>
                  seqfor (fun j : fin m => f (idx_2d_to_1d i j)))).
    cbv beta.
    erewrite (seqfor_1).
    cbv beta. f_equal.
    + apply seqfor_extensionality. intro j. f_equal. apply fin_eq.
      rewrite ?fin2nat_tile_cast, ?fin2nat_tile_lo.
      unfold idx_2d_to_1d. simpl.
      rewrite ?fin2nat_tile_cast, ?fin2nat_tile_lo. simpl. lia.
    + apply seqfor_extensionality. intro i.
      apply seqfor_extensionality. intro j. f_equal. apply fin_eq.
      rewrite ?fin2nat_tile_cast, ?fin2nat_tile_hi.
      unfold idx_2d_to_1d. simpl.
      rewrite ?fin2nat_tile_cast, ?fin2nat_tile_hi. simpl. lia.
Qed.

(* -------------------------------------------------------------------------- *)
(* split/join: type-changing reindexing between flat and nested arrays        *)
(* -------------------------------------------------------------------------- *)

(* Indexing a split array at (i, j) is indexing the flat array at i*m+j. *)
Lemma idx_split : forall (n m : nat) (d : data)
  (e : exp (ary '{n*m} d)) (i : fin n) (j : fin m),
  (split e)|[i]|[j] = e|[idx_2d_to_1d i j].
Proof.
  intros. unfold split, mkvSeq, idx.
  rewrite v_idx_mk_vec, v_idx_mk_vec. reflexivity.
Qed.

(* Indexing a joined array at [k] uses the div/mod decomposition of [k]. *)
Lemma idx_join : forall (n m : nat) (d : data)
  (e : exp (ary '{n} (ary '{m} d))) (k : fin (n*m)),
  (join e)|[k] = let '(i, j) := idx_1d_to_2d k in e|[i]|[j].
Proof.
  intros. unfold join, mkvSeq, idx.
  rewrite v_idx_mk_vec. destruct (idx_1d_to_2d k). reflexivity.
Qed.

(* [join] after [split] is the identity. *)
Lemma join_split : forall (n m : nat) (d : data) (e : exp (ary '{n*m} d)),
  join (split e) = e.
Proof.
  intros n m d e.
  apply (@vector_eq_v_idx _ _ _ _ (exp_default d)). intro k.
  change ((join (split e))|[k] = e|[k]).
  rewrite idx_join.
  destruct (idx_1d_to_2d k) as [i j] eqn:E. cbv beta iota.
  rewrite idx_split. f_equal.
  assert (Hi : i = fst (idx_1d_to_2d k)) by (rewrite E; reflexivity).
  assert (Hj : j = snd (idx_1d_to_2d k)) by (rewrite E; reflexivity).
  rewrite Hi, Hj. apply idx_2d_to_1d_after_idx_1d_to_2d.
Qed.

(* [split] after [join] is the identity. *)
Lemma split_join : forall (n m : nat) (d : data)
  (e : exp (ary '{n} (ary '{m} d))),
  split (join e) = e.
Proof.
  intros n m d e.
  apply (@vector_eq_v_idx _ _ _ _ (exp_default (ary '{m} d))). intro i.
  apply (@vector_eq_v_idx _ _ _ _ (exp_default d)). intro j.
  change ((split (join e))|[i]|[j] = e|[i]|[j]).
  rewrite idx_split. rewrite idx_join.
  rewrite idx_1d_to_2d_after_idx_2d_to_1d. cbv beta iota. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Constructor tiling rules                                                   *)
(* -------------------------------------------------------------------------- *)

(* Tiling version of the [mkvSeql] combinator: the flat loop over the
   element accessors of [a] decomposes into a block loop of block loops. *)
Lemma mkvSeql_tiled : forall (n m : nat) (d : data)
  (f : fin (n*m) -> acc d -> comm) (a : acc (ary '{n*m} d)),
  mkvSeql f a =
  seqfor (fun i : fin n =>
    seqfor (fun j : fin m => f (idx_2d_to_1d i j) (a|{idx_2d_to_1d i j}))).
Proof.
  intros. unfold mkvSeql. apply seqfor_split.
Qed.

(* Tiling version of [AmkvSeq]: materialising a flat array [mkvSeq f] into a
   flat accumulator is the nested block loop of point assignments. *)
Lemma AmkvSeq_tiled : forall (n m : nat) (d : data)
  (f : fin (n*m) -> exp d) (a : acc (ary '{n*m} d)),
  A(a, mkvSeq f) =
  seqfor (fun i : fin n =>
    seqfor (fun j : fin m => A(a|{idx_2d_to_1d i j}, f (idx_2d_to_1d i j)))).
Proof.
  intros n m d f a. rewrite AmkvSeq. rewrite mkvSeql_tiled. reflexivity.
Qed.

(* Constructor split rule for a nested accumulator: materialising
   [split (mkvSeq f)] into a nested accumulator is the nested [mkvSeql]
   of point assignments. *)
Lemma AmkvSeq_split : forall (n m : nat) (d : data)
  (f : fin (n*m) -> exp d) (a : acc (ary '{n} (ary '{m} d))),
  A(a, split (mkvSeq f)) =
  mkvSeql (fun i o => mkvSeql (fun j o' => A(o', f (idx_2d_to_1d i j))) o) a.
Proof.
  intros n m d f a. unfold A, mkvSeql. rewrite assign_ary.
  apply seqfor_extensionality. intro i. cbv beta. rewrite assign_ary.
  apply seqfor_extensionality. intro j. cbv beta. f_equal.
  rewrite idx_split. unfold mkvSeq, idx. rewrite v_idx_mk_vec. reflexivity.
Qed.

(* -------------------------------------------------------------------------- *)
(* Reduction tiling (bonus)                                                   *)
(* -------------------------------------------------------------------------- *)

(* The [reducel] skeleton over a flat array of size [n * m] reindexes to a
   block loop of block loops.  This is a pure loop-nest reindexing: the
   iteration order is preserved, so no algebraic side condition on [op] is
   needed. *)
Lemma reducel_tiled : forall (n m : nat) (s t : data)
  (op : exp s -> exp t -> exp t) (init : exp t)
  (xs : exp (ary '{n*m} s)) (cont : exp t -> comm) (out : acc t),
  reducel op init xs cont out =
  new (fun tmp : acc t =>
    (tmp |:= init) ';
    (seqfor (fun i : fin n => seqfor (fun j : fin m => fun rho : env =>
       assign tmp (op (xs|[idx_2d_to_1d i j]) (read_exp rho tmp)) rho)) ';
     (fun rho : env => cont (read_exp rho tmp) rho))) out.
Proof.
  intros n m s t op init xs cont out.
  unfold reducel, new. cbv beta. rewrite seqfor_split. reflexivity.
Qed.

(* Tiling version of [A_reduce_num]: the reduction assigned to a scalar
   accumulator is the tiled [reducel] skeleton followed by the store. *)
Lemma A_reduce_num_tiled : forall (n m : nat) (s : data)
  (op : exp s -> exp num -> exp num) (init : exp num)
  (xs : exp (ary '{n*m} s)) (p : path),
  A(acc' p, reduce op init xs) =
  new (fun tmp : acc num =>
    (tmp |:= init) ';
    (seqfor (fun i : fin n => seqfor (fun j : fin m => fun rho : env =>
       assign tmp (op (xs|[idx_2d_to_1d i j]) (read_exp rho tmp)) rho)) ';
     (fun rho : env => ((acc' p) |:= read_exp rho tmp) rho))) (acc' p).
Proof.
  intros n m s op init xs p. rewrite A_reduce_num. rewrite reducel_tiled.
  reflexivity.
Qed.
