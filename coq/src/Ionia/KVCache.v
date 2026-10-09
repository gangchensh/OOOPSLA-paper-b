(* DPIA-style Leibniz equivalence proofs for KV-cached bounded autoregressive
   generation (milestone N4.1 of the NLP/LLM extension, cf.
   doc/N4立项分析_20260911.md §1) in the route-A R-based expression model.

   Key design insight (per the milestone analysis): deployed autoregressive
   generation always has a static upper bound (max_new_tokens), so a bounded
   for-loop with If-guarded writes expresses the semantics without any while
   primitive; EOS early-exit is modelled by writing a sentinel once the done
   flag is set, keeping performance and semantics separate.

   Delivered here (all closed with [Qed], no Admitted/Axiom):

   Part 1 — the KV-cache core theorem.
     [AttnQ]: single-query attention over a length-(t+1) prefix (the
       generation-step shape: query = current token, keys/values = prefix);
       the causal mask is trivially all-keep for the last position, so no
       mask term is needed.  [AttnQ_cell_last] ties it to the full causal
       cell of Ionia.Attention_DPIA: the last row of
       [Attention_cell Q K V] is exactly [AttnQ] of the last query row.
     [cachefill]: filling the K/V caches (whole-array writes, which unfold
       to slot-by-slot seqfor loops — [cachefill_loops]).
     The prefix-consistency lemmas [fill_read]/[fill_other] (built on
       [access_seqfor_ary_eq_general]/[access_seqfor_ary_neq_general],
       i.e. the access_assign/assign_assign family) show that slots already
       written are never disturbed.
     [kv_cache_equiv]: attention computed from the cached K/V read back out
       of the environment equals attention over the recomputed prefix.
     [A_AttnQ_cached]: the command-level form — the cached attention command
       observed at an output path equals the functional recompute.

   Part 2 — bounded autoregressive generation.
     [gen_trace]/[gen_at]: the functional token stream (snoc recursion;
       each step: simplified MHA over the prefix KV, then [emit]);
       [gk]/[gv]/[gout]: the If-guarded (sentinel) per-step cache/output
       values; [gen_outputs]: the length-T output array.
     [genstep]: one imperative step — read the state buffer, If-guarded
       writes of the K/V cache slots and the output slot, attention over the
       cache PREFIX read back from the environment, state update.
     [genstep_correct]/[genloop_inv]: the step and loop invariants — after n
       steps the state buffer holds [gen_at n], cache slot j < n holds
       [gk j]/[gv j], output slot j < n holds [gout j].
     [A_BoundedGenerate]: end-to-end — the T-step loop observed at an output
       path equals the functional [gen_outputs].  Note the premises are only
       path disjointness of the four buffers; no freshness/undefinedness of
       the incoming environment is needed, because every read happens after
       the corresponding write.

   Part 3 — small-instance spot checks (T = 4 scale). *)

From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
(* Reals must be imported before [Import Proof_CodeGen] (cf. Ops_BatchNorm). *)
From Stdlib Require Import Reals Lia.
From Stdlib Require Import Classical_Prop.
Import Proof_CodeGen.
(* [Softmax1d]. *)
Require Import Ionia.LeNet5_Functional.
(* [Attention_cell], [attn_scale], [BMatMul2d]; transitively MatMul2d,
   Transpose2d, CausalMask2d, Mulc2d, Softmax2d. *)
Require Import Ionia.Attention_DPIA.
(* explicit re-export of the T1 operators (CausalMask2d, MatMul2d,
   Transpose2d) and [Mulc2d]. *)
Require Import Ionia.Ops_Transformer.
Require Import Ionia.Ops_Elementwise.
(* [Softmax2d]. *)
Require Import Ionia.Ops_Reduce.
(* [idxAcc_acc'_at]. *)
Require Import Ionia.Seq2Seq_DPIA.
From Stdlib Require Import String.
Open Scope string_scope.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Helpers                                                                     *)
(* -------------------------------------------------------------------------- *)

(* Same base, different index: the slot paths differ. *)
Lemma aryidx_neq_idx : forall (n : nat) (i j : fin n) (a : path),
  fin2nat i <> fin2nat j -> AryIdx i a <> AryIdx j a.
Proof.
  intros n i j a H Hc. apply AryIdx_eq in Hc. destruct Hc as [_ [H2 _]].
  contradiction.
Qed.

(* Different bases: the slot paths differ. *)
Lemma aryidx_neq_base : forall (n m : nat) (i : fin n) (j : fin m) (a b : path),
  a <> b -> AryIdx i a <> AryIdx j b.
Proof.
  intros n m i j a b H Hc. apply AryIdx_eq in Hc. destruct Hc as [_ [_ H3]].
  contradiction.
Qed.

(* read_exp of a defined accumulator is the stored value. *)
Lemma read_exp_eq : forall (d : data) (rho : env) (a : acc d) (e : exp d),
  access rho a = Some e -> read_exp rho a = e.
Proof. intros d rho a e H. destruct d; simpl in *; rewrite H; reflexivity. Qed.

(* An If-guarded pair of assignments is one assignment of the conditional
   value (the [Aif1] rule read right-to-left). *)
Lemma If_assign_merge : forall (d : data) (a : acc d) (b : bool) (e1 e2 : exp d),
  If b (a |:= e1) (a |:= e2) = a |:= (if b then e1 else e2).
Proof.
  intros.
  change (a |:= (if b then e1 else e2)) with (A(a, if b then e1 else e2)).
  change (a |:= e1) with (A(a, e1)).
  change (a |:= e2) with (A(a, e2)).
  symmetry. apply Aif1.
Qed.

(* fin2nat of the snoc-last index. *)
Lemma fin2nat_ltS : forall (m : nat), fin2nat ('[m]) = m.
Proof. intro m. unfold ltS. rewrite fin2nat_exist. reflexivity. Qed.

(* Slot path of an acc'-generated buffer, in the exact implicit-argument
   shape produced by reducing [in_acc] ([fle2nat (fle_self n)], not [n]) —
   keyed rewriting with [idxAcc_acc'_at] fails on the reduced form. *)
Lemma slot_path_raw : forall (n : nat) (d : data) (p : path)
    (i : fin (fle2nat (fle_self n))),
  @idxAcc (fle2nat (fle_self n)) d (@acc' (@ary n (fle_self n) d) p) i
  = @acc' d (@AryIdx (fle2nat (fle_self n)) i p).
Proof.
  intros. unfold idxAcc. rewrite acc'_ary. apply v_idx_mk_vec.
Qed.

(* Same slot-path fact for [c_idx] (the accessor produced by [access_ary]). *)
Lemma c_idx_acc'_raw : forall (n : nat) (d : data) (p : path)
    (i : fin (fle2nat (fle_self n))),
  @c_idx (fle2nat (fle_self n)) d (@acc' (@ary n (fle_self n) d) p) i
  = @acc' d (@AryIdx (fle2nat (fle_self n)) i p).
Proof. intros. apply slot_path_raw. Qed.

(* One level of read-back through a whole-array access: from
   access rho (acc' base) = Some G to the slot value [idx G i]. *)
Lemma access_acc'_level : forall (n : nat) (d : data) (base : path) (rho : env)
    (G : exp (ary '{n} d)) (i : fin n),
  access rho (acc' base : acc (ary '{n} d)) = Some G ->
  access rho (acc' (AryIdx i base) : acc d) = Some (idx G i).
Proof.
  intros n d base rho G i H. rewrite access_ary in H.
  (* [access_ary] produces the binder type [fin (fle2nat (fle_self n))];
     normalise by conversion so the mkoptvec lemmas apply. *)
  change (mkoptvec (fun i0 : fin n =>
            access rho (c_idx (acc' base : acc (ary '{n} d)) i0)) = Some G) in H.
  assert (Hnn : mkoptvec (fun i0 : fin n =>
                  access rho (c_idx (acc' base : acc (ary '{n} d)) i0)) <> None).
  { rewrite H. discriminate. }
  pose proof (idx_opt_mkoptvec _ _ i Hnn) as H1.
  rewrite H in H1. rewrite idx_opt_Some_idx in H1.
  assert (Hc : c_idx (acc' base : acc (ary '{n} d)) i = acc' (AryIdx i base)).
  { unfold c_idx. rewrite acc'_ary. apply v_idx_mk_vec. }
  rewrite Hc in H1. symmetry. exact H1.
Qed.

(* mkoptvec of a Some-valued function is the whole vector (any length). *)
Lemma mkoptvec_some_all : forall (n : nat) (d : data) (f : fin n -> exp d),
  mkoptvec (fun i : fin n => Some (f i)) = Some (mk_vec f).
Proof.
  intros n d f. destruct n as [|n'].
  - reflexivity.
  - apply mkoptvec_mk_vec.
Qed.

(* Pointwise equality of array expressions (idx form of [vector_eq_v_idx]). *)
Lemma exp_ary_eq : forall (dk : nat) (a b : exp (ary '{dk} num)),
  (forall i : fin dk, idx a i = idx b i) -> a = b.
Proof.
  intros dk a b H.
  apply (proj2 (@vector_eq_v_idx (exp num) dk a b (exp_default num))).
  intro i. exact (H i).
Qed.

(* -------------------------------------------------------------------------- *)
(* Single-query attention over a prefix (the generation-step cell)            *)
(* -------------------------------------------------------------------------- *)

(* Dot product of two dk-vectors. *)
Definition dotr {dk : nat} (u v : exp (ary '{dk} num)) : exp num :=
  sum (mkvSeq (fun dd : fin dk => mul (idx u dd) (idx v dd))).

(* Scaled scores of query [q] against the K rows (scale on the right, matching
   [Mulc2d] inside [Attention_cell]). *)
Definition attn_scores {dk n : nat}
  (q : exp (ary '{dk} num)) (K : exp (ary '{n} (ary '{dk} num)))
  : exp (ary '{n} num) :=
  mkvSeq (fun j : fin n => mul (dotr q (idx K j)) (attn_scale dk)).

(* softmax(q K^T / sqrt(d)) V for a single query — the last row of the causal
   attention cell (all prefix keys are visible from the last position, so the
   causal mask is the identity there). *)
Definition AttnQ {dk n : nat}
  (q : exp (ary '{dk} num))
  (K V : exp (ary '{n} (ary '{dk} num))) : exp (ary '{dk} num) :=
  mkvSeq (fun dd : fin dk =>
    sum (mkvSeq (fun j : fin n =>
      mul (idx (Softmax1d (attn_scores q K)) j) (idx (idx V j) dd)))).

(* Imperative counterpart: per-component reduction (suml skeleton). *)
Definition AttnQ_comm {dk n : nat}
  (q : exp (ary '{dk} num))
  (K V : exp (ary '{n} (ary '{dk} num)))
  (out : acc (ary '{dk} num)) : comm :=
  mkvSeql (fun dd od =>
    suml (mkvSeq (fun j : fin n =>
             mul (idx (Softmax1d (attn_scores q K)) j) (idx (idx V j) dd)))
         (fun r => od |:= r) od) out.

Lemma A_AttnQ : forall (dk n : nat)
  (q : exp (ary '{dk} num))
  (K V : exp (ary '{n} (ary '{dk} num)))
  (out : acc (ary '{dk} num)),
  A(out, AttnQ q K V) = AttnQ_comm q K V out.
Proof.
  intros. unfold AttnQ, AttnQ_comm.
  rewrite AmkvSeq.
  apply seqfor_extensionality. intro dd.
  rewrite A_sum_acc. reflexivity.
Qed.

(* Bridge: the last row of the full causal attention cell (with mask) is the
   single-query attention of the last query row. *)
Lemma AttnQ_cell_last : forall (dk : nat) (Hdk : dk > 0) (n : nat)
  (Q K V : exp (ary '{S n} (ary '{dk} num))),
  idx (Attention_cell Q K V) (fin_last n) = AttnQ (idx Q (fin_last n)) K V.
Proof.
  intros dk Hdk n Q K V.
  (* every prefix index passes the causal test at the last row *)
  assert (Hmask : forall k : fin (S n),
    (fin2nat k <=? fin2nat (fin_last n))%nat = true).
  { intro k. rewrite fin_last_correct. apply Nat.leb_le.
    pose proof (fin_proof k). lia. }
  (* the masked score row equals the AttnQ score row *)
  assert (Hrow : forall k : fin (S n),
    idx (idx (CausalMask2d (Mulc2d (attn_scale dk) (MatMul2d Q (Transpose2d K))))
             (fin_last n)) k
    = idx (attn_scores (idx Q (fin_last n)) K) k).
  { intro k.
    unfold CausalMask2d. rewrite !idx_mkvSeq by lia.
    rewrite (Hmask k).
    unfold Mulc2d. rewrite !idx_mkvSeq by lia.
    unfold MatMul2d. rewrite !idx_mkvSeq by lia.
    unfold attn_scores. rewrite idx_mkvSeq by lia.
    unfold dotr. f_equal. f_equal. f_equal.
    apply functional_extensionality. intro dd.
    unfold Transpose2d. rewrite !idx_mkvSeq by lia.
    reflexivity. }
  apply exp_ary_eq. intro dd.
  unfold Attention_cell. cbv zeta beta.
  set (M := CausalMask2d (Mulc2d (attn_scale dk) (MatMul2d Q (Transpose2d K)))).
  replace (MatMul2d (Softmax2d M) V)
    with (mkvSeq (fun i : fin (S n) => mkvSeq (fun j : fin dk =>
      sum (mkvSeq (fun k : fin (S n) =>
        mul (idx (idx (Softmax2d M) i) k) (idx (idx V k) j)))))) by reflexivity.
  rewrite idx_mkvSeq by lia. rewrite idx_mkvSeq by lia.
  unfold AttnQ. rewrite idx_mkvSeq by lia.
  f_equal. f_equal. apply functional_extensionality. intro k. f_equal.
  replace (Softmax2d M)
    with (mkvSeq (fun b : fin (S n) => mkvSeq (fun j : fin (S n) =>
      div (pExp (idx (idx M b) j))
          (sum (mkvSeq (fun i : fin (S n) => pExp (idx (idx M b) i)))))))
    by reflexivity.
  rewrite idx_mkvSeq by lia. rewrite idx_mkvSeq by lia.
  replace (Softmax1d (attn_scores (idx Q (fin_last n)) K))
    with (mkvSeq (fun i : fin (S n) =>
      div (pExp (idx (attn_scores (idx Q (fin_last n)) K) i))
          (sum (mkvSeq (fun j : fin (S n) =>
            pExp (idx (attn_scores (idx Q (fin_last n)) K) j))))))
    by reflexivity.
  rewrite idx_mkvSeq by lia.
  f_equal.
  + f_equal. apply Hrow.
  + f_equal. f_equal. apply functional_extensionality. intro i.
    f_equal. apply Hrow.
Qed.

(* -------------------------------------------------------------------------- *)
(* Part 1: KV-cache fill and the cache/recompute equivalence                  *)
(* -------------------------------------------------------------------------- *)

Section KVCache.

  (* Cache length L, key dimension dk, per-slot K/V values (however computed:
     the fill correctness is independent of where the values come from). *)
  Context (L dk : nat).
  Context (fkv fvv : fin L -> exp (ary '{dk} num)).
  Context (kcp vcp : path).
  Context (Hkv : kcp <> vcp).

  (* The fill commands: whole-array writes of the value vectors. *)
  Definition kfill : comm :=
    (acc' kcp : acc (ary '{L} (ary '{dk} num))) |:= mkvSeq fkv.
  Definition vfill : comm :=
    (acc' vcp : acc (ary '{L} (ary '{dk} num))) |:= mkvSeq fvv.
  Definition cachefill : comm := kfill '; vfill.

  (* The fills are exactly the slot-by-slot seqfor loops (the shape of the
     generated imperative code). *)
  Lemma cachefill_loops :
    cachefill =
    seqfor (fun i : fin L => ((acc' kcp : acc (ary '{L} (ary '{dk} num)))|{i} |:= fkv i)) ';
    seqfor (fun i : fin L => ((acc' vcp : acc (ary '{L} (ary '{dk} num)))|{i} |:= fvv i)).
  Proof.
    unfold cachefill, kfill, vfill. f_equal.
    - destruct L as [|L'].
      + rewrite assign_ary. reflexivity.
      + rewrite assign_ary. apply seqfor_extensionality. intro i.
        rewrite idx_mkvSeq by lia. reflexivity.
    - destruct L as [|L'].
      + rewrite assign_ary. reflexivity.
      + rewrite assign_ary. apply seqfor_extensionality. intro i.
        rewrite idx_mkvSeq by lia. reflexivity.
  Qed.

  (* Prefix consistency, read direction: after writing the whole vector,
     every slot reads back its value — already-written slots are not
     disturbed by other slots' writes (the access_assign family). *)
  Lemma fill_read : forall (base : path) (vals : fin L -> exp (ary '{dk} num))
    (m : fin L) (rho : env),
    access (((acc' base : acc (ary '{L} (ary '{dk} num))) |:= mkvSeq vals) rho)
           ((acc' base : acc (ary '{L} (ary '{dk} num)))|{m})
    = Some (vals m).
  Proof.
    intros base vals m rho. destruct L as [|L'].
    - destruct m as [x Hx]. lia.
    - rewrite (idxAcc_acc'_at (ary '{dk} num) base m).
      rewrite assign_ary.
      transitivity (access (seqfor (fun j : fin (S L') =>
                              assign (acc' (AryIdx j base)) ((mkvSeq vals)|[j])) rho)
                           (acc' (AryIdx m base) : acc (ary '{dk} num))).
      2: { rewrite (@access_seqfor_ary_eq_general
                      (ary '{dk} num) base rho (S L') (S L')
                      (fun j : fin (S L') => j) (mkvSeq vals)
                      (fun j k H => H)
                      (fun p1 p2 e' x' H => access_assign_neq (ary '{dk} num) e' x' H)
                      (fun p1 e' x' => access_assign_eq (ary '{dk} num) e' x' eq_refl)
                      m).
           rewrite idx_mkvSeq by lia. reflexivity. }
      f_equal. f_equal.
      apply functional_extensionality. intro i. f_equal.
      apply (idxAcc_acc'_at (ary '{dk} num) base i).
  Qed.

  (* Prefix consistency, non-interference direction: filling one cache does
     not disturb the other cache's slots (assign_assign/access_assign_neq). *)
  Lemma fill_other : forall (base other : path), base <> other ->
    forall (vals : fin L -> exp (ary '{dk} num)) (m : fin L) (rho : env),
    access (((acc' base : acc (ary '{L} (ary '{dk} num))) |:= mkvSeq vals) rho)
           ((acc' other : acc (ary '{L} (ary '{dk} num)))|{m})
    = access rho ((acc' other : acc (ary '{L} (ary '{dk} num)))|{m}).
  Proof.
    intros base other Hbo vals m rho. destruct L as [|L'].
    - destruct m as [x Hx]. lia.
    - rewrite (idxAcc_acc'_at (ary '{dk} num) other m).
      rewrite assign_ary.
      transitivity (access (seqfor (fun j : fin (S L') =>
                              assign (acc' (AryIdx j base)) ((mkvSeq vals)|[j])) rho)
                           (acc' (AryIdx m other) : acc (ary '{dk} num))).
      2: { apply (@access_seqfor_ary_neq_general
                    (ary '{dk} num) base other rho (S L') (S L')
                    (fun j : fin (S L') => j) (mkvSeq vals)
                    Hbo (fun j k H => H)
                    (fun p1 p2 e' x' H => access_assign_neq (ary '{dk} num) e' x' H)). }
      f_equal. f_equal.
      apply functional_extensionality. intro i. f_equal.
      apply (idxAcc_acc'_at (ary '{dk} num) base i).
  Qed.

  (* After the full fill, every K slot holds its value ... *)
  Lemma cache_k : forall (m : fin L) (rho : env),
    access (cachefill rho) ((acc' kcp : acc (ary '{L} (ary '{dk} num)))|{m})
    = Some (fkv m).
  Proof.
    intros m rho. unfold cachefill, vfill. unfold seq.
    rewrite (fill_other (base:=vcp) (other:=kcp) (fun H : vcp = kcp => Hkv (eq_sym H)) fvv m (kfill rho)).
    apply fill_read.
  Qed.

  (* ... and so does every V slot. *)
  Lemma cache_v : forall (m : fin L) (rho : env),
    access (cachefill rho) ((acc' vcp : acc (ary '{L} (ary '{dk} num)))|{m})
    = Some (fvv m).
  Proof.
    intros m rho. unfold cachefill. unfold seq.
    apply fill_read.
  Qed.

  (* Prefix lifting: a fin (S t) index into the length-L cache (t < L). *)
  Definition liftL (t : nat) (Ht : (t < L)%nat) (j : fin (S t)) : fin L :=
    nat2fin (Nat.le_lt_trans _ _ _
               (proj1 (Nat.lt_succ_r _ _) (fin_proof j)) Ht).

  (* Cached read: the length-(t+1) prefix read back from the environment. *)
  Definition kread (t : nat) (Ht : (t < L)%nat) (rho : env)
    : exp (ary '{S t} (ary '{dk} num)) :=
    mkvSeq (fun j : fin (S t) =>
      read_exp rho ((acc' kcp : acc (ary '{L} (ary '{dk} num)))|{liftL Ht j})).
  Definition vread (t : nat) (Ht : (t < L)%nat) (rho : env)
    : exp (ary '{S t} (ary '{dk} num)) :=
    mkvSeq (fun j : fin (S t) =>
      read_exp rho ((acc' vcp : acc (ary '{L} (ary '{dk} num)))|{liftL Ht j})).

  (* Recompute: the length-(t+1) prefix of the value vector. *)
  Definition kpref (t : nat) (Ht : (t < L)%nat)
    : exp (ary '{S t} (ary '{dk} num)) :=
    mkvSeq (fun j : fin (S t) => fkv (liftL Ht j)).
  Definition vpref (t : nat) (Ht : (t < L)%nat)
    : exp (ary '{S t} (ary '{dk} num)) :=
    mkvSeq (fun j : fin (S t) => fvv (liftL Ht j)).

  Lemma kread_eq : forall (t : nat) (Ht : (t < L)%nat) (rho : env),
    kread Ht (cachefill rho) = kpref Ht.
  Proof.
    intros t Ht rho. unfold kread, kpref. f_equal.
    apply functional_extensionality. intro j.
    apply read_exp_eq. apply cache_k.
  Qed.

  Lemma vread_eq : forall (t : nat) (Ht : (t < L)%nat) (rho : env),
    vread Ht (cachefill rho) = vpref Ht.
  Proof.
    intros t Ht rho. unfold vread, vpref. f_equal.
    apply functional_extensionality. intro j.
    apply read_exp_eq. apply cache_v.
  Qed.

  (* The KV-cache core theorem: attention at step t computed from the cached
     K/V equals attention over the recomputed prefix. *)
  Theorem kv_cache_equiv : forall (t : nat) (Ht : (t < L)%nat) (rho : env)
    (q : exp (ary '{dk} num)),
    AttnQ q (kread Ht (cachefill rho)) (vread Ht (cachefill rho))
    = AttnQ q (kpref Ht) (vpref Ht).
  Proof.
    intros. rewrite kread_eq, vread_eq. reflexivity.
  Qed.

  (* Cell-level form: the last row of the full causal attention cell is the
     same whether K/V come from the cache or from recomputation. *)
  Theorem kv_cache_equiv_cell : forall (t : nat) (Ht : (t < L)%nat)
    (Hdk : dk > 0) (rho : env) (Q : exp (ary '{S t} (ary '{dk} num))),
    idx (Attention_cell Q (kread Ht (cachefill rho)) (vread Ht (cachefill rho)))
        (fin_last t)
    = idx (Attention_cell Q (kpref Ht) (vpref Ht)) (fin_last t).
  Proof.
    intros. rewrite kread_eq, vread_eq. reflexivity.
  Qed.

  (* The cached attention command: reads the cache prefix from the incoming
     environment and runs the single-query attention loop nest. *)
  Definition attn_cached_comm (t : nat) (Ht : (t < L)%nat)
    (q : exp (ary '{dk} num)) (out : acc (ary '{dk} num)) : comm :=
    fun rho => AttnQ_comm q (kread Ht rho) (vread Ht rho) out rho.

  (* Command-level equivalence: after the fill, the cached command observed
     at an output path equals the functional recompute. *)
  Theorem A_AttnQ_cached : forall (t : nat) (Ht : (t < L)%nat)
    (q : exp (ary '{dk} num)) (out : acc (ary '{dk} num))
    (rho : env) (p : path),
    in_acc p out ->
    attn_cached_comm Ht q out (cachefill rho) p
    = A(out, AttnQ q (kpref Ht) (vpref Ht)) rho p.
  Proof.
    intros t Ht q out rho p Hp. unfold attn_cached_comm.
    rewrite <- (A_AttnQ dk (S t) q
                  (kread Ht (cachefill rho)) (vread Ht (cachefill rho)) out).
    rewrite (kv_cache_equiv (t:=t) Ht rho q).
    unfold A. apply assign_pure_independent. exact Hp.
  Qed.

End KVCache.

(* -------------------------------------------------------------------------- *)
(* Part 2: bounded autoregressive generation with KV-cache                    *)
(* -------------------------------------------------------------------------- *)

Section BoundedGenerate.

  Context (T dk : nat).
  (* current-token embedding at position 0 (the prompt's last token) *)
  Context (x0 : exp (ary '{dk} num)).
  (* projections and the next-token map (simplified MHA step: AttnQ of the
     current query over the cached prefix, then [emit]) *)
  Context (qproj kproj vproj emit : exp (ary '{dk} num) -> exp (ary '{dk} num)).
  (* EOS/done flag and the sentinel rows written once done *)
  Context (isdone : exp (ary '{dk} num) -> bool).
  Context (sentk sentv sento : exp (ary '{dk} num)).
  (* buffers: state, K cache, V cache, outputs *)
  Context (sp kcp vcp outp : path).

  Definition stD : data := ary '{dk} num.

  (* Path disjointness of the four buffers (the only premise of the
     end-to-end theorem). *)
  Definition kv_paths_distinct : Prop :=
    (forall j : fin T, sp <> AryIdx j kcp) /\
    (forall j : fin T, sp <> AryIdx j vcp) /\
    (forall j : fin T, sp <> AryIdx j outp) /\
    (forall i j : fin T, AryIdx i kcp <> AryIdx j vcp) /\
    (forall i j : fin T, AryIdx i kcp <> AryIdx j outp) /\
    (forall i j : fin T, AryIdx i vcp <> AryIdx j outp).

  Context (Hdist : kv_paths_distinct).

  (* ------------- functional model (snoc recursion on the token trace) ---- *)

  Fixpoint gen_trace (n : nat) : exp (ary '{S n} stD) :=
    match n with
    | 0 => mkvSeq (fun _ : fin 1 => x0)
    | S n' =>
      let prev := gen_trace n' in
      let xl := idx prev (fin_last n') in
      (prev, if isdone xl then xl
             else emit (AttnQ (qproj xl)
                         (mkvSeq (fun j : fin (S n') =>
                           let xj := idx prev j in
                           if isdone xj then sentk else kproj xj))
                         (mkvSeq (fun j : fin (S n') =>
                           let xj := idx prev j in
                           if isdone xj then sentv else vproj xj))))
    end.

  (* the token embedding at position n *)
  Definition gen_at (n : nat) : exp stD := idx (gen_trace n) (fin_last n).

  (* guarded (sentinel) per-position K/V values *)
  Definition gk (n : nat) : exp stD :=
    if isdone (gen_at n) then sentk else kproj (gen_at n).
  Definition gv (n : nat) : exp stD :=
    if isdone (gen_at n) then sentv else vproj (gen_at n).

  (* prefix K/V tables for the step-n attention *)
  Definition gpreK (n : nat) : exp (ary '{S n} stD) :=
    mkvSeq (fun j : fin (S n) => gk (fin2nat j)).
  Definition gpreV (n : nat) : exp (ary '{S n} stD) :=
    mkvSeq (fun j : fin (S n) => gv (fin2nat j)).

  (* step-n attention output and its guarded output value *)
  Definition attnF (n : nat) : exp stD :=
    AttnQ (qproj (gen_at n)) (gpreK n) (gpreV n).
  Definition gout (n : nat) : exp stD :=
    if isdone (gen_at n) then sento else attnF n.

  (* the length-T output array *)
  Definition gen_outputs : exp (ary '{T} stD) :=
    mkvSeq (fun t : fin T => gout (fin2nat t)).

  (* ------------- definitional unfolding lemmas (Opaque wrappers) --------- *)

  Lemma gen_at_0 : gen_at 0 = x0.
  Proof. unfold gen_at. cbn [gen_trace]. rewrite idx_mkvSeq by lia. reflexivity. Qed.

  (* trace consistency: position j of the length-(n+1) trace is token j *)
  Lemma trace_at : forall (n : nat) (j : fin (S n)),
    idx (gen_trace n) j = gen_at (fin2nat j).
  Proof.
    induction n as [|n' IHn]; intro j.
    - assert (Hj : fin2nat j = 0).
      { destruct j as [[|x] Hx]; [reflexivity | lia]. }
      rewrite Hj. rewrite gen_at_0.
      cbn [gen_trace]. rewrite idx_mkvSeq by lia. reflexivity.
    - destruct (fin_case j) as [[i Hi] | Hi].
      + subst j. cbn [gen_trace]. rewrite idx_pred.
        rewrite IHn. rewrite fin2nat_fin2finS. reflexivity.
      + subst j. unfold ltS. rewrite fin2nat_nat2fin.
        unfold gen_at. reflexivity.
  Qed.

  Lemma gpreK_trace : forall (n : nat),
    mkvSeq (fun j : fin (S n) =>
      (let xj := idx (gen_trace n) j in if isdone xj then sentk else kproj xj))
    = gpreK n.
  Proof.
    intro n. unfold gpreK, gk. f_equal.
    apply functional_extensionality. intro j. cbv zeta.
    rewrite trace_at. reflexivity.
  Qed.

  Lemma gpreV_trace : forall (n : nat),
    mkvSeq (fun j : fin (S n) =>
      (let xj := idx (gen_trace n) j in if isdone xj then sentv else vproj xj))
    = gpreV n.
  Proof.
    intro n. unfold gpreV, gv. f_equal.
    apply functional_extensionality. intro j. cbv zeta.
    rewrite trace_at. reflexivity.
  Qed.

  (* the step equation of the functional token stream *)
  Lemma gen_at_S : forall (n : nat),
    gen_at (S n) = if isdone (gen_at n) then gen_at n else emit (attnF n).
  Proof.
    intro n. unfold gen_at, attnF. cbn [gen_trace].
    rewrite idx_last. cbv zeta.
    rewrite gpreK_trace, gpreV_trace. reflexivity.
  Qed.

  Lemma gk_body : forall n, gk n = if isdone (gen_at n) then sentk else kproj (gen_at n).
  Proof. reflexivity. Qed.
  Lemma gv_body : forall n, gv n = if isdone (gen_at n) then sentv else vproj (gen_at n).
  Proof. reflexivity. Qed.
  Lemma gpreK_body : forall n, gpreK n = mkvSeq (fun j : fin (S n) => gk (fin2nat j)).
  Proof. reflexivity. Qed.
  Lemma gpreV_body : forall n, gpreV n = mkvSeq (fun j : fin (S n) => gv (fin2nat j)).
  Proof. reflexivity. Qed.
  Lemma attnF_body : forall n,
    attnF n = AttnQ (qproj (gen_at n)) (gpreK n) (gpreV n).
  Proof. reflexivity. Qed.
  Lemma gout_body : forall n,
    gout n = if isdone (gen_at n) then sento else attnF n.
  Proof. reflexivity. Qed.
  Lemma gen_outputs_body :
    gen_outputs = mkvSeq (fun t : fin T => gout (fin2nat t)).
  Proof. reflexivity. Qed.

  Opaque gen_trace gen_at gk gv gpreK gpreV attnF gout gen_outputs.

  (* ------------- imperative program ------------------------------------- *)

  (* prefix lifting into the length-T caches *)
  Definition liftT (t : fin T) (j : fin (S (fin2nat t))) : fin T :=
    nat2fin (Nat.le_lt_trans _ _ _
               (proj1 (Nat.lt_succ_r _ _) (fin_proof j)) (fin_proof t)).

  Lemma liftT_fin2nat : forall (t : fin T) (j : fin (S (fin2nat t))),
    fin2nat (liftT t j) = fin2nat j.
  Proof. intros. unfold liftT. apply fin2nat_nat2fin. Qed.

  (* One generation step: read the current token, If-guarded writes of the
     K/V cache slots and the output slot (sentinel once done), attention over
     the cache prefix read back from the environment, state update. *)
  Definition genstep (t : fin T) : comm := fun rho =>
    let st := read_exp rho (acc' sp : acc stD) in
    let g := isdone st in
    let rho1 := (If g (acc' (AryIdx t kcp) |:= sentk)
                      (acc' (AryIdx t kcp) |:= kproj st)) rho in
    let rho2 := (If g (acc' (AryIdx t vcp) |:= sentv)
                      (acc' (AryIdx t vcp) |:= vproj st)) rho1 in
    let kr := mkvSeq (fun j : fin (S (fin2nat t)) =>
                read_exp rho2 (acc' (AryIdx (liftT t j) kcp))) in
    let vr := mkvSeq (fun j : fin (S (fin2nat t)) =>
                read_exp rho2 (acc' (AryIdx (liftT t j) vcp))) in
    let rho3 := (If g (acc' (AryIdx t outp) |:= sento)
                      (acc' (AryIdx t outp) |:= AttnQ (qproj st) kr vr)) rho2 in
    ((acc' sp : acc stD) |:= (if g then st else emit (AttnQ (qproj st) kr vr))) rho3.

  Definition gen_init : comm := (acc' sp : acc stD) |:= x0.
  Definition genloop : comm := seqfor (fun t : fin T => genstep t).
  Definition bounded_gen_comm : comm := gen_init '; genloop.

  (* ------------- loop invariant ------------------------------------------ *)

  Definition gen_inv (n : nat) (rho : env) : Prop :=
    access rho (acc' sp : acc stD) = Some (gen_at n) /\
    (forall j : fin T, (fin2nat j < n)%nat ->
      access rho (acc' (AryIdx j kcp)) = Some (gk (fin2nat j))) /\
    (forall j : fin T, (fin2nat j < n)%nat ->
      access rho (acc' (AryIdx j vcp)) = Some (gv (fin2nat j))) /\
    (forall j : fin T, (fin2nat j < n)%nat ->
      access rho (acc' (AryIdx j outp)) = Some (gout (fin2nat j))).

  (* Reading the K prefix after this step's guarded K/V writes: slot t reads
     the just-written value, earlier slots read the invariant values. *)
  Lemma kslot_read_after : forall (t : fin T) (rho : env) (ek ev : exp stD),
    gen_inv (fin2nat t) rho ->
    forall (j : fin (S (fin2nat t))),
    read_exp ((acc' (AryIdx t vcp) |:= ev) ((acc' (AryIdx t kcp) |:= ek) rho))
             (acc' (AryIdx (liftT t j) kcp))
    = (if (fin2nat j =? fin2nat t)%nat then ek else gk (fin2nat j)).
  Proof.
    intros t rho ek ev [Hst [Hk [Hv Ho]]] j.
    destruct Hdist as [Hsk [Hsv [Hso [Hkv [Hko Hvo]]]]].
    unfold stD in *. unfold read_exp.
    assert (Hneq1 : AryIdx t vcp <> AryIdx (liftT t j) kcp).
    { intros Hc. apply (Hkv (liftT t j) t). symmetry. exact Hc. }
    rewrite (access_assign_neq _ _ _ Hneq1).
    rewrite access_assign.
    destruct (fin2nat j =? fin2nat t)%nat eqn:E.
    - apply Nat.eqb_eq in E.
      assert (Hp : AryIdx t kcp = AryIdx (liftT t j) kcp).
      { apply AryIdx_eq_l2; [| reflexivity].
        apply (proj1 (fin_eq _ _)). rewrite liftT_fin2nat.
        symmetry. exact E. }
      rewrite Hp. rewrite path_eqb_refl. reflexivity.
    - apply Nat.eqb_neq in E.
      assert (Hp : path_eqb (AryIdx t kcp) (AryIdx (liftT t j) kcp) = false).
      { apply path_eqb_neq. intros Hc.
        apply AryIdx_eq in Hc. destruct Hc as [_ [H2 _]].
        rewrite liftT_fin2nat in H2. apply E. symmetry. exact H2. }
      rewrite Hp.
      assert (Hlt : (fin2nat (liftT t j) < fin2nat t)%nat).
      { rewrite liftT_fin2nat. pose proof (fin_proof j). lia. }
      rewrite (Hk (liftT t j) Hlt).
      rewrite liftT_fin2nat. reflexivity.
  Qed.

  (* Same for the V prefix. *)
  Lemma vslot_read_after : forall (t : fin T) (rho : env) (ek ev : exp stD),
    gen_inv (fin2nat t) rho ->
    forall (j : fin (S (fin2nat t))),
    read_exp ((acc' (AryIdx t vcp) |:= ev) ((acc' (AryIdx t kcp) |:= ek) rho))
             (acc' (AryIdx (liftT t j) vcp))
    = (if (fin2nat j =? fin2nat t)%nat then ev else gv (fin2nat j)).
  Proof.
    intros t rho ek ev [Hst [Hk [Hv Ho]]] j.
    destruct Hdist as [Hsk [Hsv [Hso [Hkv [Hko Hvo]]]]].
    unfold stD in *. unfold read_exp.
    rewrite access_assign.
    destruct (fin2nat j =? fin2nat t)%nat eqn:E.
    - apply Nat.eqb_eq in E.
      assert (Hp : AryIdx t vcp = AryIdx (liftT t j) vcp).
      { apply AryIdx_eq_l2; [| reflexivity].
        apply (proj1 (fin_eq _ _)). rewrite liftT_fin2nat.
        symmetry. exact E. }
      rewrite Hp. rewrite path_eqb_refl. reflexivity.
    - apply Nat.eqb_neq in E.
      assert (Hp : path_eqb (AryIdx t vcp) (AryIdx (liftT t j) vcp) = false).
      { apply path_eqb_neq. intros Hc.
        apply AryIdx_eq in Hc. destruct Hc as [_ [H2 _]].
        rewrite liftT_fin2nat in H2. apply E. symmetry. exact H2. }
      rewrite Hp.
      assert (Hneq1 : AryIdx t kcp <> AryIdx (liftT t j) vcp).
      { intros Hc. apply (Hkv t (liftT t j)). exact Hc. }
      rewrite (access_assign_neq _ _ _ Hneq1).
      assert (Hlt : (fin2nat (liftT t j) < fin2nat t)%nat).
      { rewrite liftT_fin2nat. pose proof (fin_proof j). lia. }
      rewrite (Hv (liftT t j) Hlt).
      rewrite liftT_fin2nat. reflexivity.
  Qed.

  (* Step correctness: the invariant advances from n to S n. *)
  Lemma genstep_correct : forall (t : fin T) (rho : env),
    gen_inv (fin2nat t) rho -> gen_inv (S (fin2nat t)) (genstep t rho).
  Proof.
    intros t rho Hinv. destruct Hinv as [Hst [Hk [Hv Ho]]].
    destruct Hdist as [Hsk [Hsv [Hso [Hkv [Hko Hvo]]]]].
    unfold stD in *.
    assert (Hok : forall i j : fin T, AryIdx i outp <> AryIdx j kcp).
    { intros i0 j0 Hc. apply (Hko j0 i0). symmetry. exact Hc. }
    assert (Hvk : forall i j : fin T, AryIdx i vcp <> AryIdx j kcp).
    { intros i0 j0 Hc. apply (Hkv j0 i0). symmetry. exact Hc. }
    assert (Hov : forall i j : fin T, AryIdx i outp <> AryIdx j vcp).
    { intros i0 j0 Hc. apply (Hvo j0 i0). symmetry. exact Hc. }
    unfold genstep. cbv beta zeta.
    assert (Hrd : read_exp rho (acc' sp : acc stD) = gen_at (fin2nat t)).
    { apply read_exp_eq. exact Hst. }
    rewrite !Hrd.
    rewrite !If_assign_merge.
    (* the read-back K/V prefixes equal the recomputed prefixes *)
    assert (Hkr : mkvSeq (fun j : fin (S (fin2nat t)) =>
                    read_exp ((acc' (AryIdx t vcp) |:=
                                (if isdone (gen_at (fin2nat t)) then sentv
                                 else vproj (gen_at (fin2nat t))))
                              ((acc' (AryIdx t kcp) |:=
                                (if isdone (gen_at (fin2nat t)) then sentk
                                 else kproj (gen_at (fin2nat t)))) rho))
                             (acc' (AryIdx (liftT t j) kcp)))
                  = gpreK (fin2nat t)).
    { rewrite gpreK_body. f_equal. apply functional_extensionality. intro j.
      rewrite (kslot_read_after t _ _ (conj Hst (conj Hk (conj Hv Ho))) j).
      destruct (fin2nat j =? fin2nat t)%nat eqn:E.
      - apply Nat.eqb_eq in E. rewrite E. rewrite gk_body. reflexivity.
      - reflexivity. }
    assert (Hvr : mkvSeq (fun j : fin (S (fin2nat t)) =>
                    read_exp ((acc' (AryIdx t vcp) |:=
                                (if isdone (gen_at (fin2nat t)) then sentv
                                 else vproj (gen_at (fin2nat t))))
                              ((acc' (AryIdx t kcp) |:=
                                (if isdone (gen_at (fin2nat t)) then sentk
                                 else kproj (gen_at (fin2nat t)))) rho))
                             (acc' (AryIdx (liftT t j) vcp)))
                  = gpreV (fin2nat t)).
    { rewrite gpreV_body. f_equal. apply functional_extensionality. intro j.
      rewrite (vslot_read_after t _ _ (conj Hst (conj Hk (conj Hv Ho))) j).
      destruct (fin2nat j =? fin2nat t)%nat eqn:E.
      - apply Nat.eqb_eq in E. rewrite E. rewrite gv_body. reflexivity.
      - reflexivity. }
    unfold stD in Hkr, Hvr.
    rewrite Hkr, Hvr.
    rewrite <- gk_body, <- gv_body, <- attnF_body, <- gout_body, <- gen_at_S.
    (* now the four components of the invariant at S (fin2nat t) *)
    unfold gen_inv. split; [| split; [| split]].
    - rewrite (access_assign_eq _ _ _ eq_refl). reflexivity.
    - intros j Hj.
      rewrite (access_assign_neq _ _ _ (Hsk j)).
      rewrite (access_assign_neq _ _ _ (Hok t j)).
      rewrite (access_assign_neq _ _ _ (Hvk t j)).
      destruct (Nat.eq_dec (fin2nat j) (fin2nat t)) as [E | E].
      + assert (j = t) by (apply (proj1 (fin_eq _ _)); exact E). subst j.
        rewrite (access_assign_eq _ _ _ eq_refl). reflexivity.
      + assert (Hne2 : AryIdx t kcp <> AryIdx j kcp).
        { apply aryidx_neq_idx. lia. }
        rewrite (access_assign_neq _ _ _ Hne2).
        apply Hk. pose proof (fin_proof t). lia.
    - intros j Hj.
      rewrite (access_assign_neq _ _ _ (Hsv j)).
      rewrite (access_assign_neq _ _ _ (Hov t j)).
      destruct (Nat.eq_dec (fin2nat j) (fin2nat t)) as [E | E].
      + assert (j = t) by (apply (proj1 (fin_eq _ _)); exact E). subst j.
        rewrite (access_assign_eq _ _ _ eq_refl). reflexivity.
      + assert (Hne2 : AryIdx t vcp <> AryIdx j vcp).
        { apply aryidx_neq_idx. lia. }
        rewrite (access_assign_neq _ _ _ Hne2).
        rewrite (access_assign_neq _ _ _ (Hkv t j)).
        apply Hv. pose proof (fin_proof t). lia.
    - intros j Hj.
      rewrite (access_assign_neq _ _ _ (Hso j)).
      destruct (Nat.eq_dec (fin2nat j) (fin2nat t)) as [E | E].
      + assert (j = t) by (apply (proj1 (fin_eq _ _)); exact E). subst j.
        rewrite (access_assign_eq _ _ _ eq_refl). reflexivity.
      + assert (Hne2 : AryIdx t outp <> AryIdx j outp).
        { apply aryidx_neq_idx. lia. }
        rewrite (access_assign_neq _ _ _ Hne2).
        rewrite (access_assign_neq _ _ _ (Hvo t j)).
        rewrite (access_assign_neq _ _ _ (Hko t j)).
        apply Ho. pose proof (fin_proof t). lia.
  Qed.

  (* The initial write establishes the invariant at 0. *)
  Lemma gen_inv_init : forall rho, gen_inv 0 (gen_init rho).
  Proof.
    intro rho. unfold gen_inv, gen_init. split; [| split; [| split]].
    - rewrite (access_assign_eq _ x0 rho eq_refl).
      rewrite gen_at_0. reflexivity.
    - intros j Hj. exfalso. lia.
    - intros j Hj. exfalso. lia.
    - intros j Hj. exfalso. lia.
  Qed.

  (* The n-step prefix of the loop establishes the invariant at n. *)
  Lemma genloop_inv : forall (n : nat) (Hn : (n <= T)%nat) (rho : env),
    gen_inv 0 rho ->
    gen_inv n (seqfor (fun s : fin n =>
                 genstep (nat2fin (Nat.lt_le_trans _ _ _ (fin_proof s) Hn))) rho).
  Proof.
    induction n as [|n' IHn]; intros Hn rho H0.
    - exact H0.
    - rewrite seqfor_Sn. unfold seq.
      assert (Hn'T : (n' < T)%nat) by lia.
      assert (Halign : nat2fin (Nat.lt_le_trans _ _ _ (fin_proof (ltS n')) Hn)
                       = nat2fin Hn'T).
      { apply (proj1 (fin_eq _ _)). rewrite !fin2nat_nat2fin.
        apply fin2nat_ltS. }
      rewrite Halign.
      apply genstep_correct.
      assert (Hn' : (n' <= T)%nat) by lia.
      pose proof (IHn Hn' rho H0) as IH.
      replace (seqfor (fun i : fin n' =>
                 genstep (nat2fin (Nat.lt_le_trans _ _ _ (fin_proof FS[i]) Hn))))
        with (seqfor (fun i : fin n' =>
                 genstep (nat2fin (Nat.lt_le_trans _ _ _ (fin_proof i) Hn')))).
      2: { apply seqfor_extensionality. intro i. f_equal.
           apply (proj1 (fin_eq _ _)).
           rewrite !fin2nat_nat2fin.
           first [apply fin2nat_fin2finS | symmetry; apply fin2nat_fin2finS]. }
      exact IH.
  Qed.

  (* ------------- end-to-end ---------------------------------------------- *)

  (* paths under a two-level buffer acc' base *)
  Lemma in_acc_acc'2 : forall (base : path) (p : path),
    in_acc p (acc' base : acc (ary '{T} stD)) ->
    exists (t : fin T) (dd : fin dk), p = AryIdx dd (AryIdx t base).
  Proof.
    intros base p H. cbn [in_acc] in H. destruct H as [t Ht].
    rewrite (slot_path_raw stD base t) in Ht.
    cbn [in_acc] in Ht. destruct Ht as [dd Hdd].
    unfold stD in Hdd.
    rewrite (slot_path_raw num (AryIdx t base) dd) in Hdd.
    cbn [in_acc] in Hdd. cbn in Hdd.
    exists t, dd. symmetry. exact Hdd.
  Qed.

  (* leaf read-back from a whole-array access *)
  Lemma access_leaf2 : forall (base : path) (rho : env)
    (G : exp (ary '{T} stD)) (t : fin T) (dd : fin dk),
    access rho (acc' base : acc (ary '{T} stD)) = Some G ->
    rho (AryIdx dd (AryIdx t base)) = Some (idx (idx G t) dd).
  Proof.
    intros base rho G t dd H.
    pose proof (access_acc'_level stD base rho t H) as H1.
    pose proof (access_acc'_level num (AryIdx t base) rho dd H1) as H2.
    exact H2.
  Qed.

  (* the loop computes the functional outputs (whole-array read-back) *)
  Lemma bounded_gen_access : forall (rho : env),
    access (bounded_gen_comm rho) (acc' outp : acc (ary '{T} stD))
    = Some gen_outputs.
  Proof.
    intro rho.
    assert (Hsf : genloop
            = seqfor (fun s : fin T =>
                genstep (nat2fin (Nat.lt_le_trans _ _ _ (fin_proof s) (le_n T))))).
    { unfold genloop. apply seqfor_extensionality. intro t. f_equal.
      apply (proj1 (fin_eq _ _)). rewrite fin2nat_nat2fin. reflexivity. }
    unfold bounded_gen_comm. unfold seq. rewrite Hsf.
    pose proof (genloop_inv (le_n T) (gen_inv_init rho))
      as [Hst [Hk [Hv Ho]]].
    rewrite access_ary.
    rewrite (mkoptvec_dependence _ _ (fun t : fin T => Some (gout (fin2nat t)))).
    2: { intro t.
         rewrite (c_idx_acc'_raw stD outp t).
         apply Ho. apply fin_proof. }
    rewrite mkoptvec_some_all. rewrite gen_outputs_body. reflexivity.
  Qed.

  (* End-to-end: the T-step bounded generation loop with KV-cache, observed
     at an output path, equals the functional bounded generation. *)
  Theorem A_BoundedGenerate : forall (rho : env) (p : path),
    in_acc p (acc' outp : acc (ary '{T} stD)) ->
    bounded_gen_comm rho p = A(acc' outp : acc (ary '{T} stD), gen_outputs) rho p.
  Proof.
    intros rho p Hp.
    destruct (in_acc_acc'2 outp Hp) as [t [dd Hpeq]]. subst p.
    rewrite (access_leaf2 _ _ _ _ (bounded_gen_access rho)).
    unfold A.
    assert (H2 : access (assign (acc' outp : acc (ary '{T} stD)) gen_outputs rho)
                        (acc' outp) = Some gen_outputs).
    { apply access_assign_eq. reflexivity. }
    rewrite (access_leaf2 _ _ _ _ H2). reflexivity.
  Qed.

  (* ------------- small-instance spot checks (inside the section) --------- *)

  (* the functional token stream unrolls step by step *)
  Example gen_at_unroll2 :
    gen_at 2 = if isdone (gen_at 1) then gen_at 1 else emit (attnF 1).
  Proof. exact (gen_at_S 1). Qed.

  Example gen_at_unroll4 :
    gen_at 4 = if isdone (gen_at 3) then gen_at 3 else emit (attnF 3).
  Proof. exact (gen_at_S 3). Qed.

  (* output array entry = guarded per-step output *)
  Example gen_outputs_at : forall t : fin T,
    idx gen_outputs t = gout (fin2nat t).
  Proof.
    intro t. rewrite gen_outputs_body. apply idx_mkvSeq.
    pose proof (fin_proof t). lia.
  Qed.

End BoundedGenerate.

(* -------------------------------------------------------------------------- *)
(* Part 3: small-instance spot checks (T = 4 scale)                           *)
(* -------------------------------------------------------------------------- *)

Section Small_T4.

  Context (dk4 : nat) (x4 : exp (ary '{dk4} num))
          (q4 k4 v4 e4 : exp (ary '{dk4} num) -> exp (ary '{dk4} num))
          (d4 : exp (ary '{dk4} num) -> bool)
          (sk4 sv4 so4 : exp (ary '{dk4} num))
          (sp4 kc4 vc4 ou4 : path).

  (* NB: section discharge only abstracts the variables actually used:
     [genstep] does not mention x0. *)
  Definition genstep4 : fin 4 -> comm :=
    genstep (T:=4) dk4 q4 k4 v4 e4 d4 sk4 sv4 so4 sp4 kc4 vc4 ou4.
  Definition bounded_gen4 : comm :=
    bounded_gen_comm 4 dk4 x4 q4 k4 v4 e4 d4 sk4 sv4 so4 sp4 kc4 vc4 ou4.
  Definition gen_outputs4 : exp (ary '{4} (ary '{dk4} num)) :=
    gen_outputs 4 dk4 x4 q4 k4 v4 e4 d4 sk4 sv4 so4.

  (* the T = 4 loop unrolls one step (snoc order) *)
  Example genloop4_unroll :
    seqfor (fun t : fin 4 => genstep4 t)
    = seqfor (fun i : fin 3 => genstep4 FS[i]) '; genstep4 '[3].
  Proof. exact (seqfor_Sn (fun t : fin 4 => genstep4 t)). Qed.

  (* the end-to-end theorem instantiates at T = 4 *)
  Example A_BoundedGenerate_T4 :
    kv_paths_distinct 4 sp4 kc4 vc4 ou4 ->
    forall (rho : env) (p : path),
    in_acc p (acc' ou4 : acc (ary '{4} (ary '{dk4} num))) ->
    bounded_gen4 rho p
    = A(acc' ou4 : acc (ary '{4} (ary '{dk4} num)), gen_outputs4) rho p.
  Proof.
    intros H rho p Hp.
    exact (A_BoundedGenerate (T:=4) (dk:=dk4)
             x4 q4 k4 v4 e4 d4 sk4 sv4 so4 H rho Hp).
  Qed.

End Small_T4.

(* Structural spot checks of the single-query attention at dk = 2, prefix 2. *)

Definition Q2 : exp (ary '{2} num) := mkvSeq (fun _ : fin 2 => (INR 1 : exp num)).
Definition K2 : exp (ary '{2} (ary '{2} num)) :=
  mkvSeq (fun j : fin 2 => mkvSeq (fun dd : fin 2 => (INR (fin2nat j + 1) : exp num))).
Definition V2 : exp (ary '{2} (ary '{2} num)) :=
  mkvSeq (fun j : fin 2 => mkvSeq (fun dd : fin 2 => (INR (fin2nat j * 2 + fin2nat dd) : exp num))).
Definition i0_2k : fin 2 := @nat2fin 2 0 (ltac:(lia)).

(* score at prefix position 0: q . K_0 = 1*1 + 1*1, scaled *)
Example check_attnq_score0 :
  idx (attn_scores Q2 K2) i0_2k
  = mul (sum (mkvSeq (fun dd : fin 2 => mul (INR 1) (INR 1)))) (attn_scale 2).
Proof. reflexivity. Qed.

(* output component 0: softmax-weighted sum of the V rows' first components *)
Example check_attnq_entry0 :
  idx (AttnQ Q2 K2 V2) i0_2k
  = sum (mkvSeq (fun j : fin 2 =>
      mul (idx (Softmax1d (attn_scores Q2 K2)) j) (idx (idx V2 j) i0_2k))).
Proof. reflexivity. Qed.

(* the cache/recompute equivalence at L = 4, step t = 2 *)
Section Small_KV4.

  (* prefix consistency at L = 4 (the heart of the cache theorem) *)
  Example cache_k_L4 : forall (fk4 fv4 : fin 4 -> exp (ary '{2} num))
    (kc4 vc4 : path) (Hkv4 : kc4 <> vc4) (m : fin 4) (rho : env),
    access (cachefill (L:=4) 2 fk4 fv4 kc4 vc4 rho)
           ((acc' kc4 : acc (ary '{4} (ary '{2} num)))|{m})
    = Some (fk4 m).
  Proof. intros. apply cache_k. exact Hkv4. Qed.

  (* the full equivalence at L = 4, step t = 2 *)
  Example kv_cache_equiv_L4 : forall (fk4 fv4 : fin 4 -> exp (ary '{2} num))
    (kc4 vc4 : path) (Hkv4 : kc4 <> vc4) (rho : env) (q : exp (ary '{2} num))
    (Ht : (2 < 4)%nat),
    AttnQ q (kread (L:=4) 2 kc4 Ht (cachefill (L:=4) 2 fk4 fv4 kc4 vc4 rho))
            (vread (L:=4) 2 vc4 Ht (cachefill (L:=4) 2 fk4 fv4 kc4 vc4 rho))
    = AttnQ q (kpref (L:=4) 2 fk4 Ht) (vpref (L:=4) 2 fv4 Ht).
  Proof. intros. apply kv_cache_equiv. exact Hkv4. Qed.

End Small_KV4.

(* -------------------------------------------------------------------------- *)
(* Axiom audit                                                                *)
(* -------------------------------------------------------------------------- *)

Print Assumptions If_assign_merge.
Print Assumptions fill_read.
Print Assumptions fill_other.
Print Assumptions A_AttnQ.
Print Assumptions AttnQ_cell_last.
Print Assumptions kv_cache_equiv.
Print Assumptions kv_cache_equiv_cell.
Print Assumptions A_AttnQ_cached.
Print Assumptions gen_at_S.
Print Assumptions genstep_correct.
Print Assumptions genloop_inv.
Print Assumptions bounded_gen_access.
Print Assumptions A_BoundedGenerate.
Print Assumptions A_BoundedGenerate_T4.
