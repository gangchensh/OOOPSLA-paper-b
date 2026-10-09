(* ========================================================================= *)
(* Opt_QuantError_LLaMA.v                                                    *)
(*                                                                           *)
(* Instantiation of the generic rounding/quantization error bounds           *)
(* (Opt_ApproxError.v: TF32/FP16 relative-model track; Opt_QuantError.v:     *)
(* int8 absolute-model track) to the decode-phase GEMV dot products of a     *)
(* LLaMA-style decoder (KVCache.v, LLaMAMini_DPIA.v).                        *)
(*                                                                           *)
(* The three dot products of one decode step (token s = 1 against the        *)
(* length-n KV prefix) are:                                                  *)
(*   (1) attention scores      dotr q (idx K j)          — length dk         *)
(*       (KVCache.v, [dotr] inside [attn_scores]);                           *)
(*   (2) attention output      idx (AttnQ q K V) dd      — length n          *)
(*       (softmax weights times the V column dd, KVCache.v [AttnQ]);         *)
(*   (3) FFN / projection GEMV idx (idx (MatMul2d a w) i) j — length n       *)
(*       (Ops_Transformer.v [MatMul2d]; [BMatMul2d] with s = 1 degenerates   *)
(*       to a matvec; SwiGLUFFN of LLaMAMini_DPIA.v is three such GEMVs      *)
(*       followed by one df -> dm GEMV).  LLaMA-mini sizes: dk = 16,         *)
(*       dm = df = 32 (LLaMAMini_DPIA.v, Section Small_1_8_2_8).             *)
(*                                                                           *)
(* In the strict DPIA track these are EXACT R-expressions                    *)
(* (exp num = R definitionally); each theorem below relates the exact        *)
(* DPIA semantics to the same computation under an abstract rounding         *)
(* operator [rnd] (standard model |rnd x - x| <= u|x|) resp. int8 quantized  *)
(* inputs with exact int32 accumulation, by a single [apply] of the generic  *)
(* bound.  The only non-trivial new ingredient is the bridge lemma           *)
(* [mkvSeq_pw2]: the DPIA summand vector mkvSeq (fun k => mul (idx u k)      *)
(* (idx v k)) is definitionally-extensionally the pointwise product          *)
(* v_pw2 Rmult n u v used by the error bounds.                               *)
(*                                                                           *)
(* Contents:                                                                 *)
(*   1. mkvSeq_pw2 + corollaries dotr_eq_dot_exact, attnQ_entry_eq_dot_exact *)
(*      (attention weighted sum), matmul_entry_eq_dot_exact and              *)
(*      bmatmul_entry_eq_dot_exact (FFN/projection GEMV entry).              *)
(*   2. TF32/float track (abstract u, rnd): llama_attn_score_rnd_error,      *)
(*      llama_attn_out_rnd_error, llama_gemv_rnd_error.                      *)
(*   3. int8 track: llama_attn_score_int8_error, llama_gemv_int8_error.      *)
(*   4. LLaMA-mini concrete instances: dk = 16 attention scores,             *)
(*      dm = df = 32 decode (s = 1) FFN GEMV entry.                          *)
(*   5. TF32 numeric certificates (u = 2^-11) for gamma_17 (dk = 16) and     *)
(*      gamma_33 (dm = 32) via Q + vm_compute, in the style of the           *)
(*      tf32_gamma_* table of Opt_ApproxError_Apply.v.                       *)
(*                                                                           *)
(* No Admitted, no Axiom: [u]/[rnd] and the int8 quantization premises are   *)
(* ordinary universal hypotheses of the theorems.                            *)
(* ========================================================================= *)

Require Import Reals Lra Psatz Arith QArith Qreals.
From Stdlib Require Import FunctionalExtensionality.
Require Import Ionia.Proof_CodeGen.
Require Import Ionia.Opt_ApproxError.
Require Import Ionia.Opt_ApproxError_Apply.
Require Import Ionia.Opt_QuantError.
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.Ops_Transformer.
Require Import Ionia.Attention_DPIA.
Require Import Ionia.KVCache.
Require Import Ionia.LLaMAMini_DPIA.

Open Scope R_scope.

(* -------------------------------------------------------------------------- *)
(* 1. Bridge: the DPIA summand vector IS the pointwise product                *)
(* -------------------------------------------------------------------------- *)

(* Ascription-free variants of idx_pred/idx_last: after [destruct] the snoc
   pair carries the raw product type, against which the exp(ary ...)-ascribed
   originals do not unify under keyed matching. *)
Lemma idx_pred_R : forall (n:nat) (v : vector R n) (e : R) (i : fin n),
  @idx (S n) num (v, e) (fin2finS i) = @idx n num v i.
Proof. intros n v e i. exact (@idx_pred n num v e i). Qed.

Lemma idx_last_R : forall (n:nat) (v : vector R n) (e : R),
  @idx (S n) num (v, e) (fin_last n) = e.
Proof. intros n v e. exact (@idx_last n num v e). Qed.

(* snoc induction: mkvSeq = mk_vec is snoc recursion, paired with v_pw2_Sn
   via idx_pred_R (non-last slots) and idx_last_R (last slot). *)
Lemma mkvSeq_pw2 : forall (n:nat) (u v : exp (ary '{n} num)),
  mkvSeq (fun k : fin n => mul (idx u k) (idx v k))
  = v_pw2 Rmult n u v.
Proof.
  induction n as [|n IHn]; intros u v.
  - destruct u, v. reflexivity.
  - destruct u as [u1 u2], v as [v1 v2].
    rewrite v_pw2_Sn. unfold mkvSeq. cbn [mk_vec]. f_equal.
    + (* non-last slots: idx of a snoc at FS[i] *)
      assert (Hf : (fun i : fin n =>
                      mul (@idx (S n) num (u1, u2) (fin2finS i))
                          (@idx (S n) num (v1, v2) (fin2finS i)))
                 = (fun i : fin n => mul (@idx n num u1 i) (@idx n num v1 i))).
      { apply functional_extensionality. intro i.
        rewrite !idx_pred_R. reflexivity. }
      rewrite Hf. exact (IHn u1 v1).
    + (* last slot: idx of a snoc at fin_last *)
      match goal with
      | |- context [idx (u1, u2) ?x] =>
          replace x with (fin_last n) by reflexivity
      end.
      rewrite !idx_last_R. reflexivity.
Qed.

(* The attention-score dot product [dotr] of KVCache.v is exactly [dot_exact]
   of Opt_ApproxError.v (via rsum_eq_sum). *)
Lemma dotr_eq_dot_exact : forall (dk:nat) (u v : exp (ary '{dk} num)),
  dotr u v = dot_exact u v.
Proof.
  intros dk u v. unfold dotr, dot_exact.
  rewrite mkvSeq_pw2. symmetry. apply rsum_eq_sum.
Qed.

(* The length-n vector of V-column-dd values over the KV prefix. *)
Definition attn_out_col {dk n : nat}
  (V : exp (ary '{n} (ary '{dk} num))) (dd : fin dk)
  : exp (ary '{n} num) :=
  mkvSeq (fun j : fin n => idx (idx V j) dd).

(* Component dd of the single-query attention output (KVCache.v [AttnQ]) is
   the exact dot product of the softmax weights with the V column dd. *)
Lemma attnQ_entry_eq_dot_exact : forall (dk n : nat)
    (Hdk : (dk > 0)%nat) (Hn : (n > 0)%nat)
    (q : exp (ary '{dk} num))
    (K V : exp (ary '{n} (ary '{dk} num))) (dd : fin dk),
  idx (AttnQ q K V) dd
  = dot_exact (Softmax1d (attn_scores q K)) (attn_out_col V dd).
Proof.
  intros dk n Hdk Hn q K V dd.
  unfold AttnQ. rewrite idx_mkvSeq by exact Hdk.
  unfold dot_exact, attn_out_col.
  transitivity (sum (v_pw2 Rmult n (Softmax1d (attn_scores q K))
                      (mkvSeq (fun j : fin n => idx (idx V j) dd)))).
  - f_equal. symmetry. rewrite <- mkvSeq_pw2. f_equal.
    apply functional_extensionality. intro j.
    rewrite idx_mkvSeq by exact Hn. reflexivity.
  - symmetry. apply rsum_eq_sum.
Qed.

(* Entry (i, j) of MatMul2d is the exact length-n dot product of row i of a
   with column j of w (the decode GEMV: s = 1 row against the projection). *)
Lemma matmul_entry_eq_dot_exact : forall (m n p : nat) (Hn : (n > 0)%nat)
    (a : exp (ary '{m} (ary '{n} num)))
    (w : exp (ary '{n} (ary '{p} num)))
    (i : fin m) (j : fin p),
  idx (idx (MatMul2d a w) i) j
  = dot_exact (idx a i) (mkvSeq (fun k : fin n => idx (idx w k) j)).
Proof.
  intros m n p Hn a w i j.
  assert (Hm : (m > 0)%nat) by (destruct i as [x Hx]; lia).
  assert (Hp : (p > 0)%nat) by (destruct j as [y Hy]; lia).
  unfold MatMul2d.
  rewrite idx_mkvSeq by exact Hm.
  rewrite idx_mkvSeq by exact Hp.
  unfold dot_exact.
  transitivity (sum (v_pw2 Rmult n (idx a i)
                      (mkvSeq (fun k : fin n => idx (idx w k) j)))).
  - f_equal. symmetry. rewrite <- mkvSeq_pw2. f_equal.
    apply functional_extensionality. intro k.
    rewrite idx_mkvSeq by exact Hn. reflexivity.
  - symmetry. apply rsum_eq_sum.
Qed.

(* Batched form: entry (bb, i, j) of BMatMul2d (batch bb of a batch of
   matvecs; the LLaMA FFN projections x W1, x W3 and (.) W2 are of this
   shape with s = 1 at decode time). *)
Lemma bmatmul_entry_eq_dot_exact : forall (b m n p : nat) (Hn : (n > 0)%nat)
    (a : exp (ary '{b} (ary '{m} (ary '{n} num))))
    (w : exp (ary '{n} (ary '{p} num)))
    (bb : fin b) (i : fin m) (j : fin p),
  idx (idx (idx (BMatMul2d a w) bb) i) j
  = dot_exact (idx (idx a bb) i) (mkvSeq (fun k : fin n => idx (idx w k) j)).
Proof.
  intros b m n p Hn a w bb i j.
  assert (Hb : (b > 0)%nat) by (destruct bb as [x Hx]; lia).
  unfold BMatMul2d. rewrite idx_mkvSeq by exact Hb.
  apply matmul_entry_eq_dot_exact. exact Hn.
Qed.

(* -------------------------------------------------------------------------- *)
(* 2. TF32 / floating-point track: gamma_{n+1} bounds for the decode GEMV     *)
(* -------------------------------------------------------------------------- *)

(* Attention score dotr q (idx K j): length-dk dot product. *)
Theorem llama_attn_score_rnd_error : forall (u : R) (Hu : 0 <= u)
    (rnd : R -> R) (Hrnd : forall x:R, Rabs (rnd x - x) <= u * Rabs x)
    (dk : nat) (q kj : exp (ary '{dk} num)),
  Rabs (dot_rnd rnd q kj - dotr q kj)
  <= ((1 + u) ^ S dk - 1) * v_abs_sum (v_pw2 Rmult dk q kj).
Proof.
  intros u Hu rnd Hrnd dk q kj.
  rewrite dotr_eq_dot_exact.
  apply (dot_rnd_error u Hu rnd Hrnd).
Qed.

(* Attention weighted sum idx (AttnQ q K V) dd: length-n dot product of the
   softmax weights with V column dd. *)
Theorem llama_attn_out_rnd_error : forall (u : R) (Hu : 0 <= u)
    (rnd : R -> R) (Hrnd : forall x:R, Rabs (rnd x - x) <= u * Rabs x)
    (dk n : nat) (Hdk : (dk > 0)%nat) (Hn : (n > 0)%nat)
    (q : exp (ary '{dk} num))
    (K V : exp (ary '{n} (ary '{dk} num))) (dd : fin dk),
  Rabs (dot_rnd rnd (Softmax1d (attn_scores q K)) (attn_out_col V dd)
        - idx (AttnQ q K V) dd)
  <= ((1 + u) ^ S n - 1)
     * v_abs_sum (v_pw2 Rmult n (Softmax1d (attn_scores q K))
                    (attn_out_col V dd)).
Proof.
  intros u Hu rnd Hrnd dk n Hdk Hn q K V dd.
  rewrite attnQ_entry_eq_dot_exact by assumption.
  apply (dot_rnd_error u Hu rnd Hrnd).
Qed.

(* FFN / projection GEMV: entry (i, j) of MatMul2d a w (decode: s = 1). *)
Theorem llama_gemv_rnd_error : forall (u : R) (Hu : 0 <= u)
    (rnd : R -> R) (Hrnd : forall x:R, Rabs (rnd x - x) <= u * Rabs x)
    (m n p : nat) (Hn : (n > 0)%nat)
    (a : exp (ary '{m} (ary '{n} num)))
    (w : exp (ary '{n} (ary '{p} num)))
    (i : fin m) (j : fin p),
  Rabs (dot_rnd rnd (idx a i) (mkvSeq (fun k : fin n => idx (idx w k) j))
        - idx (idx (MatMul2d a w) i) j)
  <= ((1 + u) ^ S n - 1)
     * v_abs_sum (v_pw2 Rmult n (idx a i)
                    (mkvSeq (fun k : fin n => idx (idx w k) j))).
Proof.
  intros u Hu rnd Hrnd m n p Hn a w i j.
  rewrite matmul_entry_eq_dot_exact by exact Hn.
  apply (dot_rnd_error u Hu rnd Hrnd).
Qed.

(* -------------------------------------------------------------------------- *)
(* 3. int8 track: linear (no gamma) worst-case bounds, exact int32 accum.     *)
(* -------------------------------------------------------------------------- *)

(* Attention score with int8-quantized query/key levels (|q| <= 127). *)
Theorem llama_attn_score_int8_error : forall (dk : nat)
    (q kj qq qkj : exp (ary '{dk} num)) (sq sk : R),
  0 <= sq -> 0 <= sk ->
  v_pw_rel (fun t qi => Rabs (sq * t - qi) <= sq / 2) dk qq q ->
  v_pw_rel (fun t ki => Rabs (sk * t - ki) <= sk / 2) dk qkj kj ->
  v_all (fun t => Rabs t <= 127) dk qq ->
  v_all (fun t => Rabs t <= 127) dk qkj ->
  Rabs (dot_int8 sq sk qq qkj - dotr q kj)
  <= sq * sk * INR dk * (509 / 4).
Proof.
  intros dk q kj qq qkj sq sk Hsq Hsk Hq Hk Hq127 Hk127.
  rewrite dotr_eq_dot_exact.
  apply (dot_int8_error_int8 dk q kj qq qkj sq sk Hsq Hsk Hq Hk Hq127 Hk127).
Qed.

(* FFN / projection GEMV entry with int8-quantized activation/weight levels. *)
Theorem llama_gemv_int8_error : forall (m n p : nat) (Hn : (n > 0)%nat)
    (a : exp (ary '{m} (ary '{n} num)))
    (w : exp (ary '{n} (ary '{p} num)))
    (qa qw : exp (ary '{n} num)) (sa sw : R)
    (i : fin m) (j : fin p),
  0 <= sa -> 0 <= sw ->
  v_pw_rel (fun t ai => Rabs (sa * t - ai) <= sa / 2) n qa (idx a i) ->
  v_pw_rel (fun t wi => Rabs (sw * t - wi) <= sw / 2) n qw
    (mkvSeq (fun k : fin n => idx (idx w k) j)) ->
  v_all (fun t => Rabs t <= 127) n qa ->
  v_all (fun t => Rabs t <= 127) n qw ->
  Rabs (dot_int8 sa sw qa qw - idx (idx (MatMul2d a w) i) j)
  <= sa * sw * INR n * (509 / 4).
Proof.
  intros m n p Hn a w qa qw sa sw i j Hsa Hsw Ha Hw Ha127 Hw127.
  rewrite matmul_entry_eq_dot_exact by exact Hn.
  apply (dot_int8_error_int8 n (idx a i)
           (mkvSeq (fun k : fin n => idx (idx w k) j)) qa qw sa sw);
    assumption.
Qed.

(* -------------------------------------------------------------------------- *)
(* 4. LLaMA-mini concrete instances (dk = 16, dm = df = 32, decode s = 1)     *)
(* -------------------------------------------------------------------------- *)

(* Attention score at head dim dk = 16: gamma_17. *)
Corollary llama_mini_attn_score_rnd_error : forall (u : R) (Hu : 0 <= u)
    (rnd : R -> R) (Hrnd : forall x:R, Rabs (rnd x - x) <= u * Rabs x)
    (q kj : exp (ary '{16} num)),
  Rabs (dot_rnd rnd q kj - dotr q kj)
  <= ((1 + u) ^ 17 - 1) * v_abs_sum (v_pw2 Rmult 16 q kj).
Proof.
  intros. apply (llama_attn_score_rnd_error u Hu rnd Hrnd 16).
Qed.

(* Decode-time (b = 1, s = 1) FFN projection x W1 (equally x W3, and the
   df -> dm projection by W2) of LLaMAMini_DPIA.v [SwiGLUFFN], at
   dm = df = 32: entry-level gamma_33 bound. *)
Corollary llama_mini_ffn_decode_rnd_error : forall (u : R) (Hu : 0 <= u)
    (rnd : R -> R) (Hrnd : forall x:R, Rabs (rnd x - x) <= u * Rabs x)
    (x1 : exp (ary '{1} (ary '{1} (ary '{32} num))))
    (w1 : exp (ary '{32} (ary '{32} num)))
    (bb : fin 1) (i : fin 1) (j : fin 32),
  Rabs (dot_rnd rnd (idx (idx x1 bb) i)
          (mkvSeq (fun k : fin 32 => idx (idx w1 k) j))
        - idx (idx (idx (BMatMul2d x1 w1) bb) i) j)
  <= ((1 + u) ^ 33 - 1)
     * v_abs_sum (v_pw2 Rmult 32 (idx (idx x1 bb) i)
                    (mkvSeq (fun k : fin 32 => idx (idx w1 k) j))).
Proof.
  intros u Hu rnd Hrnd x1 w1 bb i j.
  rewrite bmatmul_entry_eq_dot_exact by lia.
  apply (dot_rnd_error u Hu rnd Hrnd).
Qed.

(* -------------------------------------------------------------------------- *)
(* 5. TF32 numerics at LLaMA-mini sizes (u = 2^-11), via Q + vm_compute       *)
(* -------------------------------------------------------------------------- *)

(* gamma_17  = (1+2^-11)^17  - 1 <= 0.00834  (attention scores, dk = 16). *)
Theorem tf32_gamma_attn_dk16 : (1 + u_TF32)^17%nat - 1 <= Q2R (834 # 100000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute.
  reflexivity.
Qed.

(* gamma_33  = (1+2^-11)^33  - 1 <= 0.01624  (FFN/projection GEMV, dm = 32). *)
Theorem tf32_gamma_ffn_dm32 : (1 + u_TF32)^33%nat - 1 <= Q2R (1624 # 100000).
Proof.
  rewrite <- gammaQ_R. apply Qle_Rle. apply Qle_bool_iff. vm_compute.
  reflexivity.
Qed.
