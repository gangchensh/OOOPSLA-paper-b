(* ========================================================================= *)
(* MiniTransformer_AST.v                                                     *)
(*                                                                           *)
(* Route-B (AST / code-generation) version of the mini GPT-style             *)
(* decoder-only network whose route-A DPIA correctness theorem               *)
(* [MiniTransformer_DPIA.A_MiniTransformer] was proved in milestone T4       *)
(* (cf. doc/Transformer扩展开发规划_20260829.md).  This file is milestone    *)
(* T5: it builds the concrete imperative AST at the small instance           *)
(* b = 1, s = 8, h = 2, d = 16 (model dim 32), df = 32, vocab v = 8,         *)
(* in both sequential and OpenMP-parallel ([parfor]) variants, proves the    *)
(* two variants denotationally equal under [eval] (the [LeNet5_Par]          *)
(* pattern), and extracts the ASTs for the streaming OCaml printers.         *)
(*                                                                           *)
(* Stage structure mirrors [MiniTransformer_DPIA.minitransformer_comm]       *)
(* one-to-one (same buffers, same order):                                    *)
(*                                                                           *)
(*   l1 = embed(toks) + pos        (Gather2d + Add3d; see the note on the    *)
(*   l2 = TransformerBlock l1       token unrolling below)                   *)
(*   l3 = TransformerBlock l2                                                *)
(*   l4 = LayerNorm l3                                                       *)
(*   output = l4 @ whead                                                   *)
(*                                                                           *)
(*   TransformerBlock x =                                                    *)
(*     bln1 = LN(x);  mtq/mtk/mtv = bln1 Wq/Wk/Wv;  mt*s = split heads;      *)
(*     mtatt = per-head softmax(causal(QK^T/sqrt(d))) V  (staged through     *)
(*     mtscore/mtprob);  mtmg = merge heads;  bmha = mtmg Wo;                *)
(*     br1 = x + bmha;  bln2 = LN(br1);  btf1 = bln2 W1;  btg = GELU(btf1);  *)
(*     btf2 = btg W2;  out = br1 + btf2                                      *)
(*                                                                           *)
(* Differences from route A (documented as trust boundaries in the T5        *)
(* report):                                                                  *)
(*   1. The embedding Gather2d loop is unrolled over the 8 positions with    *)
(*      the (compile-time) token index of each position inlined, because a   *)
(*      Coq-level index map [toks : fin 8 -> fin 8] cannot be evaluated on   *)
(*      the symbolic loop indices used by extraction-based code generation.  *)
(*      Pointwise the same values result.                                    *)
(*   2. The attention cell is staged through score/probability buffers       *)
(*      instead of the route-A recompute-per-element composed expression     *)
(*      ([attention_cell_comm]); same arithmetic, different staging.         *)
(*   3. LayerNorm mean/variance are computed once per row in [loopacc]       *)
(*      accumulators instead of being recomputed per output element          *)
(*      ([A_LNcell]); same values, fewer FLOPs.                              *)
(*   4. Scalar constants (eps = 1e-5, NEGINF = -1e30, the GELU constants,    *)
(*      the attention scale) are [REconst] leaves carrying both their exact  *)
(*      real value (used by [eval]) and the C literal string (used by the    *)
(*      printer).                                                            *)
(*                                                                           *)
(* This file modifies nothing else; it is in _CoqProject (main build).       *)
(* ========================================================================= *)

From Stdlib Require Import Reals Lia.
Require Import Ionia.CNN_Examples_Base.
Require Import Ionia.CNN_Examples_Base_Ops.
Require Import Ionia.CNN_CodeGen_Semantics.

From Stdlib Require Import String List.
Import ListNotations.
Open Scope string_scope.
Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* Scalar constants (exact real value for [eval], C literal for the printer) *)
(* -------------------------------------------------------------------------- *)

Definition mt_eps : exp num := REconst (1 / IZR 100000)%R "1e-5".
Definition mt_neginf : exp num := REconst (- IZR (10 ^ 30)%Z)%R "-1e30".
Definition mt_half : exp num := REconst (1 / 2)%R "0.5".
(* NOTE: the real component of an [REconst] is evaluated eagerly by the
   extracted OCaml when the AST is built.  [R_sqrt.sqrt] and [PI] pull in the
   un-realisable classical axiom [ClassicalDedekindReals.sig_not_dec]
   (verified by single-constant extraction tests), so the real component of
   [mt_sqrt_2_pi] is a rational approximation of sqrt(2/pi); the printer only
   emits the string component.  (Rdiv/Ropp/IZR are extraction-safe.) *)
Definition mt_sqrt_2_pi : exp num :=
  REconst (IZR 7978845608028654 / IZR (10 ^ 16)%Z)%R "0.7978845608028654".
Definition mt_cubic : exp num := REconst (44715 / 1000000)%R "0.044715".
(* Attention scale 1/sqrt(16), cf. [Attention_DPIA.attn_scale]. *)
Definition mt_attn_scale : exp num := div one (sqrt (REconst (IZR 16) "16")).

(* GELU, tanh approximation (cf. [Ops_Transformer.gelu]). *)
Definition mt_tanh_r (x : exp num) : exp num :=
  div (sub (pExp x) (pExp (negate x)))
      (add (pExp x) (pExp (negate x))).

Definition mt_gelu_r (x : exp num) : exp num :=
  mul (mul mt_half x)
      (add one (mt_tanh_r (mul mt_sqrt_2_pi
                                (add x (mul mt_cubic (mul (mul x x) x)))))).

(* LayerNorm cell (cf. [Ops_BatchNorm.BNcell]). *)
Definition mt_ln_cell (x mean var g b : exp num) : exp num :=
  add (mul g (div (sub x mean) (sqrt (add var mt_eps)))) b.

(* -------------------------------------------------------------------------- *)
(* Type abbreviations (concrete instance sizes)                               *)
(* -------------------------------------------------------------------------- *)

Definition T1 := ary '{32} num.                              (* model dim vector *)
Definition T2 := ary '{32} (ary '{32} num).                  (* 32x32 matrix *)
Definition T3 := ary '{1} (ary '{8} (ary '{32} num)).        (* (b,s,dm) *)
Definition T4H := ary '{1} (ary '{2} (ary '{8} (ary '{16} num))). (* (b,h,s,d) *)
Definition T4S := ary '{1} (ary '{2} (ary '{8} (ary '{8} num))).  (* (b,h,s,s) *)
Definition T2H := ary '{32} (ary '{8} num).                  (* head matrix *)
Definition T3O := ary '{1} (ary '{8} (ary '{8} num)).        (* (b,s,v) logits *)

Definition i0_1 : fin 1 := nat2fin (Nat.lt_0_succ 0).

(* -------------------------------------------------------------------------- *)
(* Inputs, weights, buffers                                                   *)
(* -------------------------------------------------------------------------- *)

Definition tok_tab : exp (ary '{8} (ary '{32} num)) := vrd "tok_tab".
Definition pos_tab : exp (ary '{8} (ary '{32} num)) := vrd "pos_tab".

Definition l1_ln1_g : exp T1 := vrd "l1_ln1_g".
Definition l1_ln1_b : exp T1 := vrd "l1_ln1_b".
Definition l1_ln2_g : exp T1 := vrd "l1_ln2_g".
Definition l1_ln2_b : exp T1 := vrd "l1_ln2_b".
Definition l1_wq : exp T2 := vrd "l1_wq".
Definition l1_wk : exp T2 := vrd "l1_wk".
Definition l1_wv : exp T2 := vrd "l1_wv".
Definition l1_wo : exp T2 := vrd "l1_wo".
Definition l1_w1 : exp T2 := vrd "l1_w1".
Definition l1_w2 : exp T2 := vrd "l1_w2".

Definition l2_ln1_g : exp T1 := vrd "l2_ln1_g".
Definition l2_ln1_b : exp T1 := vrd "l2_ln1_b".
Definition l2_ln2_g : exp T1 := vrd "l2_ln2_g".
Definition l2_ln2_b : exp T1 := vrd "l2_ln2_b".
Definition l2_wq : exp T2 := vrd "l2_wq".
Definition l2_wk : exp T2 := vrd "l2_wk".
Definition l2_wv : exp T2 := vrd "l2_wv".
Definition l2_wo : exp T2 := vrd "l2_wo".
Definition l2_w1 : exp T2 := vrd "l2_w1".
Definition l2_w2 : exp T2 := vrd "l2_w2".

Definition lnf_g : exp T1 := vrd "lnf_g".
Definition lnf_b : exp T1 := vrd "lnf_b".
Definition whead : exp T2H := vrd "whead".

Definition l1_w : acc T3 := vwt "l1".
Definition l1_r : exp T3 := vrd "l1".
Definition l2_w : acc T3 := vwt "l2".
Definition l2_r : exp T3 := vrd "l2".
Definition l3_w : acc T3 := vwt "l3".
Definition l3_r : exp T3 := vrd "l3".
Definition l4_w : acc T3 := vwt "l4".
Definition l4_r : exp T3 := vrd "l4".

Definition bln1_w : acc T3 := vwt "bln1".
Definition bln1_r : exp T3 := vrd "bln1".
Definition bmha_w : acc T3 := vwt "bmha".
Definition bmha_r : exp T3 := vrd "bmha".
Definition br1_w : acc T3 := vwt "br1".
Definition br1_r : exp T3 := vrd "br1".
Definition bln2_w : acc T3 := vwt "bln2".
Definition bln2_r : exp T3 := vrd "bln2".
Definition btf1_w : acc T3 := vwt "btf1".
Definition btf1_r : exp T3 := vrd "btf1".
Definition btg_w : acc T3 := vwt "btg".
Definition btg_r : exp T3 := vrd "btg".
Definition btf2_w : acc T3 := vwt "btf2".
Definition btf2_r : exp T3 := vrd "btf2".

Definition mtq_w : acc T3 := vwt "mtq".
Definition mtq_r : exp T3 := vrd "mtq".
Definition mtk_w : acc T3 := vwt "mtk".
Definition mtk_r : exp T3 := vrd "mtk".
Definition mtv_w : acc T3 := vwt "mtv".
Definition mtv_r : exp T3 := vrd "mtv".
Definition mtmg_w : acc T3 := vwt "mtmg".
Definition mtmg_r : exp T3 := vrd "mtmg".

Definition mtqs_w : acc T4H := vwt "mtqs".
Definition mtqs_r : exp T4H := vrd "mtqs".
Definition mtks_w : acc T4H := vwt "mtks".
Definition mtks_r : exp T4H := vrd "mtks".
Definition mtvs_w : acc T4H := vwt "mtvs".
Definition mtvs_r : exp T4H := vrd "mtvs".
Definition mtatt_w : acc T4H := vwt "mtatt".
Definition mtatt_r : exp T4H := vrd "mtatt".

Definition mtscore_w : acc T4S := vwt "mtscore".
Definition mtscore_r : exp T4S := vrd "mtscore".
Definition mtprob_w : acc T4S := vwt "mtprob".
Definition mtprob_r : exp T4S := vrd "mtprob".

Definition output_w : acc T3O := vwt "output".

(* -------------------------------------------------------------------------- *)
(* Embedding (Gather2d + position add), unrolled over the 8 positions.        *)
(* The token index of each position is a compile-time constant (the token    *)
(* sequence is baked into the generated code, as in the route-A model where  *)
(* [toks] is a host-level index function).  Token sequence: 3,1,4,1,5,2,6,0. *)
(*                                                                           *)
(* Kept SEQUENTIAL in both variants (256 cheap assignments, like LeNet-5's   *)
(* flatten).  A parfor directly over the j loop would also be a candidate,   *)
(* but the [eval]-side par/seq conversion lemma for a concrete-length parfor *)
(* whose body is a bare indexed assignment does not close by [reflexivity]   *)
(* in practice (the concrete [PCG.seqfor] iota-unrolls and conversion        *)
(* explodes; nested-loop bodies are fine).                                   *)
(* -------------------------------------------------------------------------- *)

Definition mt_tok (i : nat) (H : i < 8) : fin 8 := nat2fin H.

Definition mt_embed_pos_comm (out : acc T3) (p tk : fin 8) : comm :=
  seqfor (fun j : fin 32 =>
    out|{i0_1}|{p}|{j} |:= add tok_tab|[tk]|[j] pos_tab|[p]|[j]).

Definition mt_embed_comm : comm :=
  mt_embed_pos_comm l1_w (@mt_tok 0 (ltac:(lia))) (@mt_tok 3 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 1 (ltac:(lia))) (@mt_tok 1 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 2 (ltac:(lia))) (@mt_tok 4 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 3 (ltac:(lia))) (@mt_tok 1 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 4 (ltac:(lia))) (@mt_tok 5 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 5 (ltac:(lia))) (@mt_tok 2 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 6 (ltac:(lia))) (@mt_tok 6 (ltac:(lia))) ';
  mt_embed_pos_comm l1_w (@mt_tok 7 (ltac:(lia))) (@mt_tok 0 (ltac:(lia))).

(* -------------------------------------------------------------------------- *)
(* LayerNorm (b,s,dm), mean/variance cached in loopacc accumulators           *)
(* -------------------------------------------------------------------------- *)

Definition mt_ln_row_comm
  (x : exp (ary '{32} num)) (g b : exp (ary '{32} num))
  (out : acc (ary '{32} num)) : comm :=
  @loopacc num (fun t1 =>
    let w1 := vwt t1 in let v1 := vrd t1 in
    (w1 |:= zero) ';
    seqfor (fun j : fin 32 => w1 |:= add x|[j] v1) ';
    @loopacc num (fun t2 =>
      let w2 := vwt t2 in let v2 := vrd t2 in
      (w2 |:= zero) ';
      seqfor (fun j : fin 32 =>
        w2 |:= add (mul (sub x|[j] (div_n v1 32)) (sub x|[j] (div_n v1 32))) v2) ';
      seqfor (fun j : fin 32 =>
        out|{j} |:= mt_ln_cell x|[j] (div_n v1 32) (div_n v2 32) g|[j] b|[j]))).

Definition mt_layernorm_comm
  (x : exp T3) (g b : exp T1) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => seqfor (fun ss : fin 8 =>
    mt_ln_row_comm x|[bb]|[ss] g b (out|{bb}|{ss}))).

Definition mt_layernorm_par_comm
  (x : exp T3) (g b : exp T1) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => parfor (out|{bb}) (fun ss o =>
    mt_ln_row_comm x|[bb]|[ss] g b o)).

(* -------------------------------------------------------------------------- *)
(* Batched right-multiplication x @ w, (1,8,n) @ (n,p) -> (1,8,p)             *)
(* -------------------------------------------------------------------------- *)

Definition mt_bmm_row_comm {n p : nat}
  (x : exp (ary '{8} (ary '{n} num))) (w : exp (ary '{n} (ary '{p} num)))
  (out : acc (ary '{8} (ary '{p} num))) : comm :=
  seqfor (fun ss : fin 8 => seqfor (fun j : fin p =>
    @loopacc num (fun tmp =>
      let wa := vwt tmp in let va := vrd tmp in
      (wa |:= zero) ';
      seqfor (fun k : fin n => wa |:= add (mul x|[ss]|[k] w|[k]|[j]) va) ';
      out|{ss}|{j} |:= va))).

Definition mt_bmm_row_par_comm {n p : nat}
  (x : exp (ary '{8} (ary '{n} num))) (w : exp (ary '{n} (ary '{p} num)))
  (out : acc (ary '{8} (ary '{p} num))) : comm :=
  parfor out (fun ss o => seqfor (fun j : fin p =>
    @loopacc num (fun tmp =>
      let wa := vwt tmp in let va := vrd tmp in
      (wa |:= zero) ';
      seqfor (fun k : fin n => wa |:= add (mul x|[ss]|[k] w|[k]|[j]) va) ';
      o|{j} |:= va))).

Definition mt_bmm_comm {n p : nat}
  (x : exp (ary '{1} (ary '{8} (ary '{n} num))))
  (w : exp (ary '{n} (ary '{p} num)))
  (out : acc (ary '{1} (ary '{8} (ary '{p} num)))) : comm :=
  seqfor (fun bb : fin 1 => mt_bmm_row_comm x|[bb] w (out|{bb})).

Definition mt_bmm_par_comm {n p : nat}
  (x : exp (ary '{1} (ary '{8} (ary '{n} num))))
  (w : exp (ary '{n} (ary '{p} num)))
  (out : acc (ary '{1} (ary '{8} (ary '{p} num)))) : comm :=
  seqfor (fun bb : fin 1 => mt_bmm_row_par_comm x|[bb] w (out|{bb})).

(* -------------------------------------------------------------------------- *)
(* Head split (1,8,32) -> (1,2,8,16) and merge back (both sequential: pure    *)
(* index permutations, the Flatten family; cf. LeNet5's sequential flatten)   *)
(* -------------------------------------------------------------------------- *)

Definition mt_splitheads_comm (x : exp T3) (out : acc T4H) : comm :=
  seqfor (fun bb : fin 1 => seqfor (fun hh : fin 2 =>
    seqfor (fun ss : fin 8 => seqfor (fun dd : fin 16 =>
      out|{bb}|{hh}|{ss}|{dd} |:= x|[bb]|[ss]|[idx_2d_to_1d hh dd])))).

Definition mt_mergeheads_comm (x : exp T4H) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => seqfor (fun ss : fin 8 =>
    seqfor (fun xx : fin 32 =>
      out|{bb}|{ss}|{xx} |:=
        x|[bb]|[fst (@idx_1d_to_2d 2 16 xx)]|[ss]|[snd (@idx_1d_to_2d 2 16 xx)]))).

(* -------------------------------------------------------------------------- *)
(* Single-head causal attention cell, row by row:                             *)
(*   score[i][j] = (QK^T)[i][j] / sqrt(16)  if j <= i,  -1e30 otherwise       *)
(*   prob[i][:]  = softmax(score[i][:])                                        *)
(*   out[i][j]   = sum_l prob[i][l] * V[l][j]                                  *)
(* -------------------------------------------------------------------------- *)

Definition mt_attn_head_comm
  (q k v : exp (ary '{8} (ary '{16} num)))
  (score_r prob_r : exp (ary '{8} (ary '{8} num)))
  (score_a prob_a : acc (ary '{8} (ary '{8} num)))
  (out : acc (ary '{8} (ary '{16} num))) : comm :=
  seqfor (fun i : fin 8 =>
    (seqfor (fun j : fin 8 =>
      If (BLeb (fin2nat j) (fin2nat i))
        (@loopacc num (fun tmp =>
          let wa := vwt tmp in let va := vrd tmp in
          (wa |:= zero) ';
          seqfor (fun kk : fin 16 => wa |:= add (mul q|[i]|[kk] k|[j]|[kk]) va) ';
          score_a|{i}|{j} |:= mul mt_attn_scale va),
         score_a|{i}|{j} |:= mt_neginf))) ';
    (@loopacc num (fun tmp =>
      let wa := vwt tmp in let va := vrd tmp in
      (wa |:= zero) ';
      seqfor (fun j : fin 8 => wa |:= add (pExp score_r|[i]|[j]) va) ';
      seqfor (fun j : fin 8 => prob_a|{i}|{j} |:= div (pExp score_r|[i]|[j]) va))) ';
    (seqfor (fun j : fin 16 =>
      @loopacc num (fun tmp =>
        let wa := vwt tmp in let va := vrd tmp in
        (wa |:= zero) ';
        seqfor (fun l : fin 8 => wa |:= add (mul prob_r|[i]|[l] v|[l]|[j]) va) ';
        out|{i}|{j} |:= va)))).

Definition mt_attnheads_comm (qs ks vs : exp T4H) (out : acc T4H) : comm :=
  seqfor (fun bb : fin 1 => seqfor (fun hh : fin 2 =>
    mt_attn_head_comm qs|[bb]|[hh] ks|[bb]|[hh] vs|[bb]|[hh]
      mtscore_r|[bb]|[hh] mtprob_r|[bb]|[hh]
      (mtscore_w|{bb}|{hh}) (mtprob_w|{bb}|{hh}) (out|{bb}|{hh}))).

Definition mt_attnheads_par_comm (qs ks vs : exp T4H) (out : acc T4H) : comm :=
  seqfor (fun bb : fin 1 => parfor (out|{bb}) (fun hh oh =>
    mt_attn_head_comm qs|[bb]|[hh] ks|[bb]|[hh] vs|[bb]|[hh]
      mtscore_r|[bb]|[hh] mtprob_r|[bb]|[hh]
      (mtscore_w|{bb}|{hh}) (mtprob_w|{bb}|{hh}) oh)).

(* -------------------------------------------------------------------------- *)
(* GELU and residual add, (b,s,dm) elementwise                                *)
(* -------------------------------------------------------------------------- *)

Definition mt_gelu3d_comm (x : exp T3) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => seqfor (fun ss : fin 8 => seqfor (fun j : fin 32 =>
    out|{bb}|{ss}|{j} |:= mt_gelu_r x|[bb]|[ss]|[j]))).

Definition mt_gelu3d_par_comm (x : exp T3) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => parfor (out|{bb}) (fun ss o =>
    seqfor (fun j : fin 32 => o|{j} |:= mt_gelu_r x|[bb]|[ss]|[j]))).

Definition mt_add3d_comm (x y : exp T3) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => seqfor (fun ss : fin 8 => seqfor (fun j : fin 32 =>
    out|{bb}|{ss}|{j} |:= add x|[bb]|[ss]|[j] y|[bb]|[ss]|[j]))).

Definition mt_add3d_par_comm (x y : exp T3) (out : acc T3) : comm :=
  seqfor (fun bb : fin 1 => parfor (out|{bb}) (fun ss o =>
    seqfor (fun j : fin 32 => o|{j} |:= add x|[bb]|[ss]|[j] y|[bb]|[ss]|[j]))).

(* -------------------------------------------------------------------------- *)
(* Transformer block (pre-norm), cf. [MiniTransformer_DPIA.TransformerBlock] *)
(* -------------------------------------------------------------------------- *)

Definition mt_block_comm
  (x : exp T3)
  (ln1_g ln1_b ln2_g ln2_b : exp T1)
  (wq wk wv wo w1 w2 : exp T2)
  (out : acc T3) : comm :=
  mt_layernorm_comm x ln1_g ln1_b bln1_w ';
  mt_bmm_comm bln1_r wq mtq_w ';
  mt_splitheads_comm mtq_r mtqs_w ';
  mt_bmm_comm bln1_r wk mtk_w ';
  mt_splitheads_comm mtk_r mtks_w ';
  mt_bmm_comm bln1_r wv mtv_w ';
  mt_splitheads_comm mtv_r mtvs_w ';
  mt_attnheads_comm mtqs_r mtks_r mtvs_r mtatt_w ';
  mt_mergeheads_comm mtatt_r mtmg_w ';
  mt_bmm_comm mtmg_r wo bmha_w ';
  mt_add3d_comm x bmha_r br1_w ';
  mt_layernorm_comm br1_r ln2_g ln2_b bln2_w ';
  mt_bmm_comm bln2_r w1 btf1_w ';
  mt_gelu3d_comm btf1_r btg_w ';
  mt_bmm_comm btg_r w2 btf2_w ';
  mt_add3d_comm br1_r btf2_r out.

Definition mt_block_par_comm
  (x : exp T3)
  (ln1_g ln1_b ln2_g ln2_b : exp T1)
  (wq wk wv wo w1 w2 : exp T2)
  (out : acc T3) : comm :=
  mt_layernorm_par_comm x ln1_g ln1_b bln1_w ';
  mt_bmm_par_comm bln1_r wq mtq_w ';
  mt_splitheads_comm mtq_r mtqs_w ';
  mt_bmm_par_comm bln1_r wk mtk_w ';
  mt_splitheads_comm mtk_r mtks_w ';
  mt_bmm_par_comm bln1_r wv mtv_w ';
  mt_splitheads_comm mtv_r mtvs_w ';
  mt_attnheads_par_comm mtqs_r mtks_r mtvs_r mtatt_w ';
  mt_mergeheads_comm mtatt_r mtmg_w ';
  mt_bmm_par_comm mtmg_r wo bmha_w ';
  mt_add3d_par_comm x bmha_r br1_w ';
  mt_layernorm_par_comm br1_r ln2_g ln2_b bln2_w ';
  mt_bmm_par_comm bln2_r w1 btf1_w ';
  mt_gelu3d_par_comm btf1_r btg_w ';
  mt_bmm_par_comm btg_r w2 btf2_w ';
  mt_add3d_par_comm br1_r btf2_r out.

(* -------------------------------------------------------------------------- *)
(* Whole network: embed + 2 x block + final LN + output head                  *)
(* -------------------------------------------------------------------------- *)

Definition minitransformer_ast_comm : comm :=
  mt_embed_comm ';
  mt_block_comm l1_r l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 l2_w ';
  mt_block_comm l2_r l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 l3_w ';
  mt_layernorm_comm l3_r lnf_g lnf_b l4_w ';
  mt_bmm_comm l4_r whead output_w.

Definition minitransformer_ast_par_comm : comm :=
  mt_embed_comm ';
  mt_block_par_comm l1_r l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b
                    l1_wq l1_wk l1_wv l1_wo l1_w1 l1_w2 l2_w ';
  mt_block_par_comm l2_r l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b
                    l2_wq l2_wk l2_wv l2_wo l2_w1 l2_w2 l3_w ';
  mt_layernorm_par_comm l3_r lnf_g lnf_b l4_w ';
  mt_bmm_par_comm l4_r whead output_w.

(* -------------------------------------------------------------------------- *)
(* Correctness of the parallel variant: eval par = eval seq                   *)
(* (the [LeNet5_Par] pattern: [eval] maps [CG.parfor] to [PCG.seqfor], so    *)
(* each stage equality closes by conversion)                                  *)
(* -------------------------------------------------------------------------- *)

Lemma eval_seq_congr : forall c1 c1' c2 c2' rho,
  (forall r, eval c1 r = eval c1' r) ->
  (forall r, eval c2 r = eval c2' r) ->
  eval (c1 '; c2) rho = eval (c1' '; c2') rho.
Proof.
  intros c1 c1' c2 c2' rho H1 H2.
  unfold eval in *. rewrite !eval_seq_aux.
  unfold PCG.seq. rewrite H1, H2. reflexivity.
Qed.

Lemma mt_layernorm_par_eval : forall x g b out rho,
  eval (mt_layernorm_par_comm x g b out) rho =
  eval (mt_layernorm_comm x g b out) rho.
Proof. intros. reflexivity. Qed.

Lemma mt_bmm_par_eval : forall n p x w out rho,
  eval (@mt_bmm_par_comm n p x w out) rho = eval (@mt_bmm_comm n p x w out) rho.
Proof. intros. reflexivity. Qed.

Lemma mt_attnheads_par_eval : forall qs ks vs out rho,
  eval (mt_attnheads_par_comm qs ks vs out) rho =
  eval (mt_attnheads_comm qs ks vs out) rho.
Proof. intros. reflexivity. Qed.

Lemma mt_gelu3d_par_eval : forall x out rho,
  eval (mt_gelu3d_par_comm x out) rho = eval (mt_gelu3d_comm x out) rho.
Proof. intros. reflexivity. Qed.

Lemma mt_add3d_par_eval : forall x y out rho,
  eval (mt_add3d_par_comm x y out) rho = eval (mt_add3d_comm x y out) rho.
Proof. intros. reflexivity. Qed.

Lemma mt_block_par_eval : forall x ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 out rho,
  eval (mt_block_par_comm x ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 out) rho =
  eval (mt_block_comm x ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 out) rho.
Proof.
  intros. unfold mt_block_par_comm, mt_block_comm.
  apply eval_seq_congr; [ intros r; apply mt_layernorm_par_eval |].
  intros r. apply eval_seq_congr; [ intros r0; apply mt_bmm_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; reflexivity (* split *) |].
  intros r1. apply eval_seq_congr; [ intros r2; apply mt_bmm_par_eval |].
  intros r2. apply eval_seq_congr; [ intros r3; reflexivity (* split *) |].
  intros r3. apply eval_seq_congr; [ intros r4; apply mt_bmm_par_eval |].
  intros r4. apply eval_seq_congr; [ intros r5; reflexivity (* split *) |].
  intros r5. apply eval_seq_congr; [ intros r6; apply mt_attnheads_par_eval |].
  intros r6. apply eval_seq_congr; [ intros r7; reflexivity (* merge *) |].
  intros r7. apply eval_seq_congr; [ intros r8; apply mt_bmm_par_eval |].
  intros r8. apply eval_seq_congr; [ intros r9; apply mt_add3d_par_eval |].
  intros r9. apply eval_seq_congr; [ intros r10; apply mt_layernorm_par_eval |].
  intros r10. apply eval_seq_congr; [ intros r11; apply mt_bmm_par_eval |].
  intros r11. apply eval_seq_congr; [ intros r12; apply mt_gelu3d_par_eval |].
  intros r12. apply eval_seq_congr; [ intros r13; apply mt_bmm_par_eval |].
  intros r13. apply mt_add3d_par_eval.
Qed.

(* The parallel net has the same denotation as the sequential net. *)
Theorem minitransformer_ast_par_eval_eq : forall rho,
  eval minitransformer_ast_par_comm rho = eval minitransformer_ast_comm rho.
Proof.
  intros rho. unfold minitransformer_ast_par_comm, minitransformer_ast_comm.
  apply eval_seq_congr; [ intros r; reflexivity (* embed: identical *) |].
  intros r. apply eval_seq_congr; [ intros r0; apply mt_block_par_eval |].
  intros r0. apply eval_seq_congr; [ intros r1; apply mt_block_par_eval |].
  intros r1. apply eval_seq_congr; [ intros r2; apply mt_layernorm_par_eval |].
  intros r2. apply mt_bmm_par_eval.
Qed.

(* -------------------------------------------------------------------------- *)
(* Extraction for the streaming printers                                      *)
(* -------------------------------------------------------------------------- *)

Extraction "minitransformer_ast_comm.ml" minitransformer_ast_comm.
Extraction "minitransformer_ast_par_comm.ml" minitransformer_ast_par_comm.
