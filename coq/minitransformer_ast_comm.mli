
type __ = Obj.t

type unit0 =
| Tt

type bool =
| True
| False

type nat =
| O
| S of nat

type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b

type ('a, 'b) prod =
| Pair of 'a * 'b

val fst : ('a1, 'a2) prod -> 'a1

val snd : ('a1, 'a2) prod -> 'a2

type comparison =
| Eq
| Lt
| Gt

val compOpp : comparison -> comparison

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val eqb : bool -> bool -> bool

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val pow : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val mul : positive -> positive -> positive

  val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val of_succ_nat : nat -> positive
 end

module Coq_Pos :
 sig
  val succ : positive -> positive

  val add : positive -> positive -> positive

  val add_carry : positive -> positive -> positive

  val pred_double : positive -> positive

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  val succ_double_mask : mask -> mask

  val double_mask : mask -> mask

  val double_pred_mask : positive -> mask

  val sub_mask : positive -> positive -> mask

  val sub_mask_carry : positive -> positive -> mask

  val sub : positive -> positive -> positive

  val mul : positive -> positive -> positive

  val compare_cont : comparison -> positive -> positive -> comparison

  val compare : positive -> positive -> comparison

  val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1

  val to_nat : positive -> nat

  val size_nat : positive -> nat

  val ggcdn :
    nat -> positive -> positive -> (positive, (positive, positive) prod) prod

  val ggcd :
    positive -> positive -> (positive, (positive, positive) prod) prod

  val of_nat : nat -> positive
 end

module Z :
 sig
  val double : z -> z

  val succ_double : z -> z

  val pred_double : z -> z

  val pos_sub : positive -> positive -> z

  val add : z -> z -> z

  val opp : z -> z

  val sub : z -> z -> z

  val mul : z -> z -> z

  val pow_pos : z -> positive -> z

  val pow : z -> z -> z

  val compare : z -> z -> comparison

  val max : z -> z -> z

  val min : z -> z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

val z_lt_dec : z -> z -> sumbool

val z_lt_ge_dec : z -> z -> sumbool

val z_lt_le_dec : z -> z -> sumbool

type q = { qnum : z; qden : positive }

val qplus : q -> q -> q

val qmult : q -> q -> q

val qopp : q -> q

val qminus : q -> q -> q

val qinv : q -> q

val qlt_le_dec : q -> q -> sumbool

val qarchimedean : q -> positive

val qpower_positive : q -> positive -> q

val qpower : q -> z -> q

val qred : q -> q

val qabs : q -> q

val linear_search_conform : (nat -> sumbool) -> nat -> nat

val linear_search_from_0_conform : (nat -> sumbool) -> nat

val constructive_indefinite_ground_description_nat : (nat -> sumbool) -> nat

val p'_decidable : (nat -> 'a1) -> ('a1 -> sumbool) -> nat -> sumbool

val constructive_indefinite_ground_description :
  ('a1 -> nat) -> (nat -> 'a1) -> ('a1 -> sumbool) -> 'a1

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val qbound_ltabs_ZExp2 : q -> z

val z_inj_nat : z -> nat

val z_inj_nat_rev : nat -> z

val constructive_indefinite_ground_description_Z : (z -> sumbool) -> z

type cReal = { seq : (z -> q); scale : z }

type cRealLt = z

type cReal_appart = (cRealLt, cRealLt) sum

val cRealLt_lpo_dec :
  cReal -> cReal -> (__ -> (nat -> sumbool) -> nat sumor) -> (cRealLt, __) sum

val inject_Q : q -> cReal

val cReal_plus_seq : cReal -> cReal -> z -> q

val cReal_plus_scale : cReal -> cReal -> z

val cReal_plus : cReal -> cReal -> cReal

val cReal_opp_seq : cReal -> z -> q

val cReal_opp_scale : cReal -> z

val cReal_opp : cReal -> cReal

val cReal_mult_seq : cReal -> cReal -> z -> q

val cReal_mult_scale : cReal -> cReal -> z

val cReal_mult : cReal -> cReal -> cReal

val cRealLowerBound : cReal -> cRealLt -> z

val cReal_inv_pos_cm : cReal -> cRealLt -> z -> z

val cReal_inv_pos_seq : cReal -> cRealLt -> z -> q

val cReal_inv_pos_scale : cReal -> cRealLt -> z

val cReal_inv_pos : cReal -> cRealLt -> cReal

val cReal_neg_lt_pos : cReal -> cRealLt -> cRealLt

val cReal_inv : cReal -> cReal_appart -> cReal

val cRealLtDisjunctEpsilon :
  cReal -> cReal -> cReal -> cReal -> (cRealLt, cRealLt) sum

val sig_forall_dec : (nat -> sumbool) -> nat sumor

val lowerCutBelow : (q -> bool) -> q

val lowerCutAbove : (q -> bool) -> q

type dReal = (q -> bool)

val dRealQlim_rec : (q -> bool) -> nat -> nat -> q

val dRealAbstr : cReal -> dReal

val dRealQlim : dReal -> nat -> q

val dRealQlimExp2 : dReal -> nat -> q

val cReal_of_DReal_seq : dReal -> z -> q

val cReal_of_DReal_scale : dReal -> z

val dRealRepr : dReal -> cReal

module type RbaseSymbolsSig =
 sig
  type coq_R

  val coq_Rabst : cReal -> coq_R

  val coq_Rrepr : coq_R -> cReal

  val coq_R0 : coq_R

  val coq_R1 : coq_R

  val coq_Rplus : coq_R -> coq_R -> coq_R

  val coq_Rmult : coq_R -> coq_R -> coq_R

  val coq_Ropp : coq_R -> coq_R
 end

module RbaseSymbolsImpl :
 RbaseSymbolsSig

val iPR_2 : positive -> RbaseSymbolsImpl.coq_R

val iPR : positive -> RbaseSymbolsImpl.coq_R

val iZR : z -> RbaseSymbolsImpl.coq_R

val total_order_T :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> sumbool sumor

val req_appart_dec :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> sumbool

val rrepr_appart_0 : RbaseSymbolsImpl.coq_R -> cReal_appart

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl :
 RinvSig

val rdiv :
  RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

val eqb0 : ascii -> ascii -> bool

type string =
| EmptyString
| String of ascii * string

val eqb1 : string -> string -> bool

val append : string -> string -> string

type fin = nat

val fin2nat : nat -> fin -> nat

val fin2finS : nat -> fin -> fin

val nat2fin : nat -> nat -> fin

type fle = nat

val fle2nat : nat -> fle -> nat

val fle_self : nat -> fle

val natToDigit : nat -> ascii

val writeNatAux : nat -> nat -> string -> string

val writeNat : nat -> string

type 'a vector = __

val mk_vec : nat -> (fin -> 'a1) -> 'a1 vector

val v_nth : nat -> 'a1 -> 'a1 vector -> nat -> 'a1

val v_idx : nat -> 'a1 -> 'a1 vector -> fin -> 'a1

val idx_2d_to_1d : nat -> nat -> fin -> fin -> fin

val idx_1d_to_2d : nat -> nat -> fin -> (fin, fin) prod

type data =
| Num
| Ary of nat * fle * data

type path =
| Var of string
| AryIdx of nat * fin * path

type bexp =
| BTrue
| BFalse
| BLe of rexp * rexp
| BGt of rexp * rexp
| BLt of nat * nat
| BEq of nat * nat
| BLeb of nat * nat
| BAnd of bexp * bexp
| BNot of bexp
and rexp =
| REvar of string
| REconst of RbaseSymbolsImpl.coq_R * string
| REopp of rexp
| REadd of rexp * rexp
| REsub of rexp * rexp
| REmul of rexp * rexp
| REdiv of rexp * rexp
| REdiv_n of rexp * nat
| REscal of RbaseSymbolsImpl.coq_R * rexp
| REpow of rexp * nat
| REexp of rexp
| REln of rexp
| REsqrt of rexp
| REif of bexp * rexp * rexp

type exp = __

type acc = __

val mkvSeq : data -> nat -> (fin -> exp) -> exp

val exp_default : data -> exp

val idx : nat -> data -> exp -> fin -> exp

val zero : exp

val one : exp

val negate : exp -> exp

val add0 : exp -> exp -> exp

val mul0 : exp -> exp -> exp

val div0 : exp -> exp -> exp

val div_n : exp -> nat -> exp

val sub0 : exp -> exp -> exp

val pExp : exp -> exp

val sqrt : exp -> exp

val vrd : data -> string -> exp

val vwt : data -> string -> acc

val mkvAcc : data -> nat -> (fin -> acc) -> acc

val acc_default : data -> acc

val idxAcc : nat -> data -> acc -> fin -> acc

type comm =
| Skip
| If of bexp * (comm, comm) prod
| Seq of (comm, comm) prod
| Assign of data * (acc, exp) prod
| New of data * ((acc, exp) prod -> comm)
| Loopacc of data * (string -> comm)
| Seqfor of nat * (fin -> comm)
| Parfor of nat * data * acc * (fin -> acc -> comm)

val mt_eps : exp

val mt_neginf : exp

val mt_half : exp

val mt_sqrt_2_pi : exp

val mt_cubic : exp

val mt_attn_scale : exp

val mt_tanh_r : exp -> exp

val mt_gelu_r : exp -> exp

val mt_ln_cell : exp -> exp -> exp -> exp -> exp -> exp

val t1 : data

val t2 : data

val t3 : data

val t4H : data

val t4S : data

val t2H : data

val t3O : data

val i0_1 : fin

val tok_tab : exp

val pos_tab : exp

val l1_ln1_g : exp

val l1_ln1_b : exp

val l1_ln2_g : exp

val l1_ln2_b : exp

val l1_wq : exp

val l1_wk : exp

val l1_wv : exp

val l1_wo : exp

val l1_w1 : exp

val l1_w2 : exp

val l2_ln1_g : exp

val l2_ln1_b : exp

val l2_ln2_g : exp

val l2_ln2_b : exp

val l2_wq : exp

val l2_wk : exp

val l2_wv : exp

val l2_wo : exp

val l2_w1 : exp

val l2_w2 : exp

val lnf_g : exp

val lnf_b : exp

val whead : exp

val l1_w : acc

val l1_r : exp

val l2_w : acc

val l2_r : exp

val l3_w : acc

val l3_r : exp

val l4_w : acc

val l4_r : exp

val bln1_w : acc

val bln1_r : exp

val bmha_w : acc

val bmha_r : exp

val br1_w : acc

val br1_r : exp

val bln2_w : acc

val bln2_r : exp

val btf1_w : acc

val btf1_r : exp

val btg_w : acc

val btg_r : exp

val btf2_w : acc

val btf2_r : exp

val mtq_w : acc

val mtq_r : exp

val mtk_w : acc

val mtk_r : exp

val mtv_w : acc

val mtv_r : exp

val mtmg_w : acc

val mtmg_r : exp

val mtqs_w : acc

val mtqs_r : exp

val mtks_w : acc

val mtks_r : exp

val mtvs_w : acc

val mtvs_r : exp

val mtatt_w : acc

val mtatt_r : exp

val mtscore_w : acc

val mtscore_r : exp

val mtprob_w : acc

val mtprob_r : exp

val output_w : acc

val mt_tok : nat -> fin

val mt_embed_pos_comm : acc -> fin -> fin -> comm

val mt_embed_comm : comm

val mt_ln_row_comm : exp -> exp -> exp -> acc -> comm

val mt_layernorm_comm : exp -> exp -> exp -> acc -> comm

val mt_bmm_row_comm : nat -> nat -> exp -> exp -> acc -> comm

val mt_bmm_comm : nat -> nat -> exp -> exp -> acc -> comm

val mt_splitheads_comm : exp -> acc -> comm

val mt_mergeheads_comm : exp -> acc -> comm

val mt_attn_head_comm :
  exp -> exp -> exp -> exp -> exp -> acc -> acc -> acc -> comm

val mt_attnheads_comm : exp -> exp -> exp -> acc -> comm

val mt_gelu3d_comm : exp -> acc -> comm

val mt_add3d_comm : exp -> exp -> acc -> comm

val mt_block_comm :
  exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp
  -> acc -> comm

val minitransformer_ast_comm : comm
