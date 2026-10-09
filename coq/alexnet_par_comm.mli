
type __ = Obj.t

type unit0 =
| Tt

type bool =
| True
| False

type reflect =
| ReflectT
| ReflectF

type nat =
| O
| S of nat

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

val sub : nat -> nat -> nat

val eqb : bool -> bool -> bool

val iff_reflect : bool -> reflect

module Nat :
 sig
  val add : nat -> nat -> nat

  val mul : nat -> nat -> nat

  val sub : nat -> nat -> nat

  val eqb : nat -> nat -> bool

  val leb : nat -> nat -> bool

  val ltb : nat -> nat -> bool

  val pow : nat -> nat -> nat

  val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod

  val div : nat -> nat -> nat

  val modulo : nat -> nat -> nat

  val ltb_spec0 : nat -> nat -> reflect
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

  val compare : z -> z -> comparison

  val max : z -> z -> z

  val to_nat : z -> nat

  val of_nat : nat -> z

  val to_pos : z -> positive

  val sgn : z -> z

  val abs : z -> z

  val ggcd : z -> z -> (z, (z, z) prod) prod
 end

val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1

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

val pos_log2floor_plus1 : positive -> positive

val qbound_lt_ZExp2 : q -> z

val qbound_ltabs_ZExp2 : q -> z

type cReal = { seq : (z -> q); scale : z }

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

val acc_default : data -> acc

val idxAcc : nat -> data -> acc -> fin -> acc

val idx : nat -> data -> exp -> fin -> exp

val zero : exp

val add0 : exp -> exp -> exp

val mul0 : exp -> exp -> exp

val div0 : exp -> exp -> exp

val leExp : exp -> exp -> bexp

val gtExp : exp -> exp -> bexp

val pExp : exp -> exp

val safe_idx_nat : nat -> data -> exp -> nat -> exp

val padding2d : nat -> nat -> data -> nat -> exp -> exp

val padding3d : nat -> nat -> nat -> nat -> exp -> exp

val padding4d : nat -> nat -> nat -> nat -> nat -> exp -> exp

val vrd : data -> string -> exp

val vwt : data -> string -> acc

val mkvAcc : data -> nat -> (fin -> acc) -> acc

val acc_default0 : data -> acc

val idxAcc0 : nat -> data -> acc -> fin -> acc

type comm =
| Skip
| If of bexp * (comm, comm) prod
| Seq of (comm, comm) prod
| Assign of data * (acc, exp) prod
| New of data * ((acc, exp) prod -> comm)
| Loopacc of data * (string -> comm)
| Seqfor of nat * (fin -> comm)
| Parfor of nat * data * acc * (fin -> acc -> comm)

val reLU4d_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm

val linear2d_comm : nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm

val softmax2d_comm : nat -> nat -> exp -> acc -> comm

val reLU2d_comm : nat -> nat -> exp -> acc -> comm

val flatten_idx : nat -> nat -> nat -> fin -> fin -> fin -> fin

val flatten4d_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm

val conv4d_ast_seq_comm :
  nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> exp -> exp
  -> exp -> acc -> comm

val maxpool4d_pad_ast_seq_comm :
  nat -> nat -> nat -> nat -> nat -> nat -> nat -> exp -> acc -> comm

val conv4d_ast_par_comm :
  nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> nat -> exp -> exp
  -> exp -> acc -> comm

val reLU4d_par_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm

val maxpool4d_pad_ast_par_comm :
  nat -> nat -> nat -> nat -> nat -> nat -> nat -> exp -> acc -> comm

val linear2d_par_comm : nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm

val reLU2d_par_comm : nat -> nat -> exp -> acc -> comm

val softmax2d_par_comm : nat -> nat -> exp -> acc -> comm

val tin : data

val tw1 : data

val tb1 : data

val tc1 : data

val tp1 : data

val tw2 : data

val tb2 : data

val tc2 : data

val tp2 : data

val tw3 : data

val tb3 : data

val tc3 : data

val tw4 : data

val tb4 : data

val tc4 : data

val tw5 : data

val tb5 : data

val tc5 : data

val tp5 : data

val tflat : data

val tf1w : data

val tf1b : data

val tfc : data

val tf2w : data

val tf2b : data

val tf3w : data

val tf3b : data

val tout : data

val alexnet_par_gen_comm : comm

val alexnet_seq_gen_comm : comm
