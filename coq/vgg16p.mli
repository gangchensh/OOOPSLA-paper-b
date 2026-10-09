
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

type uint =
| Nil
| D0 of uint
| D1 of uint
| D2 of uint
| D3 of uint
| D4 of uint
| D5 of uint
| D6 of uint
| D7 of uint
| D8 of uint
| D9 of uint

type uint0 =
| Nil0
| D10 of uint0
| D11 of uint0
| D12 of uint0
| D13 of uint0
| D14 of uint0
| D15 of uint0
| D16 of uint0
| D17 of uint0
| D18 of uint0
| D19 of uint0
| Da of uint0
| Db of uint0
| Dc of uint0
| Dd of uint0
| De of uint0
| Df of uint0

type uint1 =
| UIntDecimal of uint
| UIntHexadecimal of uint0

val pred : nat -> nat

val add : nat -> nat -> nat

val mul : nat -> nat -> nat

val sub : nat -> nat -> nat

val tail_add : nat -> nat -> nat

val tail_addmul : nat -> nat -> nat -> nat

val tail_mul : nat -> nat -> nat

val of_uint_acc : uint -> nat -> nat

val of_uint : uint -> nat

val of_hex_uint_acc : uint0 -> nat -> nat

val of_hex_uint : uint0 -> nat

val of_num_uint : uint1 -> nat

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

val idx : nat -> data -> exp -> fin -> exp

val zero : exp

val add0 : exp -> exp -> exp

val mul0 : exp -> exp -> exp

val leExp : exp -> exp -> bexp

val gtExp : exp -> exp -> bexp

val safe_idx_nat : nat -> data -> exp -> nat -> exp

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

val reLU4d_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm

val linear2d_comm : nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm

val reLU2d_comm : nat -> nat -> exp -> acc -> comm

val flatten_idx : nat -> nat -> nat -> fin -> fin -> fin -> fin

val conv4d_p1_k3_comm :
  nat -> nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm

val maxPool4d_k2_comm : nat -> nat -> nat -> exp -> acc -> comm

val flatten4d_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm

val vgg16_input : exp

val vgg16_conv1_1_w : exp

val vgg16_conv1_1_b : exp

val vgg16_conv1_1_out : acc

val vgg16_relu1_1_out : acc

val vgg16_conv1_2_w : exp

val vgg16_conv1_2_b : exp

val vgg16_conv1_2_out : acc

val vgg16_relu1_2_out : acc

val vgg16_conv2_1_w : exp

val vgg16_conv2_1_b : exp

val vgg16_conv2_1_out : acc

val vgg16_relu2_1_out : acc

val vgg16_conv2_2_w : exp

val vgg16_conv2_2_b : exp

val vgg16_conv2_2_out : acc

val vgg16_relu2_2_out : acc

val vgg16_conv3_1_w : exp

val vgg16_conv3_1_b : exp

val vgg16_conv3_1_out : acc

val vgg16_relu3_1_out : acc

val vgg16_conv3_2_w : exp

val vgg16_conv3_2_b : exp

val vgg16_conv3_2_out : acc

val vgg16_relu3_2_out : acc

val vgg16_conv3_3_w : exp

val vgg16_conv3_3_b : exp

val vgg16_conv3_3_out : acc

val vgg16_relu3_3_out : acc

val vgg16_conv4_1_w : exp

val vgg16_conv4_1_b : exp

val vgg16_conv4_1_out : acc

val vgg16_relu4_1_out : acc

val vgg16_conv4_2_w : exp

val vgg16_conv4_2_b : exp

val vgg16_conv4_2_out : acc

val vgg16_relu4_2_out : acc

val vgg16_conv4_3_w : exp

val vgg16_conv4_3_b : exp

val vgg16_conv4_3_out : acc

val vgg16_relu4_3_out : acc

val vgg16_conv5_1_w : exp

val vgg16_conv5_1_b : exp

val vgg16_conv5_1_out : acc

val vgg16_relu5_1_out : acc

val vgg16_conv5_2_w : exp

val vgg16_conv5_2_b : exp

val vgg16_conv5_2_out : acc

val vgg16_relu5_2_out : acc

val vgg16_conv5_3_w : exp

val vgg16_conv5_3_b : exp

val vgg16_conv5_3_out : acc

val vgg16_relu5_3_out : acc

val vgg16_pool1_out : acc

val vgg16_pool2_out : acc

val vgg16_pool3_out : acc

val vgg16_pool4_out : acc

val vgg16_pool5_out : acc

val vgg16_flatten_out : acc

val vgg16_fc1_w : exp

val vgg16_fc1_b : exp

val vgg16_fc1_out : acc

val vgg16_fc1_relu_out : acc

val vgg16_fc2_w : exp

val vgg16_fc2_b : exp

val vgg16_fc2_out : acc

val vgg16_fc2_relu_out : acc

val vgg16_fc3_w : exp

val vgg16_fc3_b : exp

val vgg16_output : acc

val vgg16_comm : comm

val conv4d_p1_k3_par_comm :
  nat -> nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm

val reLU4d_par_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm

val maxPool4d_k2_par_comm : nat -> nat -> nat -> exp -> acc -> comm

val linear2d_par_comm : nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm

val reLU2d_par_comm : nat -> nat -> exp -> acc -> comm

val vgg16_par_comm : comm
