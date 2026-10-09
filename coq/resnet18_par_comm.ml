
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val fst : ('a1, 'a2) prod -> 'a1 **)

let fst = function
| Pair (x, _) -> x

(** val snd : ('a1, 'a2) prod -> 'a2 **)

let snd = function
| Pair (_, y) -> y

type comparison =
| Eq
| Lt
| Gt

(** val compOpp : comparison -> comparison **)

let compOpp = function
| Eq -> Eq
| Lt -> Gt
| Gt -> Lt

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type sumbool =
| Left
| Right

type 'a sumor =
| Inleft of 'a
| Inright

(** val pred : nat -> nat **)

let pred n = match n with
| O -> n
| S u -> u

module Coq__1 = struct
 (** val add : nat -> nat -> nat **)

 let rec add n m =
   match n with
   | O -> m
   | S p -> S (add p m)
end
include Coq__1

(** val mul : nat -> nat -> nat **)

let rec mul n m =
  match n with
  | O -> O
  | S p -> add m (mul p m)

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

(** val iff_reflect : bool -> reflect **)

let iff_reflect = function
| True -> ReflectT
| False -> ReflectF

module Nat =
 struct
  (** val add : nat -> nat -> nat **)

  let rec add n m =
    match n with
    | O -> m
    | S p -> S (add p m)

  (** val mul : nat -> nat -> nat **)

  let rec mul n m =
    match n with
    | O -> O
    | S p -> add m (mul p m)

  (** val sub : nat -> nat -> nat **)

  let rec sub n m =
    match n with
    | O -> n
    | S k -> (match m with
              | O -> n
              | S l -> sub k l)

  (** val eqb : nat -> nat -> bool **)

  let rec eqb n m =
    match n with
    | O -> (match m with
            | O -> True
            | S _ -> False)
    | S n' -> (match m with
               | O -> False
               | S m' -> eqb n' m')

  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')

  (** val ltb : nat -> nat -> bool **)

  let ltb n m =
    leb (S n) m

  (** val pow : nat -> nat -> nat **)

  let rec pow n = function
  | O -> S O
  | S m0 -> mul n (pow n m0)

  (** val divmod : nat -> nat -> nat -> nat -> (nat, nat) prod **)

  let rec divmod x y q0 u =
    match x with
    | O -> Pair (q0, u)
    | S x' ->
      (match u with
       | O -> divmod x' y (S q0) y
       | S u' -> divmod x' y q0 u')

  (** val div : nat -> nat -> nat **)

  let div x y = match y with
  | O -> y
  | S y' -> fst (divmod x y' O y')

  (** val modulo : nat -> nat -> nat **)

  let modulo x = function
  | O -> x
  | S y' -> sub y' (snd (divmod x y' O y'))

  (** val ltb_spec0 : nat -> nat -> reflect **)

  let ltb_spec0 x y =
    iff_reflect (ltb x y)
 end

type positive =
| XI of positive
| XO of positive
| XH

type z =
| Z0
| Zpos of positive
| Zneg of positive

module Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val of_succ_nat : nat -> positive **)

  let rec of_succ_nat = function
  | O -> XH
  | S x -> succ (of_succ_nat x)
 end

module Coq_Pos =
 struct
  (** val succ : positive -> positive **)

  let rec succ = function
  | XI p -> XO (succ p)
  | XO p -> XI p
  | XH -> XO XH

  (** val add : positive -> positive -> positive **)

  let rec add x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XI (add p q0)
       | XO q0 -> XO (add p q0)
       | XH -> XI p)
    | XH -> (match y with
             | XI q0 -> XO (succ q0)
             | XO q0 -> XI q0
             | XH -> XO XH)

  (** val add_carry : positive -> positive -> positive **)

  and add_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> XI (add_carry p q0)
       | XO q0 -> XO (add_carry p q0)
       | XH -> XI (succ p))
    | XO p ->
      (match y with
       | XI q0 -> XO (add_carry p q0)
       | XO q0 -> XI (add p q0)
       | XH -> XO (succ p))
    | XH ->
      (match y with
       | XI q0 -> XI (succ q0)
       | XO q0 -> XO (succ q0)
       | XH -> XI XH)

  (** val pred_double : positive -> positive **)

  let rec pred_double = function
  | XI p -> XI (XO p)
  | XO p -> XI (pred_double p)
  | XH -> XH

  type mask = Pos.mask =
  | IsNul
  | IsPos of positive
  | IsNeg

  (** val succ_double_mask : mask -> mask **)

  let succ_double_mask = function
  | IsNul -> IsPos XH
  | IsPos p -> IsPos (XI p)
  | IsNeg -> IsNeg

  (** val double_mask : mask -> mask **)

  let double_mask = function
  | IsPos p -> IsPos (XO p)
  | x0 -> x0

  (** val double_pred_mask : positive -> mask **)

  let double_pred_mask = function
  | XI p -> IsPos (XO (XO p))
  | XO p -> IsPos (XO (pred_double p))
  | XH -> IsNul

  (** val sub_mask : positive -> positive -> mask **)

  let rec sub_mask x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double_mask (sub_mask p q0)
       | XO q0 -> succ_double_mask (sub_mask p q0)
       | XH -> IsPos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XH -> (match y with
             | XH -> IsNul
             | _ -> IsNeg)

  (** val sub_mask_carry : positive -> positive -> mask **)

  and sub_mask_carry x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> succ_double_mask (sub_mask_carry p q0)
       | XO q0 -> double_mask (sub_mask p q0)
       | XH -> IsPos (pred_double p))
    | XO p ->
      (match y with
       | XI q0 -> double_mask (sub_mask_carry p q0)
       | XO q0 -> succ_double_mask (sub_mask_carry p q0)
       | XH -> double_pred_mask p)
    | XH -> IsNeg

  (** val sub : positive -> positive -> positive **)

  let sub x y =
    match sub_mask x y with
    | IsPos z0 -> z0
    | _ -> XH

  (** val mul : positive -> positive -> positive **)

  let rec mul x y =
    match x with
    | XI p -> add y (XO (mul p y))
    | XO p -> XO (mul p y)
    | XH -> y

  (** val compare_cont : comparison -> positive -> positive -> comparison **)

  let rec compare_cont r x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> compare_cont r p q0
       | XO q0 -> compare_cont Gt p q0
       | XH -> Gt)
    | XO p ->
      (match y with
       | XI q0 -> compare_cont Lt p q0
       | XO q0 -> compare_cont r p q0
       | XH -> Gt)
    | XH -> (match y with
             | XH -> r
             | _ -> Lt)

  (** val compare : positive -> positive -> comparison **)

  let compare =
    compare_cont Eq

  (** val iter_op : ('a1 -> 'a1 -> 'a1) -> positive -> 'a1 -> 'a1 **)

  let rec iter_op op p a =
    match p with
    | XI p0 -> op a (iter_op op p0 (op a a))
    | XO p0 -> iter_op op p0 (op a a)
    | XH -> a

  (** val to_nat : positive -> nat **)

  let to_nat x =
    iter_op Coq__1.add x (S O)

  (** val size_nat : positive -> nat **)

  let rec size_nat = function
  | XI p0 -> S (size_nat p0)
  | XO p0 -> S (size_nat p0)
  | XH -> S O

  (** val ggcdn :
      nat -> positive -> positive -> (positive, (positive, positive) prod)
      prod **)

  let rec ggcdn n a b =
    match n with
    | O -> Pair (XH, (Pair (a, b)))
    | S n0 ->
      (match a with
       | XI a' ->
         (match b with
          | XI b' ->
            (match compare a' b' with
             | Eq -> Pair (a, (Pair (XH, XH)))
             | Lt ->
               let Pair (g, p) = ggcdn n0 (sub b' a') a in
               let Pair (ba, aa) = p in
               Pair (g, (Pair (aa, (add aa (XO ba)))))
             | Gt ->
               let Pair (g, p) = ggcdn n0 (sub a' b') b in
               let Pair (ab, bb) = p in
               Pair (g, (Pair ((add bb (XO ab)), bb))))
          | XO b0 ->
            let Pair (g, p) = ggcdn n0 a b0 in
            let Pair (aa, bb) = p in Pair (g, (Pair (aa, (XO bb))))
          | XH -> Pair (XH, (Pair (a, XH))))
       | XO a0 ->
         (match b with
          | XI _ ->
            let Pair (g, p) = ggcdn n0 a0 b in
            let Pair (aa, bb) = p in Pair (g, (Pair ((XO aa), bb)))
          | XO b0 -> let Pair (g, p) = ggcdn n0 a0 b0 in Pair ((XO g), p)
          | XH -> Pair (XH, (Pair (a, XH))))
       | XH -> Pair (XH, (Pair (XH, b))))

  (** val ggcd :
      positive -> positive -> (positive, (positive, positive) prod) prod **)

  let ggcd a b =
    ggcdn (Coq__1.add (size_nat a) (size_nat b)) a b

  (** val of_nat : nat -> positive **)

  let rec of_nat = function
  | O -> XH
  | S x -> (match x with
            | O -> XH
            | S _ -> succ (of_nat x))
 end

module Z =
 struct
  (** val double : z -> z **)

  let double = function
  | Z0 -> Z0
  | Zpos p -> Zpos (XO p)
  | Zneg p -> Zneg (XO p)

  (** val succ_double : z -> z **)

  let succ_double = function
  | Z0 -> Zpos XH
  | Zpos p -> Zpos (XI p)
  | Zneg p -> Zneg (Pos.pred_double p)

  (** val pred_double : z -> z **)

  let pred_double = function
  | Z0 -> Zneg XH
  | Zpos p -> Zpos (Pos.pred_double p)
  | Zneg p -> Zneg (XI p)

  (** val pos_sub : positive -> positive -> z **)

  let rec pos_sub x y =
    match x with
    | XI p ->
      (match y with
       | XI q0 -> double (pos_sub p q0)
       | XO q0 -> succ_double (pos_sub p q0)
       | XH -> Zpos (XO p))
    | XO p ->
      (match y with
       | XI q0 -> pred_double (pos_sub p q0)
       | XO q0 -> double (pos_sub p q0)
       | XH -> Zpos (Pos.pred_double p))
    | XH ->
      (match y with
       | XI q0 -> Zneg (XO q0)
       | XO q0 -> Zneg (Pos.pred_double q0)
       | XH -> Z0)

  (** val add : z -> z -> z **)

  let add x y =
    match x with
    | Z0 -> y
    | Zpos x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> Zpos (Pos.add x' y')
       | Zneg y' -> pos_sub x' y')
    | Zneg x' ->
      (match y with
       | Z0 -> x
       | Zpos y' -> pos_sub y' x'
       | Zneg y' -> Zneg (Pos.add x' y'))

  (** val opp : z -> z **)

  let opp = function
  | Z0 -> Z0
  | Zpos x0 -> Zneg x0
  | Zneg x0 -> Zpos x0

  (** val sub : z -> z -> z **)

  let sub m n =
    add m (opp n)

  (** val mul : z -> z -> z **)

  let mul x y =
    match x with
    | Z0 -> Z0
    | Zpos x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zpos (Pos.mul x' y')
       | Zneg y' -> Zneg (Pos.mul x' y'))
    | Zneg x' ->
      (match y with
       | Z0 -> Z0
       | Zpos y' -> Zneg (Pos.mul x' y')
       | Zneg y' -> Zpos (Pos.mul x' y'))

  (** val compare : z -> z -> comparison **)

  let compare x y =
    match x with
    | Z0 -> (match y with
             | Z0 -> Eq
             | Zpos _ -> Lt
             | Zneg _ -> Gt)
    | Zpos x' -> (match y with
                  | Zpos y' -> Pos.compare x' y'
                  | _ -> Gt)
    | Zneg x' ->
      (match y with
       | Zneg y' -> compOpp (Pos.compare x' y')
       | _ -> Lt)

  (** val max : z -> z -> z **)

  let max n m =
    match compare n m with
    | Lt -> m
    | _ -> n

  (** val to_nat : z -> nat **)

  let to_nat = function
  | Zpos p -> Pos.to_nat p
  | _ -> O

  (** val of_nat : nat -> z **)

  let of_nat = function
  | O -> Z0
  | S n0 -> Zpos (Pos.of_succ_nat n0)

  (** val to_pos : z -> positive **)

  let to_pos = function
  | Zpos p -> p
  | _ -> XH

  (** val sgn : z -> z **)

  let sgn = function
  | Z0 -> Z0
  | Zpos _ -> Zpos XH
  | Zneg _ -> Zneg XH

  (** val abs : z -> z **)

  let abs = function
  | Zneg p -> Zpos p
  | x -> x

  (** val ggcd : z -> z -> (z, (z, z) prod) prod **)

  let ggcd a b =
    match a with
    | Z0 -> Pair ((abs b), (Pair (Z0, (sgn b))))
    | Zpos a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zpos aa), (Zneg bb)))))
    | Zneg a0 ->
      (match b with
       | Z0 -> Pair ((abs a), (Pair ((sgn a), Z0)))
       | Zpos b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zpos bb))))
       | Zneg b0 ->
         let Pair (g, p) = Coq_Pos.ggcd a0 b0 in
         let Pair (aa, bb) = p in
         Pair ((Zpos g), (Pair ((Zneg aa), (Zneg bb)))))
 end

(** val pow_pos : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos rmul x = function
| XI i0 -> let p = pow_pos rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos rmul x i0 in rmul p p
| XH -> x

(** val z_lt_dec : z -> z -> sumbool **)

let z_lt_dec x y =
  match Z.compare x y with
  | Lt -> Left
  | _ -> Right

(** val z_lt_ge_dec : z -> z -> sumbool **)

let z_lt_ge_dec =
  z_lt_dec

(** val z_lt_le_dec : z -> z -> sumbool **)

let z_lt_le_dec =
  z_lt_ge_dec

type q = { qnum : z; qden : positive }

(** val qplus : q -> q -> q **)

let qplus x y =
  { qnum = (Z.add (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden)));
    qden = (Coq_Pos.mul x.qden y.qden) }

(** val qmult : q -> q -> q **)

let qmult x y =
  { qnum = (Z.mul x.qnum y.qnum); qden = (Coq_Pos.mul x.qden y.qden) }

(** val qopp : q -> q **)

let qopp x =
  { qnum = (Z.opp x.qnum); qden = x.qden }

(** val qminus : q -> q -> q **)

let qminus x y =
  qplus x (qopp y)

(** val qinv : q -> q **)

let qinv x =
  match x.qnum with
  | Z0 -> { qnum = Z0; qden = XH }
  | Zpos p -> { qnum = (Zpos x.qden); qden = p }
  | Zneg p -> { qnum = (Zneg x.qden); qden = p }

(** val qlt_le_dec : q -> q -> sumbool **)

let qlt_le_dec x y =
  z_lt_le_dec (Z.mul x.qnum (Zpos y.qden)) (Z.mul y.qnum (Zpos x.qden))

(** val qarchimedean : q -> positive **)

let qarchimedean q0 =
  let { qnum = qnum0; qden = _ } = q0 in
  (match qnum0 with
   | Zpos p -> Coq_Pos.add p XH
   | _ -> XH)

(** val qpower_positive : q -> positive -> q **)

let qpower_positive =
  pow_pos qmult

(** val qpower : q -> z -> q **)

let qpower q0 = function
| Z0 -> { qnum = (Zpos XH); qden = XH }
| Zpos p -> qpower_positive q0 p
| Zneg p -> qinv (qpower_positive q0 p)

(** val qred : q -> q **)

let qred q0 =
  let { qnum = q1; qden = q2 } = q0 in
  let Pair (r1, r2) = snd (Z.ggcd q1 (Zpos q2)) in
  { qnum = r1; qden = (Z.to_pos r2) }

(** val qabs : q -> q **)

let qabs x =
  let { qnum = n; qden = d } = x in { qnum = (Z.abs n); qden = d }

(** val pos_log2floor_plus1 : positive -> positive **)

let rec pos_log2floor_plus1 = function
| XI p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XO p' -> Coq_Pos.succ (pos_log2floor_plus1 p')
| XH -> XH

(** val qbound_lt_ZExp2 : q -> z **)

let qbound_lt_ZExp2 q0 =
  match q0.qnum with
  | Z0 -> Zneg (XO (XO (XO (XI (XO (XI (XI (XI (XI XH)))))))))
  | Zpos p ->
    Z.pos_sub (Coq_Pos.succ (pos_log2floor_plus1 p))
      (pos_log2floor_plus1 q0.qden)
  | Zneg _ -> Z0

(** val qbound_ltabs_ZExp2 : q -> z **)

let qbound_ltabs_ZExp2 q0 =
  qbound_lt_ZExp2 (qabs q0)

type cReal = { seq : (z -> q); scale : z }

(** val inject_Q : q -> cReal **)

let inject_Q q0 =
  { seq = (fun _ -> q0); scale = (qbound_ltabs_ZExp2 q0) }

(** val cReal_plus_seq : cReal -> cReal -> z -> q **)

let cReal_plus_seq x y n =
  qred (qplus (x.seq (Z.sub n (Zpos XH))) (y.seq (Z.sub n (Zpos XH))))

(** val cReal_plus_scale : cReal -> cReal -> z **)

let cReal_plus_scale x y =
  Z.add (Z.max x.scale y.scale) (Zpos XH)

(** val cReal_plus : cReal -> cReal -> cReal **)

let cReal_plus x y =
  { seq = (cReal_plus_seq x y); scale = (cReal_plus_scale x y) }

(** val cReal_opp_seq : cReal -> z -> q **)

let cReal_opp_seq x n =
  qopp (x.seq n)

(** val cReal_opp_scale : cReal -> z **)

let cReal_opp_scale x =
  x.scale

(** val cReal_opp : cReal -> cReal **)

let cReal_opp x =
  { seq = (cReal_opp_seq x); scale = (cReal_opp_scale x) }

(** val cReal_mult_seq : cReal -> cReal -> z -> q **)

let cReal_mult_seq x y n =
  qmult (x.seq (Z.sub (Z.sub n y.scale) (Zpos XH)))
    (y.seq (Z.sub (Z.sub n x.scale) (Zpos XH)))

(** val cReal_mult_scale : cReal -> cReal -> z **)

let cReal_mult_scale x y =
  Z.add x.scale y.scale

(** val cReal_mult : cReal -> cReal -> cReal **)

let cReal_mult x y =
  { seq = (cReal_mult_seq x y); scale = (cReal_mult_scale x y) }

(** val sig_forall_dec : (nat -> sumbool) -> nat sumor **)

let sig_forall_dec =
  failwith "AXIOM TO BE REALIZED (Stdlib.Reals.ClassicalDedekindReals.sig_forall_dec)"

(** val lowerCutBelow : (q -> bool) -> q **)

let lowerCutBelow f =
  let s =
    sig_forall_dec (fun n ->
      let b = f (qopp { qnum = (Z.of_nat n); qden = XH }) in
      (match b with
       | True -> Right
       | False -> Left))
  in
  (match s with
   | Inleft s0 -> qopp { qnum = (Z.of_nat s0); qden = XH }
   | Inright -> assert false (* absurd case *))

(** val lowerCutAbove : (q -> bool) -> q **)

let lowerCutAbove f =
  let s =
    sig_forall_dec (fun n ->
      let b = f { qnum = (Z.of_nat n); qden = XH } in
      (match b with
       | True -> Left
       | False -> Right))
  in
  (match s with
   | Inleft s0 -> { qnum = (Z.of_nat s0); qden = XH }
   | Inright -> assert false (* absurd case *))

type dReal = (q -> bool)

(** val dRealQlim_rec : (q -> bool) -> nat -> nat -> q **)

let rec dRealQlim_rec f n = function
| O -> assert false (* absurd case *)
| S n0 ->
  let b =
    f
      (qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
        (Coq_Pos.of_nat (S n)) })
  in
  (match b with
   | True ->
     qplus (lowerCutBelow f) { qnum = (Z.of_nat n0); qden =
       (Coq_Pos.of_nat (S n)) }
   | False -> dRealQlim_rec f n n0)

(** val dRealAbstr : cReal -> dReal **)

let dRealAbstr x =
  let h = fun q0 n ->
    let s =
      qlt_le_dec
        (qplus q0
          (qpower { qnum = (Zpos (XO XH)); qden = XH } (Z.opp (Z.of_nat n))))
        (x.seq (Z.opp (Z.of_nat n)))
    in
    (match s with
     | Left -> Right
     | Right -> Left)
  in
  (fun q0 ->
  match sig_forall_dec (h q0) with
  | Inleft _ -> True
  | Inright -> False)

(** val dRealQlim : dReal -> nat -> q **)

let dRealQlim x n =
  let s = lowerCutAbove x in
  let s0 = qarchimedean (qminus s (lowerCutBelow x)) in
  dRealQlim_rec x n (mul (S n) (Coq_Pos.to_nat s0))

(** val dRealQlimExp2 : dReal -> nat -> q **)

let dRealQlimExp2 x n =
  dRealQlim x (pred (Nat.pow (S (S O)) n))

(** val cReal_of_DReal_seq : dReal -> z -> q **)

let cReal_of_DReal_seq x n =
  dRealQlimExp2 x (Z.to_nat (Z.opp n))

(** val cReal_of_DReal_scale : dReal -> z **)

let cReal_of_DReal_scale x =
  qbound_lt_ZExp2
    (qplus (qabs (cReal_of_DReal_seq x (Zneg XH))) { qnum = (Zpos (XO XH));
      qden = XH })

(** val dRealRepr : dReal -> cReal **)

let dRealRepr x =
  { seq = (cReal_of_DReal_seq x); scale = (cReal_of_DReal_scale x) }

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

module RbaseSymbolsImpl =
 struct
  type coq_R = dReal

  (** val coq_Rabst : cReal -> dReal **)

  let coq_Rabst =
    dRealAbstr

  (** val coq_Rrepr : dReal -> cReal **)

  let coq_Rrepr =
    dRealRepr

  (** val coq_Rquot1 : __ **)

  let coq_Rquot1 =
    __

  (** val coq_Rquot2 : __ **)

  let coq_Rquot2 =
    __

  (** val coq_R0 : coq_R **)

  let coq_R0 =
    coq_Rabst (inject_Q { qnum = Z0; qden = XH })

  (** val coq_R1 : coq_R **)

  let coq_R1 =
    coq_Rabst (inject_Q { qnum = (Zpos XH); qden = XH })

  (** val coq_Rplus : coq_R -> coq_R -> coq_R **)

  let coq_Rplus x y =
    coq_Rabst (cReal_plus (coq_Rrepr x) (coq_Rrepr y))

  (** val coq_Rmult : coq_R -> coq_R -> coq_R **)

  let coq_Rmult x y =
    coq_Rabst (cReal_mult (coq_Rrepr x) (coq_Rrepr y))

  (** val coq_Ropp : coq_R -> coq_R **)

  let coq_Ropp x =
    coq_Rabst (cReal_opp (coq_Rrepr x))

  type coq_Rlt = __

  (** val coq_R0_def : __ **)

  let coq_R0_def =
    __

  (** val coq_R1_def : __ **)

  let coq_R1_def =
    __

  (** val coq_Rplus_def : __ **)

  let coq_Rplus_def =
    __

  (** val coq_Rmult_def : __ **)

  let coq_Rmult_def =
    __

  (** val coq_Ropp_def : __ **)

  let coq_Ropp_def =
    __

  (** val coq_Rlt_def : __ **)

  let coq_Rlt_def =
    __
 end

type ascii =
| Ascii of bool * bool * bool * bool * bool * bool * bool * bool

(** val eqb0 : ascii -> ascii -> bool **)

let eqb0 a b =
  let Ascii (a0, a1, a2, a3, a4, a5, a6, a7) = a in
  let Ascii (b0, b1, b2, b3, b4, b5, b6, b7) = b in
  (match match match match match match match eqb a0 b0 with
                                       | True -> eqb a1 b1
                                       | False -> False with
                                 | True -> eqb a2 b2
                                 | False -> False with
                           | True -> eqb a3 b3
                           | False -> False with
                     | True -> eqb a4 b4
                     | False -> False with
               | True -> eqb a5 b5
               | False -> False with
         | True -> eqb a6 b6
         | False -> False with
   | True -> eqb a7 b7
   | False -> False)

type string =
| EmptyString
| String of ascii * string

(** val eqb1 : string -> string -> bool **)

let rec eqb1 s1 s2 =
  match s1 with
  | EmptyString ->
    (match s2 with
     | EmptyString -> True
     | String (_, _) -> False)
  | String (c1, s1') ->
    (match s2 with
     | EmptyString -> False
     | String (c2, s2') ->
       (match eqb0 c1 c2 with
        | True -> eqb1 s1' s2'
        | False -> False))

(** val append : string -> string -> string **)

let rec append s1 s2 =
  match s1 with
  | EmptyString -> s2
  | String (c, s1') -> String (c, (append s1' s2))

type fin = nat

(** val fin2nat : nat -> fin -> nat **)

let fin2nat _ i =
  i

(** val fin2finS : nat -> fin -> fin **)

let fin2finS =
  fin2nat

(** val nat2fin : nat -> nat -> fin **)

let nat2fin _ i =
  i

type fle = nat

(** val fle2nat : nat -> fle -> nat **)

let fle2nat _ i =
  i

(** val fle_self : nat -> fle **)

let fle_self n =
  n

(** val natToDigit : nat -> ascii **)

let natToDigit = function
| O -> Ascii (False, False, False, False, True, True, False, False)
| S n0 ->
  (match n0 with
   | O -> Ascii (True, False, False, False, True, True, False, False)
   | S n1 ->
     (match n1 with
      | O -> Ascii (False, True, False, False, True, True, False, False)
      | S n2 ->
        (match n2 with
         | O -> Ascii (True, True, False, False, True, True, False, False)
         | S n3 ->
           (match n3 with
            | O -> Ascii (False, False, True, False, True, True, False, False)
            | S n4 ->
              (match n4 with
               | O ->
                 Ascii (True, False, True, False, True, True, False, False)
               | S n5 ->
                 (match n5 with
                  | O ->
                    Ascii (False, True, True, False, True, True, False, False)
                  | S n6 ->
                    (match n6 with
                     | O ->
                       Ascii (True, True, True, False, True, True, False,
                         False)
                     | S n7 ->
                       (match n7 with
                        | O ->
                          Ascii (False, False, False, True, True, True,
                            False, False)
                        | S n8 ->
                          (match n8 with
                           | O ->
                             Ascii (True, False, False, True, True, True,
                               False, False)
                           | S _ ->
                             Ascii (False, False, False, False, True, True,
                               False, False))))))))))

(** val writeNatAux : nat -> nat -> string -> string **)

let rec writeNatAux time n acc0 =
  let acc' = String
    ((natToDigit (Nat.modulo n (S (S (S (S (S (S (S (S (S (S O)))))))))))),
    acc0)
  in
  (match time with
   | O -> acc'
   | S time' ->
     (match Nat.div n (S (S (S (S (S (S (S (S (S (S O)))))))))) with
      | O -> acc'
      | S n0 -> writeNatAux time' (S n0) acc'))

(** val writeNat : nat -> string **)

let writeNat n =
  writeNatAux n n EmptyString

type 'a vector = __

(** val mk_vec : nat -> (fin -> 'a1) -> 'a1 vector **)

let rec mk_vec m x =
  match m with
  | O -> Obj.magic Tt
  | S m' ->
    Obj.magic (Pair ((mk_vec m' (fun i -> x (fin2finS m' i))), (x m')))

(** val v_nth : nat -> 'a1 -> 'a1 vector -> nat -> 'a1 **)

let rec v_nth n x0 x x1 =
  match n with
  | O -> x0
  | S n' ->
    (match Nat.eqb x1 n' with
     | True -> snd (Obj.magic x)
     | False -> v_nth n' x0 (fst (Obj.magic x)) x1)

(** val v_idx : nat -> 'a1 -> 'a1 vector -> fin -> 'a1 **)

let v_idx n x0 v i =
  v_nth n x0 v (fin2nat n i)

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

(** val mkvSeq : data -> nat -> (fin -> exp) -> exp **)

let mkvSeq _ =
  mk_vec

(** val exp_default : data -> exp **)

let rec exp_default = function
| Num ->
  Obj.magic (REconst (RbaseSymbolsImpl.coq_R0, (String ((Ascii (False, False,
    False, False, True, True, False, False)), EmptyString))))
| Ary (n0, n, d0) -> mkvSeq d0 (fle2nat n0 n) (fun _ -> exp_default d0)

(** val idx : nat -> data -> exp -> fin -> exp **)

let idx n t v i =
  v_idx (fle2nat n (fle_self n)) (exp_default t) v i

(** val zero : exp **)

let zero =
  Obj.magic (REconst (RbaseSymbolsImpl.coq_R0, (String ((Ascii (False, False,
    False, False, True, True, False, False)), EmptyString))))

(** val add0 : exp -> exp -> exp **)

let add0 x y =
  Obj.magic (REadd ((Obj.magic x), (Obj.magic y)))

(** val mul0 : exp -> exp -> exp **)

let mul0 x y =
  Obj.magic (REmul ((Obj.magic x), (Obj.magic y)))

(** val div0 : exp -> exp -> exp **)

let div0 x y =
  Obj.magic (REdiv ((Obj.magic x), (Obj.magic y)))

(** val div_n : exp -> nat -> exp **)

let div_n x n =
  Obj.magic (REdiv_n ((Obj.magic x), n))

(** val sub0 : exp -> exp -> exp **)

let sub0 x y =
  Obj.magic (REsub ((Obj.magic x), (Obj.magic y)))

(** val leExp : exp -> exp -> bexp **)

let leExp x y =
  BLe ((Obj.magic x), (Obj.magic y))

(** val gtExp : exp -> exp -> bexp **)

let gtExp x y =
  BGt ((Obj.magic x), (Obj.magic y))

(** val sqrt : exp -> exp **)

let sqrt x =
  Obj.magic (REsqrt (Obj.magic x))

(** val safe_idx_nat : nat -> data -> exp -> nat -> exp **)

let safe_idx_nat n t e i =
  match Nat.ltb_spec0 i n with
  | ReflectT -> idx n t e (nat2fin n i)
  | ReflectF -> exp_default t

(** val vrd : data -> string -> exp **)

let rec vrd d s =
  match d with
  | Num ->
    (match eqb1 s (String ((Ascii (False, False, False, False, True, True,
             False, False)), EmptyString)) with
     | True ->
       Obj.magic (REconst (RbaseSymbolsImpl.coq_R0, (String ((Ascii (False,
         False, False, False, True, True, False, False)), EmptyString))))
     | False ->
       (match eqb1 s (String ((Ascii (True, False, False, False, True, True,
                False, False)), EmptyString)) with
        | True ->
          Obj.magic (REconst (RbaseSymbolsImpl.coq_R1, (String ((Ascii (True,
            False, False, False, True, True, False, False)), EmptyString))))
        | False -> Obj.magic (REvar s)))
  | Ary (n0, n, d') ->
    mk_vec (fle2nat n0 n) (fun i ->
      vrd d'
        (append s
          (append (String ((Ascii (True, True, False, True, True, False,
            True, False)), EmptyString))
            (append (writeNat (fin2nat (fle2nat n0 n) i)) (String ((Ascii
              (True, False, True, True, True, False, True, False)),
              EmptyString))))))

(** val vwt : data -> string -> acc **)

let rec vwt d s =
  match d with
  | Num -> Obj.magic (Var s)
  | Ary (n0, n, d') ->
    mk_vec (fle2nat n0 n) (fun i ->
      vwt d'
        (append s
          (append (String ((Ascii (True, True, False, True, True, False,
            True, False)), EmptyString))
            (append (writeNat (fin2nat (fle2nat n0 n) i)) (String ((Ascii
              (True, False, True, True, True, False, True, False)),
              EmptyString))))))

(** val mkvAcc : data -> nat -> (fin -> acc) -> acc **)

let mkvAcc _ =
  mk_vec

(** val acc_default : data -> acc **)

let rec acc_default = function
| Num ->
  vwt Num (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), EmptyString))))))))
| Ary (n0, n, d0) -> mkvAcc d0 (fle2nat n0 n) (fun _ -> acc_default d0)

(** val idxAcc : nat -> data -> acc -> fin -> acc **)

let idxAcc n t v i =
  v_idx (fle2nat n (fle_self n)) (acc_default t) v i

type comm =
| Skip
| If of bexp * (comm, comm) prod
| Seq of (comm, comm) prod
| Assign of data * (acc, exp) prod
| New of data * ((acc, exp) prod -> comm)
| Loopacc of data * (string -> comm)
| Seqfor of nat * (fin -> comm)
| Parfor of nat * data * acc * (fin -> acc -> comm)

(** val resnet18_input : exp **)

let resnet18_input =
  vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (True, False, False, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))

(** val resnet18_conv1_w : exp **)

let resnet18_conv1_w =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S
    (S (S O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num))))))))
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, True, False, True, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    EmptyString))))))))))))))

(** val resnet18_conv1_b : exp **)

let resnet18_conv1_b =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))

(** val resnet18_bn1_mean : exp **)

let resnet18_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))

(** val resnet18_bn1_var : exp **)

let resnet18_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))

(** val resnet18_bn1_gamma : exp **)

let resnet18_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))

(** val resnet18_bn1_beta : exp **)

let resnet18_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val resnet18_eps : exp **)

let resnet18_eps =
  vrd Num (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))))))

(** val resnet18_conv1_out : acc **)

let resnet18_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))

(** val resnet18_bn1_out : acc **)

let resnet18_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, True, False, False, False, True,
    True, False)), (String ((Ascii (False, True, True, True, False, True,
    True, False)), (String ((Ascii (True, False, False, False, True, True,
    False, False)), (String ((Ascii (True, True, True, True, True, False,
    True, False)), (String ((Ascii (True, True, True, True, False, True,
    True, False)), (String ((Ascii (True, False, True, False, True, True,
    True, False)), (String ((Ascii (False, False, True, False, True, True,
    True, False)), EmptyString))))))))))))))

(** val resnet18_relu1_out : acc **)

let resnet18_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))

(** val resnet18_pool_out : acc **)

let resnet18_pool_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, False, False, True, True,
    True, False)), (String ((Ascii (True, True, True, True, False, True,
    True, False)), (String ((Ascii (True, True, True, True, False, True,
    True, False)), (String ((Ascii (False, False, True, True, False, True,
    True, False)), (String ((Ascii (True, True, True, True, True, False,
    True, False)), (String ((Ascii (True, True, True, True, False, True,
    True, False)), (String ((Ascii (True, False, True, False, True, True,
    True, False)), (String ((Ascii (False, False, True, False, True, True,
    True, False)), EmptyString))))))))))))))))

(** val resnet18_l1_b1_w1 : exp **)

let resnet18_l1_b1_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l1_b1_b1 : exp **)

let resnet18_l1_b1_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l1_b1_w2 : exp **)

let resnet18_l1_b1_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l1_b1_b2 : exp **)

let resnet18_l1_b1_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l1_b1_bn1_mean : exp **)

let resnet18_l1_b1_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn1_var : exp **)

let resnet18_l1_b1_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn1_gamma : exp **)

let resnet18_l1_b1_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn1_beta : exp **)

let resnet18_l1_b1_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn2_mean : exp **)

let resnet18_l1_b1_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn2_var : exp **)

let resnet18_l1_b1_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn2_gamma : exp **)

let resnet18_l1_b1_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn2_beta : exp **)

let resnet18_l1_b1_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b1_conv1_out : acc **)

let resnet18_l1_b1_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn1_out : acc **)

let resnet18_l1_b1_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b1_relu1_out : acc **)

let resnet18_l1_b1_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b1_conv2_out : acc **)

let resnet18_l1_b1_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b1_bn2_out : acc **)

let resnet18_l1_b1_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b1_add_out : acc **)

let resnet18_l1_b1_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b2_w1 : exp **)

let resnet18_l1_b2_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l1_b2_b1 : exp **)

let resnet18_l1_b2_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l1_b2_w2 : exp **)

let resnet18_l1_b2_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l1_b2_b2 : exp **)

let resnet18_l1_b2_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l1_b2_bn1_mean : exp **)

let resnet18_l1_b2_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn1_var : exp **)

let resnet18_l1_b2_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn1_gamma : exp **)

let resnet18_l1_b2_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn1_beta : exp **)

let resnet18_l1_b2_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn2_mean : exp **)

let resnet18_l1_b2_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn2_var : exp **)

let resnet18_l1_b2_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn2_gamma : exp **)

let resnet18_l1_b2_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn2_beta : exp **)

let resnet18_l1_b2_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l1_b2_conv1_out : acc **)

let resnet18_l1_b2_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn1_out : acc **)

let resnet18_l1_b2_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b2_relu1_out : acc **)

let resnet18_l1_b2_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b2_conv2_out : acc **)

let resnet18_l1_b2_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l1_b2_bn2_out : acc **)

let resnet18_l1_b2_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l1_b2_add_out : acc **)

let resnet18_l1_b2_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b1_w1 : exp **)

let resnet18_l2_b1_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l2_b1_b1 : exp **)

let resnet18_l2_b1_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l2_b1_w2 : exp **)

let resnet18_l2_b1_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l2_b1_b2 : exp **)

let resnet18_l2_b1_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l2_b1_bn1_mean : exp **)

let resnet18_l2_b1_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn1_var : exp **)

let resnet18_l2_b1_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn1_gamma : exp **)

let resnet18_l2_b1_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn1_beta : exp **)

let resnet18_l2_b1_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn2_mean : exp **)

let resnet18_l2_b1_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn2_var : exp **)

let resnet18_l2_b1_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn2_gamma : exp **)

let resnet18_l2_b1_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn2_beta : exp **)

let resnet18_l2_b1_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_w : exp **)

let resnet18_l2_b1_shortcut_w =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S O), (fle_self (S O)), (Ary ((S O), (fle_self (S O)), Num))))))))
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (False, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_b : exp **)

let resnet18_l2_b1_shortcut_b =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_mean : exp **)

let resnet18_l2_b1_shortcut_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_var : exp **)

let resnet18_l2_b1_shortcut_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_gamma : exp **)

let resnet18_l2_b1_shortcut_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_beta : exp **)

let resnet18_l2_b1_shortcut_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_shortcut_out : acc **)

let resnet18_l2_b1_shortcut_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_conv1_out : acc **)

let resnet18_l2_b1_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn1_out : acc **)

let resnet18_l2_b1_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b1_relu1_out : acc **)

let resnet18_l2_b1_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_conv2_out : acc **)

let resnet18_l2_b1_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b1_bn2_out : acc **)

let resnet18_l2_b1_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b1_add_out : acc **)

let resnet18_l2_b1_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b2_w1 : exp **)

let resnet18_l2_b2_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l2_b2_b1 : exp **)

let resnet18_l2_b2_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l2_b2_w2 : exp **)

let resnet18_l2_b2_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l2_b2_b2 : exp **)

let resnet18_l2_b2_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l2_b2_bn1_mean : exp **)

let resnet18_l2_b2_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn1_var : exp **)

let resnet18_l2_b2_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn1_gamma : exp **)

let resnet18_l2_b2_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn1_beta : exp **)

let resnet18_l2_b2_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn2_mean : exp **)

let resnet18_l2_b2_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn2_var : exp **)

let resnet18_l2_b2_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn2_gamma : exp **)

let resnet18_l2_b2_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn2_beta : exp **)

let resnet18_l2_b2_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l2_b2_conv1_out : acc **)

let resnet18_l2_b2_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn1_out : acc **)

let resnet18_l2_b2_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b2_relu1_out : acc **)

let resnet18_l2_b2_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b2_conv2_out : acc **)

let resnet18_l2_b2_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l2_b2_bn2_out : acc **)

let resnet18_l2_b2_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l2_b2_add_out : acc **)

let resnet18_l2_b2_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b1_w1 : exp **)

let resnet18_l3_b1_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l3_b1_b1 : exp **)

let resnet18_l3_b1_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l3_b1_w2 : exp **)

let resnet18_l3_b1_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l3_b1_b2 : exp **)

let resnet18_l3_b1_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l3_b1_bn1_mean : exp **)

let resnet18_l3_b1_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn1_var : exp **)

let resnet18_l3_b1_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn1_gamma : exp **)

let resnet18_l3_b1_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn1_beta : exp **)

let resnet18_l3_b1_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn2_mean : exp **)

let resnet18_l3_b1_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn2_var : exp **)

let resnet18_l3_b1_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn2_gamma : exp **)

let resnet18_l3_b1_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn2_beta : exp **)

let resnet18_l3_b1_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_w : exp **)

let resnet18_l3_b1_shortcut_w =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S O), (fle_self (S O)), (Ary ((S O), (fle_self (S O)), Num))))))))
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (False, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_b : exp **)

let resnet18_l3_b1_shortcut_b =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_mean : exp **)

let resnet18_l3_b1_shortcut_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_var : exp **)

let resnet18_l3_b1_shortcut_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_gamma : exp **)

let resnet18_l3_b1_shortcut_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_beta : exp **)

let resnet18_l3_b1_shortcut_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_shortcut_out : acc **)

let resnet18_l3_b1_shortcut_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_conv1_out : acc **)

let resnet18_l3_b1_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn1_out : acc **)

let resnet18_l3_b1_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b1_relu1_out : acc **)

let resnet18_l3_b1_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_conv2_out : acc **)

let resnet18_l3_b1_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b1_bn2_out : acc **)

let resnet18_l3_b1_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b1_add_out : acc **)

let resnet18_l3_b1_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b2_w1 : exp **)

let resnet18_l3_b2_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l3_b2_b1 : exp **)

let resnet18_l3_b2_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l3_b2_w2 : exp **)

let resnet18_l3_b2_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (True, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l3_b2_b2 : exp **)

let resnet18_l3_b2_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l3_b2_bn1_mean : exp **)

let resnet18_l3_b2_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn1_var : exp **)

let resnet18_l3_b2_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn1_gamma : exp **)

let resnet18_l3_b2_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn1_beta : exp **)

let resnet18_l3_b2_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn2_mean : exp **)

let resnet18_l3_b2_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn2_var : exp **)

let resnet18_l3_b2_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn2_gamma : exp **)

let resnet18_l3_b2_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn2_beta : exp **)

let resnet18_l3_b2_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l3_b2_conv1_out : acc **)

let resnet18_l3_b2_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn1_out : acc **)

let resnet18_l3_b2_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b2_relu1_out : acc **)

let resnet18_l3_b2_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b2_conv2_out : acc **)

let resnet18_l3_b2_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l3_b2_bn2_out : acc **)

let resnet18_l3_b2_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l3_b2_add_out : acc **)

let resnet18_l3_b2_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
    Num)))))))) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b1_w1 : exp **)

let resnet18_l4_b1_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, False,
    True, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l4_b1_b1 : exp **)

let resnet18_l4_b1_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l4_b1_w2 : exp **)

let resnet18_l4_b1_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, False,
    True, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l4_b1_b2 : exp **)

let resnet18_l4_b1_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l4_b1_bn1_mean : exp **)

let resnet18_l4_b1_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn1_var : exp **)

let resnet18_l4_b1_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn1_gamma : exp **)

let resnet18_l4_b1_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn1_beta : exp **)

let resnet18_l4_b1_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn2_mean : exp **)

let resnet18_l4_b1_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn2_var : exp **)

let resnet18_l4_b1_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn2_gamma : exp **)

let resnet18_l4_b1_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn2_beta : exp **)

let resnet18_l4_b1_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_w : exp **)

let resnet18_l4_b1_shortcut_w =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S O), (fle_self (S O)), (Ary ((S O), (fle_self (S O)), Num))))))))
    (String ((Ascii (False, False, True, True, False, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (False, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, False, True, False, True, True, False)),
    (String ((Ascii (True, True, True, True, False, True, True, False)),
    (String ((Ascii (False, True, False, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, False, False, False, True, True, False)),
    (String ((Ascii (True, False, True, False, True, True, True, False)),
    (String ((Ascii (False, False, True, False, True, True, True, False)),
    (String ((Ascii (True, True, True, True, True, False, True, False)),
    (String ((Ascii (True, True, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_b : exp **)

let resnet18_l4_b1_shortcut_b =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_mean : exp **)

let resnet18_l4_b1_shortcut_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_var : exp **)

let resnet18_l4_b1_shortcut_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_gamma : exp **)

let resnet18_l4_b1_shortcut_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_beta : exp **)

let resnet18_l4_b1_shortcut_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_shortcut_out : acc **)

let resnet18_l4_b1_shortcut_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, False, False, True, True, True, False)), (String
    ((Ascii (False, False, False, True, False, True, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_conv1_out : acc **)

let resnet18_l4_b1_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn1_out : acc **)

let resnet18_l4_b1_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b1_relu1_out : acc **)

let resnet18_l4_b1_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)), (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_conv2_out : acc **)

let resnet18_l4_b1_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b1_bn2_out : acc **)

let resnet18_l4_b1_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b1_add_out : acc **)

let resnet18_l4_b1_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b2_w1 : exp **)

let resnet18_l4_b2_w1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, False,
    True, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l4_b2_b1 : exp **)

let resnet18_l4_b2_b1 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l4_b2_w2 : exp **)

let resnet18_l4_b2_w2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
    (fle_self (S (S (S O)))), Num)))))))) (String ((Ascii (False, False,
    True, True, False, True, True, False)), (String ((Ascii (False, False,
    True, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (False, True,
    False, False, False, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), (String ((Ascii (True, True,
    True, True, True, False, True, False)), (String ((Ascii (True, True,
    True, False, True, True, True, False)), (String ((Ascii (False, True,
    False, False, True, True, False, False)), EmptyString))))))))))))))))

(** val resnet18_l4_b2_b2 : exp **)

let resnet18_l4_b2_b2 =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))))))))

(** val resnet18_l4_b2_bn1_mean : exp **)

let resnet18_l4_b2_bn1_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn1_var : exp **)

let resnet18_l4_b2_bn1_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn1_gamma : exp **)

let resnet18_l4_b2_bn1_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn1_beta : exp **)

let resnet18_l4_b2_bn1_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn2_mean : exp **)

let resnet18_l4_b2_bn2_mean =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn2_var : exp **)

let resnet18_l4_b2_bn2_var =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn2_gamma : exp **)

let resnet18_l4_b2_bn2_gamma =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn2_beta : exp **)

let resnet18_l4_b2_bn2_beta =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))))))))))))))))))))))

(** val resnet18_l4_b2_conv1_out : acc **)

let resnet18_l4_b2_conv1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn1_out : acc **)

let resnet18_l4_b2_bn1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b2_relu1_out : acc **)

let resnet18_l4_b2_relu1_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, True, True, True, False)), (String
    ((Ascii (True, False, True, False, False, True, True, False)), (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (True, False, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b2_conv2_out : acc **)

let resnet18_l4_b2_conv2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, False, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, True, False, True, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))))))

(** val resnet18_l4_b2_bn2_out : acc **)

let resnet18_l4_b2_bn2_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, True, True, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))

(** val resnet18_l4_b2_add_out : acc **)

let resnet18_l4_b2_add_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S O))))))),
    (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
    O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))))) (String
    ((Ascii (False, False, True, True, False, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (False, True, False, False, False, True, True, False)), (String
    ((Ascii (False, True, False, False, True, True, False, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, False, False, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, False, True, True, False)), (String
    ((Ascii (False, False, True, False, False, True, True, False)), (String
    ((Ascii (True, True, True, True, True, False, True, False)), (String
    ((Ascii (True, True, True, True, False, True, True, False)), (String
    ((Ascii (True, False, True, False, True, True, True, False)), (String
    ((Ascii (False, False, True, False, True, True, True, False)),
    EmptyString))))))))))))))))))))))))))

(** val resnet18_avgpool_out : acc **)

let resnet18_avgpool_out =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))) (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))))))))))))

(** val resnet18_fc_w : exp **)

let resnet18_fc_w =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))) (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), EmptyString))))))))

(** val resnet18_fc_b : exp **)

let resnet18_fc_b =
  vrd (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)) (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))

(** val resnet18_output : acc **)

let resnet18_output =
  vwt (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S
    O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
    Num)))) (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))

(** val conv4d_p1_k3_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm **)

let conv4d_p1_k3_par_comm batch inch outch m input w bias output =
  New ((Ary (batch, (fle_self batch), (Ary (inch, (fle_self inch), (Ary
    ((add m (S (S O))), (fle_self (add m (S (S O)))), (Ary
    ((add m (S (S O))), (fle_self (add m (S (S O)))), Num)))))))),
    (fun pad_tmp ->
    let Pair (pad_a, pad_v) = pad_tmp in
    Seq (Pair ((Seqfor (batch, (fun b -> Parfor (inch, (Ary
    ((add m (S (S O))), (fle_self (add m (S (S O)))), (Ary
    ((add m (S (S O))), (fle_self (add m (S (S O)))), Num)))),
    (idxAcc batch (Ary (inch, (fle_self inch), (Ary ((add m (S (S O))),
      (fle_self (add m (S (S O)))), (Ary ((add m (S (S O))),
      (fle_self (add m (S (S O)))), Num)))))) pad_a b),
    (fun c po -> Seqfor ((add m (S (S O))), (fun i -> Seqfor
    ((add m (S (S O))), (fun j -> If ((BLt ((fin2nat (add m (S (S O))) i), (S
    O))), (Pair ((Assign (Num, (Pair
    ((idxAcc (add m (S (S O))) Num
       (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
         (fle_self (add m (S (S O)))), Num)) po i)
       j),
    zero)))), (If ((BLt ((fin2nat (add m (S (S O))) i), (S m))), (Pair ((If
    ((BLt ((fin2nat (add m (S (S O))) j), (S O))), (Pair ((Assign (Num, (Pair
    ((idxAcc (add m (S (S O))) Num
       (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
         (fle_self (add m (S (S O)))), Num)) po i)
       j),
    zero)))), (If ((BLt ((fin2nat (add m (S (S O))) j), (S m))), (Pair
    ((Assign (Num, (Pair
    ((idxAcc (add m (S (S O))) Num
       (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
         (fle_self (add m (S (S O)))), Num)) po i)
       j),
    (safe_idx_nat m Num
      (safe_idx_nat m (Ary (m, (fle_self m), Num))
        (idx inch (Ary (m, (fle_self m), (Ary (m, (fle_self m), Num))))
          (idx batch (Ary (inch, (fle_self inch), (Ary (m, (fle_self m), (Ary
            (m, (fle_self m), Num)))))) input b)
          c)
        (sub (fin2nat (add m (S (S O))) i) (S O)))
      (sub (fin2nat (add m (S (S O))) j) (S O))))))),
    (Assign (Num, (Pair
    ((idxAcc (add m (S (S O))) Num
       (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
         (fle_self (add m (S (S O)))), Num)) po i)
       j),
    zero)))))))))))), (Assign (Num, (Pair
    ((idxAcc (add m (S (S O))) Num
       (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
         (fle_self (add m (S (S O)))), Num)) po i)
       j),
    zero)))))))))))))))))))), (Seqfor (batch, (fun b -> Parfor (outch, (Ary
    (m, (fle_self m), (Ary (m, (fle_self m), Num)))),
    (idxAcc batch (Ary (outch, (fle_self outch), (Ary (m, (fle_self m), (Ary
      (m, (fle_self m), Num)))))) output b),
    (fun num o -> Seqfor (m, (fun i0 -> Seqfor (m, (fun j0 -> New (Num,
    (fun acc_tmp ->
    let Pair (acc_a, acc_v) = acc_tmp in
    Seq (Pair ((Assign (Num, (Pair (acc_a, zero)))), (Seq (Pair ((Seqfor
    (inch, (fun c -> Seqfor ((S (S (S O))), (fun i1 -> Seqfor ((S (S (S O))),
    (fun j1 -> Assign (Num, (Pair (acc_a,
    (add0
      (mul0
        (safe_idx_nat (add m (S (S O))) Num
          (safe_idx_nat (add m (S (S O))) (Ary ((add m (S (S O))),
            (fle_self (add m (S (S O)))), Num))
            (idx inch (Ary ((add m (S (S O))), (fle_self (add m (S (S O)))),
              (Ary ((add m (S (S O))), (fle_self (add m (S (S O)))), Num))))
              (idx batch (Ary (inch, (fle_self inch), (Ary
                ((add m (S (S O))), (fle_self (add m (S (S O)))), (Ary
                ((add m (S (S O))), (fle_self (add m (S (S O)))), Num))))))
                pad_v b)
              c)
            (add (fin2nat m i0) (fin2nat (S (S (S O))) i1)))
          (add (fin2nat m j0) (fin2nat (S (S (S O))) j1)))
        (idx (S (S (S O))) Num
          (idx (S (S (S O))) (Ary ((S (S (S O))), (fle_self (S (S (S O)))),
            Num))
            (idx inch (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S
              (S (S O))), (fle_self (S (S (S O)))), Num))))
              (idx outch (Ary (inch, (fle_self inch), (Ary ((S (S (S O))),
                (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
                (fle_self (S (S (S O)))), Num)))))) w num)
              c)
            i1)
          j1))
      acc_v))))))))))),
    (Assign (Num, (Pair
    ((idxAcc m Num (idxAcc m (Ary (m, (fle_self m), Num)) o i0) j0),
    (add0 acc_v (idx outch Num bias num))))))))))))))))))))))))))

(** val conv4d_p1_k3_s2_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm **)

let conv4d_p1_k3_s2_par_comm batch inch outch m input w bias output =
  let half =
    add (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
      (S O)
  in
  New ((Ary (batch, (fle_self batch), (Ary (inch, (fle_self inch), (Ary
  ((add m (S (S O))), (fle_self (add m (S (S O)))), (Ary ((add m (S (S O))),
  (fle_self (add m (S (S O)))), Num)))))))), (fun pad_tmp ->
  let Pair (pad_a, pad_v) = pad_tmp in
  Seq (Pair ((Seqfor (batch, (fun b -> Parfor (inch, (Ary ((add m (S (S O))),
  (fle_self (add m (S (S O)))), (Ary ((add m (S (S O))),
  (fle_self (add m (S (S O)))), Num)))),
  (idxAcc batch (Ary (inch, (fle_self inch), (Ary ((add m (S (S O))),
    (fle_self (add m (S (S O)))), (Ary ((add m (S (S O))),
    (fle_self (add m (S (S O)))), Num)))))) pad_a b),
  (fun c po -> Seqfor ((add m (S (S O))), (fun i -> Seqfor
  ((add m (S (S O))), (fun j -> If ((BLt ((fin2nat (add m (S (S O))) i), (S
  O))), (Pair ((Assign (Num, (Pair
  ((idxAcc (add m (S (S O))) Num
     (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
       (fle_self (add m (S (S O)))), Num)) po i)
     j),
  zero)))), (If ((BLt ((fin2nat (add m (S (S O))) i), (S m))), (Pair ((If
  ((BLt ((fin2nat (add m (S (S O))) j), (S O))), (Pair ((Assign (Num, (Pair
  ((idxAcc (add m (S (S O))) Num
     (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
       (fle_self (add m (S (S O)))), Num)) po i)
     j),
  zero)))), (If ((BLt ((fin2nat (add m (S (S O))) j), (S m))), (Pair ((Assign
  (Num, (Pair
  ((idxAcc (add m (S (S O))) Num
     (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
       (fle_self (add m (S (S O)))), Num)) po i)
     j),
  (safe_idx_nat m Num
    (safe_idx_nat m (Ary (m, (fle_self m), Num))
      (idx inch (Ary (m, (fle_self m), (Ary (m, (fle_self m), Num))))
        (idx batch (Ary (inch, (fle_self inch), (Ary (m, (fle_self m), (Ary
          (m, (fle_self m), Num)))))) input b)
        c)
      (sub (fin2nat (add m (S (S O))) i) (S O)))
    (sub (fin2nat (add m (S (S O))) j) (S O))))))),
  (Assign (Num, (Pair
  ((idxAcc (add m (S (S O))) Num
     (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
       (fle_self (add m (S (S O)))), Num)) po i)
     j),
  zero)))))))))))), (Assign (Num, (Pair
  ((idxAcc (add m (S (S O))) Num
     (idxAcc (add m (S (S O))) (Ary ((add m (S (S O))),
       (fle_self (add m (S (S O)))), Num)) po i)
     j),
  zero)))))))))))))))))))), (Seqfor (batch, (fun b -> Parfor (outch, (Ary
  ((add (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
     (S O)),
  (fle_self
    (add
      (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
      (S O))),
  (Ary
  ((add (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
     (S O)),
  (fle_self
    (add
      (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
      (S O))),
  Num)))),
  (idxAcc batch (Ary (outch, (fle_self outch), (Ary
    ((add
       (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
       (S O)),
    (fle_self
      (add
        (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
        (S O))),
    (Ary
    ((add
       (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
       (S O)),
    (fle_self
      (add
        (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
        (S O))),
    Num)))))) output b),
  (fun num o -> Seqfor (half, (fun i0 -> Seqfor (half, (fun j0 -> New (Num,
  (fun acc_tmp ->
  let Pair (acc_a, acc_v) = acc_tmp in
  Seq (Pair ((Assign (Num, (Pair (acc_a, zero)))), (Seq (Pair ((Seqfor (inch,
  (fun c -> Seqfor ((S (S (S O))), (fun i1 -> Seqfor ((S (S (S O))),
  (fun j1 ->
  let ii = add (mul (S (S O)) (fin2nat half i0)) (fin2nat (S (S (S O))) i1) in
  let jj = add (mul (S (S O)) (fin2nat half j0)) (fin2nat (S (S (S O))) j1) in
  Assign (Num, (Pair (acc_a,
  (add0
    (mul0
      (safe_idx_nat (add m (S (S O))) Num
        (safe_idx_nat (add m (S (S O))) (Ary ((add m (S (S O))),
          (fle_self (add m (S (S O)))), Num))
          (idx inch (Ary ((add m (S (S O))), (fle_self (add m (S (S O)))),
            (Ary ((add m (S (S O))), (fle_self (add m (S (S O)))), Num))))
            (idx batch (Ary (inch, (fle_self inch), (Ary ((add m (S (S O))),
              (fle_self (add m (S (S O)))), (Ary ((add m (S (S O))),
              (fle_self (add m (S (S O)))), Num)))))) pad_v b)
            c)
          ii)
        jj)
      (idx (S (S (S O))) Num
        (idx (S (S (S O))) (Ary ((S (S (S O))), (fle_self (S (S (S O)))),
          Num))
          (idx inch (Ary ((S (S (S O))), (fle_self (S (S (S O)))), (Ary ((S
            (S (S O))), (fle_self (S (S (S O)))), Num))))
            (idx outch (Ary (inch, (fle_self inch), (Ary ((S (S (S O))),
              (fle_self (S (S (S O)))), (Ary ((S (S (S O))),
              (fle_self (S (S (S O)))), Num)))))) w num)
            c)
          i1)
        j1))
    acc_v))))))))))),
  (Assign (Num, (Pair
  ((idxAcc
     (add
       (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
       (S O))
     Num
     (idxAcc
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (Ary
       ((add
          (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
            O)))
          (S O)),
       (fle_self
         (add
           (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
             O)))
           (S O))),
       Num)) o i0)
     j0),
  (add0 acc_v (idx outch Num bias num))))))))))))))))))))))))))

(** val conv4d_p0_k1_s2_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm **)

let conv4d_p0_k1_s2_par_comm batch inch outch m input w bias output =
  let half = add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O) in
  Seqfor (batch, (fun b -> Parfor (outch, (Ary
  ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
  (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))), (Ary
  ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
  (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))), Num)))),
  (idxAcc batch (Ary (outch, (fle_self outch), (Ary
    ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
    (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))), (Ary
    ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
    (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))),
    Num)))))) output b),
  (fun num o -> Seqfor (half, (fun i0 -> Seqfor (half, (fun j0 -> New (Num,
  (fun acc_tmp ->
  let Pair (acc_a, acc_v) = acc_tmp in
  Seq (Pair ((Assign (Num, (Pair (acc_a, zero)))), (Seq (Pair ((Seqfor (inch,
  (fun c ->
  let ii = mul (S (S O)) (fin2nat half i0) in
  let jj = mul (S (S O)) (fin2nat half j0) in
  Assign (Num, (Pair (acc_a,
  (add0
    (mul0
      (safe_idx_nat m Num
        (safe_idx_nat m (Ary (m, (fle_self m), Num))
          (idx inch (Ary (m, (fle_self m), (Ary (m, (fle_self m), Num))))
            (idx batch (Ary (inch, (fle_self inch), (Ary (m, (fle_self m),
              (Ary (m, (fle_self m), Num)))))) input b)
            c)
          ii)
        jj)
      (safe_idx_nat (S O) Num
        (safe_idx_nat (S O) (Ary ((S O), (fle_self (S O)), Num))
          (idx inch (Ary ((S O), (fle_self (S O)), (Ary ((S O),
            (fle_self (S O)), Num))))
            (idx outch (Ary (inch, (fle_self inch), (Ary ((S O),
              (fle_self (S O)), (Ary ((S O), (fle_self (S O)), Num)))))) w
              num)
            c)
          O)
        O))
    acc_v))))))),
  (Assign (Num, (Pair
  ((idxAcc (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)) Num
     (idxAcc (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)) (Ary
       ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
       (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))),
       Num)) o i0)
     j0),
  (add0 acc_v (idx outch Num bias num)))))))))))))))))))))

(** val conv4d_p3_k7_s2_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm **)

let conv4d_p3_k7_s2_par_comm batch inch outch m input w bias output =
  let half =
    add
      (Nat.div
        (add (sub m (S (S (S (S (S (S (S O))))))))
          (mul (S (S O)) (S (S (S O)))))
        (S (S O)))
      (S O)
  in
  New ((Ary (batch, (fle_self batch), (Ary (inch, (fle_self inch), (Ary
  ((add m (S (S (S (S (S (S O))))))),
  (fle_self (add m (S (S (S (S (S (S O)))))))), (Ary
  ((add m (S (S (S (S (S (S O))))))),
  (fle_self (add m (S (S (S (S (S (S O)))))))), Num)))))))), (fun pad_tmp ->
  let Pair (pad_a, pad_v) = pad_tmp in
  Seq (Pair ((Seqfor (batch, (fun b -> Parfor (inch, (Ary
  ((add m (S (S (S (S (S (S O))))))),
  (fle_self (add m (S (S (S (S (S (S O)))))))), (Ary
  ((add m (S (S (S (S (S (S O))))))),
  (fle_self (add m (S (S (S (S (S (S O)))))))), Num)))),
  (idxAcc batch (Ary (inch, (fle_self inch), (Ary
    ((add m (S (S (S (S (S (S O))))))),
    (fle_self (add m (S (S (S (S (S (S O)))))))), (Ary
    ((add m (S (S (S (S (S (S O))))))),
    (fle_self (add m (S (S (S (S (S (S O)))))))), Num)))))) pad_a b),
  (fun c po -> Seqfor ((add m (S (S (S (S (S (S O))))))), (fun i -> Seqfor
  ((add m (S (S (S (S (S (S O))))))), (fun j -> If ((BLt
  ((fin2nat (add m (S (S (S (S (S (S O))))))) i), (S (S (S O))))), (Pair
  ((Assign (Num, (Pair
  ((idxAcc (add m (S (S (S (S (S (S O))))))) Num
     (idxAcc (add m (S (S (S (S (S (S O))))))) (Ary
       ((add m (S (S (S (S (S (S O))))))),
       (fle_self (add m (S (S (S (S (S (S O)))))))), Num)) po i)
     j),
  zero)))), (If ((BLt ((fin2nat (add m (S (S (S (S (S (S O))))))) i),
  (add (S (S (S O))) m))), (Pair ((If ((BLt
  ((fin2nat (add m (S (S (S (S (S (S O))))))) j), (S (S (S O))))), (Pair
  ((Assign (Num, (Pair
  ((idxAcc (add m (S (S (S (S (S (S O))))))) Num
     (idxAcc (add m (S (S (S (S (S (S O))))))) (Ary
       ((add m (S (S (S (S (S (S O))))))),
       (fle_self (add m (S (S (S (S (S (S O)))))))), Num)) po i)
     j),
  zero)))), (If ((BLt ((fin2nat (add m (S (S (S (S (S (S O))))))) j),
  (add (S (S (S O))) m))), (Pair ((Assign (Num, (Pair
  ((idxAcc (add m (S (S (S (S (S (S O))))))) Num
     (idxAcc (add m (S (S (S (S (S (S O))))))) (Ary
       ((add m (S (S (S (S (S (S O))))))),
       (fle_self (add m (S (S (S (S (S (S O)))))))), Num)) po i)
     j),
  (safe_idx_nat m Num
    (safe_idx_nat m (Ary (m, (fle_self m), Num))
      (idx inch (Ary (m, (fle_self m), (Ary (m, (fle_self m), Num))))
        (idx batch (Ary (inch, (fle_self inch), (Ary (m, (fle_self m), (Ary
          (m, (fle_self m), Num)))))) input b)
        c)
      (sub (fin2nat (add m (S (S (S (S (S (S O))))))) i) (S (S (S O)))))
    (sub (fin2nat (add m (S (S (S (S (S (S O))))))) j) (S (S (S O))))))))),
  (Assign (Num, (Pair
  ((idxAcc (add m (S (S (S (S (S (S O))))))) Num
     (idxAcc (add m (S (S (S (S (S (S O))))))) (Ary
       ((add m (S (S (S (S (S (S O))))))),
       (fle_self (add m (S (S (S (S (S (S O)))))))), Num)) po i)
     j),
  zero)))))))))))), (Assign (Num, (Pair
  ((idxAcc (add m (S (S (S (S (S (S O))))))) Num
     (idxAcc (add m (S (S (S (S (S (S O))))))) (Ary
       ((add m (S (S (S (S (S (S O))))))),
       (fle_self (add m (S (S (S (S (S (S O)))))))), Num)) po i)
     j),
  zero)))))))))))))))))))), (Seqfor (batch, (fun b -> Parfor (outch, (Ary
  ((add
     (Nat.div
       (add (sub m (S (S (S (S (S (S (S O))))))))
         (mul (S (S O)) (S (S (S O)))))
       (S (S O)))
     (S O)),
  (fle_self
    (add
      (Nat.div
        (add (sub m (S (S (S (S (S (S (S O))))))))
          (mul (S (S O)) (S (S (S O)))))
        (S (S O)))
      (S O))),
  (Ary
  ((add
     (Nat.div
       (add (sub m (S (S (S (S (S (S (S O))))))))
         (mul (S (S O)) (S (S (S O)))))
       (S (S O)))
     (S O)),
  (fle_self
    (add
      (Nat.div
        (add (sub m (S (S (S (S (S (S (S O))))))))
          (mul (S (S O)) (S (S (S O)))))
        (S (S O)))
      (S O))),
  Num)))),
  (idxAcc batch (Ary (outch, (fle_self outch), (Ary
    ((add
       (Nat.div
         (add (sub m (S (S (S (S (S (S (S O))))))))
           (mul (S (S O)) (S (S (S O)))))
         (S (S O)))
       (S O)),
    (fle_self
      (add
        (Nat.div
          (add (sub m (S (S (S (S (S (S (S O))))))))
            (mul (S (S O)) (S (S (S O)))))
          (S (S O)))
        (S O))),
    (Ary
    ((add
       (Nat.div
         (add (sub m (S (S (S (S (S (S (S O))))))))
           (mul (S (S O)) (S (S (S O)))))
         (S (S O)))
       (S O)),
    (fle_self
      (add
        (Nat.div
          (add (sub m (S (S (S (S (S (S (S O))))))))
            (mul (S (S O)) (S (S (S O)))))
          (S (S O)))
        (S O))),
    Num)))))) output b),
  (fun num o -> Seqfor (half, (fun i0 -> Seqfor (half, (fun j0 -> New (Num,
  (fun acc_tmp ->
  let Pair (acc_a, acc_v) = acc_tmp in
  Seq (Pair ((Assign (Num, (Pair (acc_a, zero)))), (Seq (Pair ((Seqfor (inch,
  (fun c -> Seqfor ((S (S (S (S (S (S (S O))))))), (fun i1 -> Seqfor ((S (S
  (S (S (S (S (S O))))))), (fun j1 ->
  let ii =
    add (mul (S (S O)) (fin2nat half i0))
      (fin2nat (S (S (S (S (S (S (S O))))))) i1)
  in
  let jj =
    add (mul (S (S O)) (fin2nat half j0))
      (fin2nat (S (S (S (S (S (S (S O))))))) j1)
  in
  Assign (Num, (Pair (acc_a,
  (add0
    (mul0
      (safe_idx_nat (add m (S (S (S (S (S (S O))))))) Num
        (safe_idx_nat (add m (S (S (S (S (S (S O))))))) (Ary
          ((add m (S (S (S (S (S (S O))))))),
          (fle_self (add m (S (S (S (S (S (S O)))))))), Num))
          (idx inch (Ary ((add m (S (S (S (S (S (S O))))))),
            (fle_self (add m (S (S (S (S (S (S O)))))))), (Ary
            ((add m (S (S (S (S (S (S O))))))),
            (fle_self (add m (S (S (S (S (S (S O)))))))), Num))))
            (idx batch (Ary (inch, (fle_self inch), (Ary
              ((add m (S (S (S (S (S (S O))))))),
              (fle_self (add m (S (S (S (S (S (S O)))))))), (Ary
              ((add m (S (S (S (S (S (S O))))))),
              (fle_self (add m (S (S (S (S (S (S O)))))))), Num)))))) pad_v b)
            c)
          ii)
        jj)
      (idx (S (S (S (S (S (S (S O))))))) Num
        (idx (S (S (S (S (S (S (S O))))))) (Ary ((S (S (S (S (S (S (S
          O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num))
          (idx inch (Ary ((S (S (S (S (S (S (S O))))))),
            (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S
            (S O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num))))
            (idx outch (Ary (inch, (fle_self inch), (Ary ((S (S (S (S (S (S
              (S O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S
              (S (S (S (S (S (S O))))))),
              (fle_self (S (S (S (S (S (S (S O)))))))), Num)))))) w num)
            c)
          i1)
        j1))
    acc_v))))))))))),
  (Assign (Num, (Pair
  ((idxAcc
     (add
       (Nat.div
         (add (sub m (S (S (S (S (S (S (S O))))))))
           (mul (S (S O)) (S (S (S O)))))
         (S (S O)))
       (S O))
     Num
     (idxAcc
       (add
         (Nat.div
           (add (sub m (S (S (S (S (S (S (S O))))))))
             (mul (S (S O)) (S (S (S O)))))
           (S (S O)))
         (S O))
       (Ary
       ((add
          (Nat.div
            (add (sub m (S (S (S (S (S (S (S O))))))))
              (mul (S (S O)) (S (S (S O)))))
            (S (S O)))
          (S O)),
       (fle_self
         (add
           (Nat.div
             (add (sub m (S (S (S (S (S (S (S O))))))))
               (mul (S (S O)) (S (S (S O)))))
             (S (S O)))
           (S O))),
       Num)) o i0)
     j0),
  (add0 acc_v (idx outch Num bias num))))))))))))))))))))))))))

(** val batchNorm4d_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> exp -> exp -> exp -> exp -> acc
    -> comm **)

let batchNorm4d_par_comm batch channel n1 n2 input mean var gamma beta eps output =
  Seqfor (batch, (fun b -> Parfor (channel, (Ary (n1, (fle_self n1), (Ary
    (n2, (fle_self n2), Num)))),
    (idxAcc batch (Ary (channel, (fle_self channel), (Ary (n1, (fle_self n1),
      (Ary (n2, (fle_self n2), Num)))))) output b),
    (fun c o -> Seqfor (n1, (fun i -> Seqfor (n2, (fun j ->
    let x =
      sub0
        (idx n2 Num
          (idx n1 (Ary (n2, (fle_self n2), Num))
            (idx channel (Ary (n1, (fle_self n1), (Ary (n2, (fle_self n2),
              Num))))
              (idx batch (Ary (channel, (fle_self channel), (Ary (n1,
                (fle_self n1), (Ary (n2, (fle_self n2), Num)))))) input b)
              c)
            i)
          j)
        (idx channel Num mean c)
    in
    let norm = div0 x (sqrt (add0 (idx channel Num var c) eps)) in
    Assign (Num, (Pair
    ((idxAcc n2 Num (idxAcc n1 (Ary (n2, (fle_self n2), Num)) o i) j),
    (add0 (mul0 norm (idx channel Num gamma c)) (idx channel Num beta c)))))))))))))

(** val reLU4d_par_comm : nat -> nat -> nat -> nat -> exp -> acc -> comm **)

let reLU4d_par_comm batch filernum m1 m2 input output =
  Seqfor (batch, (fun b -> Parfor (filernum, (Ary (m1, (fle_self m1), (Ary
    (m2, (fle_self m2), Num)))),
    (idxAcc batch (Ary (filernum, (fle_self filernum), (Ary (m1,
      (fle_self m1), (Ary (m2, (fle_self m2), Num)))))) output b),
    (fun num o -> Seqfor (m1, (fun i0 -> Seqfor (m2, (fun i1 -> If
    ((leExp
       (idx m2 Num
         (idx m1 (Ary (m2, (fle_self m2), Num))
           (idx filernum (Ary (m1, (fle_self m1), (Ary (m2, (fle_self m2),
             Num))))
             (idx batch (Ary (filernum, (fle_self filernum), (Ary (m1,
               (fle_self m1), (Ary (m2, (fle_self m2), Num)))))) input b)
             num)
           i0)
         i1)
       zero),
    (Pair ((Assign (Num, (Pair
    ((idxAcc m2 Num (idxAcc m1 (Ary (m2, (fle_self m2), Num)) o i0) i1),
    zero)))), (Assign (Num, (Pair
    ((idxAcc m2 Num (idxAcc m1 (Ary (m2, (fle_self m2), Num)) o i0) i1),
    (idx m2 Num
      (idx m1 (Ary (m2, (fle_self m2), Num))
        (idx filernum (Ary (m1, (fle_self m1), (Ary (m2, (fle_self m2),
          Num))))
          (idx batch (Ary (filernum, (fle_self filernum), (Ary (m1,
            (fle_self m1), (Ary (m2, (fle_self m2), Num)))))) input b)
          num)
        i0)
      i1))))))))))))))))

(** val add4d_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> acc -> comm **)

let add4d_par_comm batch channel n1 n2 x y output =
  Seqfor (batch, (fun b -> Parfor (channel, (Ary (n1, (fle_self n1), (Ary
    (n2, (fle_self n2), Num)))),
    (idxAcc batch (Ary (channel, (fle_self channel), (Ary (n1, (fle_self n1),
      (Ary (n2, (fle_self n2), Num)))))) output b),
    (fun c o -> Seqfor (n1, (fun i -> Seqfor (n2, (fun j -> Assign (Num,
    (Pair ((idxAcc n2 Num (idxAcc n1 (Ary (n2, (fle_self n2), Num)) o i) j),
    (add0
      (idx n2 Num
        (idx n1 (Ary (n2, (fle_self n2), Num))
          (idx channel (Ary (n1, (fle_self n1), (Ary (n2, (fle_self n2),
            Num))))
            (idx batch (Ary (channel, (fle_self channel), (Ary (n1,
              (fle_self n1), (Ary (n2, (fle_self n2), Num)))))) x b)
            c)
          i)
        j)
      (idx n2 Num
        (idx n1 (Ary (n2, (fle_self n2), Num))
          (idx channel (Ary (n1, (fle_self n1), (Ary (n2, (fle_self n2),
            Num))))
            (idx batch (Ary (channel, (fle_self channel), (Ary (n1,
              (fle_self n1), (Ary (n2, (fle_self n2), Num)))))) y b)
            c)
          i)
        j)))))))))))))

(** val maxPool4d_pad_par_comm :
    nat -> nat -> nat -> nat -> nat -> nat -> exp -> acc -> comm **)

let maxPool4d_pad_par_comm batch channel m k s p input output =
  let outm = add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O) in
  let padm = add m (mul (S (S O)) p) in
  New ((Ary (batch, (fle_self batch), (Ary (channel, (fle_self channel), (Ary
  (padm, (fle_self padm), (Ary (padm, (fle_self padm), Num)))))))),
  (fun pad_tmp ->
  let Pair (pad_a, pad_v) = pad_tmp in
  Seq (Pair ((Seqfor (batch, (fun b -> Parfor (channel, (Ary (padm,
  (fle_self padm), (Ary (padm, (fle_self padm), Num)))),
  (idxAcc batch (Ary (channel, (fle_self channel), (Ary (padm,
    (fle_self padm), (Ary (padm, (fle_self padm), Num)))))) pad_a b),
  (fun c po -> Seqfor (padm, (fun i -> Seqfor (padm, (fun j -> If ((BLt
  ((fin2nat padm i), p)), (Pair ((Assign (Num, (Pair
  ((idxAcc padm Num (idxAcc padm (Ary (padm, (fle_self padm), Num)) po i) j),
  zero)))), (If ((BLt ((fin2nat padm i), (add p m))), (Pair ((If ((BLt
  ((fin2nat padm j), p)), (Pair ((Assign (Num, (Pair
  ((idxAcc padm Num (idxAcc padm (Ary (padm, (fle_self padm), Num)) po i) j),
  zero)))), (If ((BLt ((fin2nat padm j), (add p m))), (Pair ((Assign (Num,
  (Pair
  ((idxAcc padm Num (idxAcc padm (Ary (padm, (fle_self padm), Num)) po i) j),
  (safe_idx_nat m Num
    (safe_idx_nat m (Ary (m, (fle_self m), Num))
      (idx channel (Ary (m, (fle_self m), (Ary (m, (fle_self m), Num))))
        (idx batch (Ary (channel, (fle_self channel), (Ary (m, (fle_self m),
          (Ary (m, (fle_self m), Num)))))) input b)
        c)
      (sub (fin2nat padm i) p))
    (sub (fin2nat padm j) p)))))),
  (Assign (Num, (Pair
  ((idxAcc padm Num (idxAcc padm (Ary (padm, (fle_self padm), Num)) po i) j),
  zero)))))))))))), (Assign (Num, (Pair
  ((idxAcc padm Num (idxAcc padm (Ary (padm, (fle_self padm), Num)) po i) j),
  zero)))))))))))))))))))), (Seqfor (batch, (fun b -> Parfor (channel, (Ary
  ((add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)),
  (fle_self (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O))), (Ary
  ((add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)),
  (fle_self (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O))),
  Num)))),
  (idxAcc batch (Ary (channel, (fle_self channel), (Ary
    ((add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)),
    (fle_self (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O))),
    (Ary ((add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)),
    (fle_self (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O))),
    Num)))))) output b),
  (fun c o -> Seqfor (outm, (fun i0 -> Seqfor (outm, (fun j0 -> New (Num,
  (fun acc_tmp ->
  let Pair (acc_a, acc_v) = acc_tmp in
  Seq (Pair ((Assign (Num, (Pair (acc_a, zero)))), (Seq (Pair ((Seqfor (k,
  (fun di -> Seqfor (k, (fun dj ->
  let ii = add (mul s (fin2nat outm i0)) (fin2nat k di) in
  let jj = add (mul s (fin2nat outm j0)) (fin2nat k dj) in
  let v =
    safe_idx_nat padm Num
      (safe_idx_nat padm (Ary (padm, (fle_self padm), Num))
        (idx channel (Ary (padm, (fle_self padm), (Ary (padm,
          (fle_self padm), Num))))
          (idx batch (Ary (channel, (fle_self channel), (Ary (padm,
            (fle_self padm), (Ary (padm, (fle_self padm), Num)))))) pad_v b)
          c)
        ii)
      jj
  in
  If ((gtExp v acc_v), (Pair ((Assign (Num, (Pair (acc_a, v)))), Skip)))))))),
  (Assign (Num, (Pair
  ((idxAcc (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)) Num
     (idxAcc (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)) (Ary
       ((add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O)),
       (fle_self (add (Nat.div (add (sub m k) (mul (S (S O)) p)) s) (S O))),
       Num)) o i0)
     j0),
  acc_v))))))))))))))))))))))))

(** val globalAvgPool4d_par_comm :
    nat -> nat -> nat -> nat -> exp -> acc -> comm **)

let globalAvgPool4d_par_comm batch channel m1 m2 input output =
  Seqfor (batch, (fun b -> Parfor (channel, Num,
    (idxAcc batch (Ary (channel, (fle_self channel), Num)) output b),
    (fun c o -> Loopacc (Num, (fun tmp ->
    let acc_a = vwt Num tmp in
    let acc_v = vrd Num tmp in
    Seq (Pair ((Assign (Num, (Pair (acc_a, zero)))), (Seq (Pair ((Seqfor
    ((mul m1 m2), (fun k ->
    let i = Nat.div (fin2nat (mul m1 m2) k) m2 in
    let j = Nat.modulo (fin2nat (mul m1 m2) k) m2 in
    Assign (Num, (Pair (acc_a,
    (add0
      (safe_idx_nat m2 Num
        (safe_idx_nat m1 (Ary (m2, (fle_self m2), Num))
          (idx channel (Ary (m1, (fle_self m1), (Ary (m2, (fle_self m2),
            Num))))
            (idx batch (Ary (channel, (fle_self channel), (Ary (m1,
              (fle_self m1), (Ary (m2, (fle_self m2), Num)))))) input b)
            c)
          i)
        j)
      acc_v))))))),
    (Assign (Num, (Pair (o, (div_n acc_v (mul m1 m2)))))))))))))))))

(** val linear2d_par_comm :
    nat -> nat -> nat -> exp -> exp -> exp -> acc -> comm **)

let linear2d_par_comm batch m outnum w b input output =
  Seqfor (batch, (fun bi -> Parfor (outnum, Num,
    (idxAcc batch (Ary (outnum, (fle_self outnum), Num)) output bi),
    (fun out o -> Loopacc (Num, (fun tmp ->
    let w_acc = vwt Num tmp in
    let v = vrd Num tmp in
    Seq (Pair ((Assign (Num, (Pair (w_acc, zero)))), (Seq (Pair ((Seqfor (m,
    (fun i -> Assign (Num, (Pair (w_acc,
    (add0
      (mul0 (idx m Num (idx batch (Ary (m, (fle_self m), Num)) input bi) i)
        (idx m Num (idx outnum (Ary (m, (fle_self m), Num)) w out) i))
      v))))))),
    (Assign (Num, (Pair (o, (add0 v (idx outnum Num b out)))))))))))))))))

(** val resNet_BB_id_par_comm :
    nat -> nat -> nat -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp
    -> exp -> exp -> exp -> exp -> exp -> exp -> acc -> acc -> acc -> acc ->
    acc -> acc -> string -> string -> string -> string -> string -> string ->
    comm **)

let resNet_BB_id_par_comm batch ch m input w1 b1 w2 b2 mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps conv1_out bn1_out relu1_out conv2_out bn2_out add_out conv1_s bn1_s relu1_s conv2_s bn2_s add_s =
  Seq (Pair ((conv4d_p1_k3_par_comm batch ch ch m input w1 b1 conv1_out),
    (Seq (Pair
    ((batchNorm4d_par_comm batch ch m m
       (vrd (Ary (batch, (fle_self batch), (Ary (ch, (fle_self ch), (Ary (m,
         (fle_self m), (Ary (m, (fle_self m), Num)))))))) conv1_s)
       mean1 var1 gamma1 beta1 eps bn1_out),
    (Seq (Pair
    ((reLU4d_par_comm batch ch m m
       (vrd (Ary (batch, (fle_self batch), (Ary (ch, (fle_self ch), (Ary (m,
         (fle_self m), (Ary (m, (fle_self m), Num)))))))) bn1_s)
       relu1_out),
    (Seq (Pair
    ((conv4d_p1_k3_par_comm batch ch ch m
       (vrd (Ary (batch, (fle_self batch), (Ary (ch, (fle_self ch), (Ary (m,
         (fle_self m), (Ary (m, (fle_self m), Num)))))))) relu1_s)
       w2 b2 conv2_out),
    (Seq (Pair
    ((batchNorm4d_par_comm batch ch m m
       (vrd (Ary (batch, (fle_self batch), (Ary (ch, (fle_self ch), (Ary (m,
         (fle_self m), (Ary (m, (fle_self m), Num)))))))) conv2_s)
       mean2 var2 gamma2 beta2 eps bn2_out),
    (Seq (Pair
    ((add4d_par_comm batch ch m m
       (vrd (Ary (batch, (fle_self batch), (Ary (ch, (fle_self ch), (Ary (m,
         (fle_self m), (Ary (m, (fle_self m), Num)))))))) bn2_s)
       input add_out),
    (reLU4d_par_comm batch ch m m
      (vrd (Ary (batch, (fle_self batch), (Ary (ch, (fle_self ch), (Ary (m,
        (fle_self m), (Ary (m, (fle_self m), Num)))))))) add_s)
      add_out))))))))))))))))))

(** val resNet_BB_proj_par_comm :
    nat -> nat -> nat -> nat -> exp -> exp -> exp -> exp -> exp -> exp -> exp
    -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> acc -> acc -> acc ->
    acc -> acc -> acc -> acc -> exp -> exp -> exp -> exp -> exp -> exp ->
    string -> string -> string -> string -> string -> string -> string -> comm **)

let resNet_BB_proj_par_comm batch inch outch m input w1 b1 w2 b2 mean1 var1 gamma1 beta1 mean2 var2 gamma2 beta2 eps conv1_out bn1_out relu1_out conv2_out bn2_out add_out shortcut_out shortcut_w shortcut_b shortcut_mean shortcut_var shortcut_gamma shortcut_beta shortcut_s conv1_s bn1_s relu1_s conv2_s bn2_s add_s =
  Seq (Pair
    ((conv4d_p0_k1_s2_par_comm batch inch outch m input shortcut_w shortcut_b
       shortcut_out),
    (Seq (Pair
    ((batchNorm4d_par_comm batch outch
       (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))
       (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
         (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))),
         (Ary ((add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O)),
         (fle_self (add (Nat.div (add (sub m (S O)) O) (S (S O))) (S O))),
         Num)))))))) shortcut_s)
       shortcut_mean shortcut_var shortcut_gamma shortcut_beta eps
       shortcut_out),
    (Seq (Pair
    ((conv4d_p1_k3_s2_par_comm batch inch outch m input w1 b1 conv1_out),
    (Seq (Pair
    ((batchNorm4d_par_comm batch outch
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         Num)))))))) conv1_s)
       mean1 var1 gamma1 beta1 eps bn1_out),
    (Seq (Pair
    ((reLU4d_par_comm batch outch
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         Num)))))))) bn1_s)
       relu1_out),
    (Seq (Pair
    ((conv4d_p1_k3_par_comm batch outch outch
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         Num)))))))) relu1_s)
       w2 b2 conv2_out),
    (Seq (Pair
    ((batchNorm4d_par_comm batch outch
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         Num)))))))) conv2_s)
       mean2 var2 gamma2 beta2 eps bn2_out),
    (Seq (Pair
    ((add4d_par_comm batch outch
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (add
         (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
         (S O))
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         Num)))))))) bn2_s)
       (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         (Ary
         ((add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O)),
         (fle_self
           (add
             (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
               O)))
             (S O))),
         Num)))))))) shortcut_s)
       add_out),
    (reLU4d_par_comm batch outch
      (add
        (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
        (S O))
      (add
        (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S O)))
        (S O))
      (vrd (Ary (batch, (fle_self batch), (Ary (outch, (fle_self outch), (Ary
        ((add
           (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
             O)))
           (S O)),
        (fle_self
          (add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O))),
        (Ary
        ((add
           (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
             O)))
           (S O)),
        (fle_self
          (add
            (Nat.div (add (sub m (S (S (S O)))) (mul (S (S O)) (S O))) (S (S
              O)))
            (S O))),
        Num)))))))) add_s)
      add_out))))))))))))))))))))))))

(** val resnet18_par_comm : comm **)

let resnet18_par_comm =
  Seq (Pair
    ((conv4d_p3_k7_s2_par_comm (S O) (S (S (S O))) (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       resnet18_input resnet18_conv1_w resnet18_conv1_b resnet18_conv1_out),
    (Seq (Pair
    ((batchNorm4d_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (True, True, False, False, False, True,
         True, False)), (String ((Ascii (True, True, True, True, False, True,
         True, False)), (String ((Ascii (False, True, True, True, False,
         True, True, False)), (String ((Ascii (False, True, True, False,
         True, True, True, False)), (String ((Ascii (True, False, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True, True,
         True, True, False, True, True, False)), (String ((Ascii (True,
         False, True, False, True, True, True, False)), (String ((Ascii
         (False, False, True, False, True, True, True, False)),
         EmptyString)))))))))))))))))))
       resnet18_bn1_mean resnet18_bn1_var resnet18_bn1_gamma
       resnet18_bn1_beta resnet18_eps resnet18_bn1_out),
    (Seq (Pair
    ((reLU4d_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, True, False, False, False, True,
         True, False)), (String ((Ascii (False, True, True, True, False,
         True, True, False)), (String ((Ascii (True, False, False, False,
         True, True, False, False)), (String ((Ascii (True, True, True, True,
         True, False, True, False)), (String ((Ascii (True, True, True, True,
         False, True, True, False)), (String ((Ascii (True, False, True,
         False, True, True, True, False)), (String ((Ascii (False, False,
         True, False, True, True, True, False)), EmptyString)))))))))))))))
       resnet18_relu1_out),
    (Seq (Pair
    ((maxPool4d_pad_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S O))) (S (S O)) (S O)
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, True, False, False, True, True,
         True, False)), (String ((Ascii (True, False, True, False, False,
         True, True, False)), (String ((Ascii (False, False, True, True,
         False, True, True, False)), (String ((Ascii (True, False, True,
         False, True, True, True, False)), (String ((Ascii (True, False,
         False, False, True, True, False, False)), (String ((Ascii (True,
         True, True, True, True, False, True, False)), (String ((Ascii (True,
         True, True, True, False, True, True, False)), (String ((Ascii (True,
         False, True, False, True, True, True, False)), (String ((Ascii
         (False, False, True, False, True, True, True, False)),
         EmptyString)))))))))))))))))))
       resnet18_pool_out),
    (Seq (Pair
    ((resNet_BB_id_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, False, False, True, True,
         True, False)), (String ((Ascii (True, True, True, True, False, True,
         True, False)), (String ((Ascii (True, True, True, True, False, True,
         True, False)), (String ((Ascii (False, False, True, True, False,
         True, True, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (True, True, True, True,
         False, True, True, False)), (String ((Ascii (True, False, True,
         False, True, True, True, False)), (String ((Ascii (False, False,
         True, False, True, True, True, False)), EmptyString)))))))))))))))))
       resnet18_l1_b1_w1 resnet18_l1_b1_b1 resnet18_l1_b1_w2
       resnet18_l1_b1_b2 resnet18_l1_b1_bn1_mean resnet18_l1_b1_bn1_var
       resnet18_l1_b1_bn1_gamma resnet18_l1_b1_bn1_beta
       resnet18_l1_b1_bn2_mean resnet18_l1_b1_bn2_var
       resnet18_l1_b1_bn2_gamma resnet18_l1_b1_bn2_beta resnet18_eps
       resnet18_l1_b1_conv1_out resnet18_l1_b1_bn1_out
       resnet18_l1_b1_relu1_out resnet18_l1_b1_conv2_out
       resnet18_l1_b1_bn2_out resnet18_l1_b1_add_out (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       False, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, False, False, False, True, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, False, True, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, False, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (False, True, False, False, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, False, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (False, False, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, False, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, False, True, True,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (False, True, False, False, True,
       True, False, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString)))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, False, True, True, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (True, True, True,
       True, False, True, True, False)), (String ((Ascii (True, False, True,
       False, True, True, True, False)), (String ((Ascii (False, False, True,
       False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_id_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (True, False, False, False, True,
         True, False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (True, False, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l1_b2_w1 resnet18_l1_b2_b1 resnet18_l1_b2_w2
       resnet18_l1_b2_b2 resnet18_l1_b2_bn1_mean resnet18_l1_b2_bn1_var
       resnet18_l1_b2_bn1_gamma resnet18_l1_b2_bn1_beta
       resnet18_l1_b2_bn2_mean resnet18_l1_b2_bn2_var
       resnet18_l1_b2_bn2_gamma resnet18_l1_b2_bn2_beta resnet18_eps
       resnet18_l1_b2_conv1_out resnet18_l1_b2_bn1_out
       resnet18_l1_b2_relu1_out resnet18_l1_b2_conv2_out
       resnet18_l1_b2_bn2_out resnet18_l1_b2_add_out (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       False, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, False, False, False, True, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, False, True, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, False, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (False, True, False, False, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, False, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (False, True, False, False, True, True, True,
       False)), (String ((Ascii (True, False, True, False, False, True, True,
       False)), (String ((Ascii (False, False, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, False, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, False, True, True,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (False, True, False, False, True,
       True, False, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString)))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, False, True, True, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (True, True, True,
       True, False, True, True, False)), (String ((Ascii (True, False, True,
       False, True, True, True, False)), (String ((Ascii (False, False, True,
       False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_proj_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S
       O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (True, False, False, False, True,
         True, False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (False, True, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l2_b1_w1 resnet18_l2_b1_b1 resnet18_l2_b1_w2
       resnet18_l2_b1_b2 resnet18_l2_b1_bn1_mean resnet18_l2_b1_bn1_var
       resnet18_l2_b1_bn1_gamma resnet18_l2_b1_bn1_beta
       resnet18_l2_b1_bn2_mean resnet18_l2_b1_bn2_var
       resnet18_l2_b1_bn2_gamma resnet18_l2_b1_bn2_beta resnet18_eps
       resnet18_l2_b1_conv1_out resnet18_l2_b1_bn1_out
       resnet18_l2_b1_relu1_out resnet18_l2_b1_conv2_out
       resnet18_l2_b1_bn2_out resnet18_l2_b1_add_out
       resnet18_l2_b1_shortcut_out resnet18_l2_b1_shortcut_w
       resnet18_l2_b1_shortcut_b resnet18_l2_b1_shortcut_mean
       resnet18_l2_b1_shortcut_var resnet18_l2_b1_shortcut_gamma
       resnet18_l2_b1_shortcut_beta (String ((Ascii (False, False, True,
       True, False, True, True, False)), (String ((Ascii (False, True, False,
       False, True, True, False, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (False, True, False,
       False, False, True, True, False)), (String ((Ascii (True, False,
       False, False, True, True, False, False)), (String ((Ascii (True, True,
       True, True, True, False, True, False)), (String ((Ascii (True, True,
       False, False, True, True, True, False)), (String ((Ascii (False,
       False, False, True, False, True, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       True, False, False, False, True, True, False)), (String ((Ascii (True,
       False, True, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (True,
       False, True, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, False, False, False, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, False, False, True,
       True, False, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString)))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (False, False, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, False, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, False, True, True,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (False, True, False, False, True,
       True, False, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString)))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, False, True, True, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (True, True, True,
       True, False, True, True, False)), (String ((Ascii (True, False, True,
       False, True, True, True, False)), (String ((Ascii (False, False, True,
       False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_id_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S O))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S O)))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S O)))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (False, True, False, False, True,
         True, False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (True, False, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l2_b2_w1 resnet18_l2_b2_b1 resnet18_l2_b2_w2
       resnet18_l2_b2_b2 resnet18_l2_b2_bn1_mean resnet18_l2_b2_bn1_var
       resnet18_l2_b2_bn1_gamma resnet18_l2_b2_bn1_beta
       resnet18_l2_b2_bn2_mean resnet18_l2_b2_bn2_var
       resnet18_l2_b2_bn2_gamma resnet18_l2_b2_bn2_beta resnet18_eps
       resnet18_l2_b2_conv1_out resnet18_l2_b2_bn1_out
       resnet18_l2_b2_relu1_out resnet18_l2_b2_conv2_out
       resnet18_l2_b2_bn2_out resnet18_l2_b2_add_out (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, True, False, False, False, True, True, False)), (String
       ((Ascii (True, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, False, True, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, True, True, True, False)), (String
       ((Ascii (True, False, True, False, False, True, True, False)), (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, True, False, True, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, True, False, False, False, True, True, False)), (String
       ((Ascii (True, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, False, True, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, False, False, False, False, True, True, False)),
       (String ((Ascii (False, False, True, False, False, True, True,
       False)), (String ((Ascii (False, False, True, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_proj_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S O))))))))))))))))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S O)))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S O)))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (False, True, False, False, True,
         True, False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (False, True, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l3_b1_w1 resnet18_l3_b1_b1 resnet18_l3_b1_w2
       resnet18_l3_b1_b2 resnet18_l3_b1_bn1_mean resnet18_l3_b1_bn1_var
       resnet18_l3_b1_bn1_gamma resnet18_l3_b1_bn1_beta
       resnet18_l3_b1_bn2_mean resnet18_l3_b1_bn2_var
       resnet18_l3_b1_bn2_gamma resnet18_l3_b1_bn2_beta resnet18_eps
       resnet18_l3_b1_conv1_out resnet18_l3_b1_bn1_out
       resnet18_l3_b1_relu1_out resnet18_l3_b1_conv2_out
       resnet18_l3_b1_bn2_out resnet18_l3_b1_add_out
       resnet18_l3_b1_shortcut_out resnet18_l3_b1_shortcut_w
       resnet18_l3_b1_shortcut_b resnet18_l3_b1_shortcut_mean
       resnet18_l3_b1_shortcut_var resnet18_l3_b1_shortcut_gamma
       resnet18_l3_b1_shortcut_beta (String ((Ascii (False, False, True,
       True, False, True, True, False)), (String ((Ascii (True, True, False,
       False, True, True, False, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (False, True, False,
       False, False, True, True, False)), (String ((Ascii (True, False,
       False, False, True, True, False, False)), (String ((Ascii (True, True,
       True, True, True, False, True, False)), (String ((Ascii (True, True,
       False, False, True, True, True, False)), (String ((Ascii (False,
       False, False, True, False, True, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       True, False, False, False, True, True, False)), (String ((Ascii (True,
       False, True, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (True,
       False, True, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, True, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, False, False, False, True, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, False, True, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, True, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, True, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, True, True, True, False)),
       (String ((Ascii (True, False, True, False, False, True, True, False)),
       (String ((Ascii (False, False, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, True, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, False, False, False, True, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, True, False, True, True, True, False)),
       (String ((Ascii (False, True, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, True, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (True, True, False, False, True, True, False, False)), (String ((Ascii
       (True, True, True, True, True, False, True, False)), (String ((Ascii
       (False, True, False, False, False, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, False, False, False, False, True, True,
       False)), (String ((Ascii (False, False, True, False, False, True,
       True, False)), (String ((Ascii (False, False, True, False, False,
       True, True, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_id_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (True, True, False, False, True,
         True, False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (True, False, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l3_b2_w1 resnet18_l3_b2_b1 resnet18_l3_b2_w2
       resnet18_l3_b2_b2 resnet18_l3_b2_bn1_mean resnet18_l3_b2_bn1_var
       resnet18_l3_b2_bn1_gamma resnet18_l3_b2_bn1_beta
       resnet18_l3_b2_bn2_mean resnet18_l3_b2_bn2_var
       resnet18_l3_b2_bn2_gamma resnet18_l3_b2_bn2_beta resnet18_eps
       resnet18_l3_b2_conv1_out resnet18_l3_b2_bn1_out
       resnet18_l3_b2_relu1_out resnet18_l3_b2_conv2_out
       resnet18_l3_b2_bn2_out resnet18_l3_b2_add_out (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, True, False, False, False, True, True, False)), (String
       ((Ascii (True, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, False, True, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, True, True, True, False)), (String
       ((Ascii (True, False, True, False, False, True, True, False)), (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, True, False, True, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, True, False, False, False, True, True, False)), (String
       ((Ascii (True, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, False, True, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (True,
       True, False, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, False, False, False, False, True, True, False)),
       (String ((Ascii (False, False, True, False, False, True, True,
       False)), (String ((Ascii (False, False, True, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_proj_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
         (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))),
         Num)))))))) (String ((Ascii (False, False, True, True, False, True,
         True, False)), (String ((Ascii (True, True, False, False, True,
         True, False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (False, True, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l4_b1_w1 resnet18_l4_b1_b1 resnet18_l4_b1_w2
       resnet18_l4_b1_b2 resnet18_l4_b1_bn1_mean resnet18_l4_b1_bn1_var
       resnet18_l4_b1_bn1_gamma resnet18_l4_b1_bn1_beta
       resnet18_l4_b1_bn2_mean resnet18_l4_b1_bn2_var
       resnet18_l4_b1_bn2_gamma resnet18_l4_b1_bn2_beta resnet18_eps
       resnet18_l4_b1_conv1_out resnet18_l4_b1_bn1_out
       resnet18_l4_b1_relu1_out resnet18_l4_b1_conv2_out
       resnet18_l4_b1_bn2_out resnet18_l4_b1_add_out
       resnet18_l4_b1_shortcut_out resnet18_l4_b1_shortcut_w
       resnet18_l4_b1_shortcut_b resnet18_l4_b1_shortcut_mean
       resnet18_l4_b1_shortcut_var resnet18_l4_b1_shortcut_gamma
       resnet18_l4_b1_shortcut_beta (String ((Ascii (False, False, True,
       True, False, True, True, False)), (String ((Ascii (False, False, True,
       False, True, True, False, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (False, True, False,
       False, False, True, True, False)), (String ((Ascii (True, False,
       False, False, True, True, False, False)), (String ((Ascii (True, True,
       True, True, True, False, True, False)), (String ((Ascii (True, True,
       False, False, True, True, True, False)), (String ((Ascii (False,
       False, False, True, False, True, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (False,
       True, False, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       True, False, False, False, True, True, False)), (String ((Ascii (True,
       False, True, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (True,
       True, True, True, False, True, True, False)), (String ((Ascii (True,
       False, True, False, True, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))))))))) (String ((Ascii
       (False, False, True, True, False, True, True, False)), (String ((Ascii
       (False, False, True, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, False, False, False, True, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, True, False, True, True,
       False)), (String ((Ascii (False, True, True, False, True, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, False, True, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, False, False, True,
       True, False, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString)))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, False, True, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       True, False)), (String ((Ascii (True, False, True, False, False, True,
       True, False)), (String ((Ascii (False, False, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, False, True, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, False, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, True, False, True,
       True, False)), (String ((Ascii (False, True, True, False, True, True,
       True, False)), (String ((Ascii (False, True, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString)))))))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, False, True, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (False, True, False, False, False,
       True, True, False)), (String ((Ascii (False, True, True, True, False,
       True, True, False)), (String ((Ascii (False, True, False, False, True,
       True, False, False)), (String ((Ascii (True, True, True, True, True,
       False, True, False)), (String ((Ascii (True, True, True, True, False,
       True, True, False)), (String ((Ascii (True, False, True, False, True,
       True, True, False)), (String ((Ascii (False, False, True, False, True,
       True, True, False)), EmptyString)))))))))))))))))))))))))) (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (False, False, True, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (False, True, False, False, False, True, True,
       False)), (String ((Ascii (True, False, False, False, True, True,
       False, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, False, False, False, False,
       True, True, False)), (String ((Ascii (False, False, True, False,
       False, True, True, False)), (String ((Ascii (False, False, True,
       False, False, True, True, False)), (String ((Ascii (True, True, True,
       True, True, False, True, False)), (String ((Ascii (True, True, True,
       True, False, True, True, False)), (String ((Ascii (True, False, True,
       False, True, True, True, False)), (String ((Ascii (False, False, True,
       False, True, True, True, False)),
       EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((resNet_BB_id_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S O)))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S O))))))),
         (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
         O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num))))))))
         (String ((Ascii (False, False, True, True, False, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (True, False, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_l4_b2_w1 resnet18_l4_b2_b1 resnet18_l4_b2_w2
       resnet18_l4_b2_b2 resnet18_l4_b2_bn1_mean resnet18_l4_b2_bn1_var
       resnet18_l4_b2_bn1_gamma resnet18_l4_b2_bn1_beta
       resnet18_l4_b2_bn2_mean resnet18_l4_b2_bn2_var
       resnet18_l4_b2_bn2_gamma resnet18_l4_b2_bn2_beta resnet18_eps
       resnet18_l4_b2_conv1_out resnet18_l4_b2_bn1_out
       resnet18_l4_b2_relu1_out resnet18_l4_b2_conv2_out
       resnet18_l4_b2_bn2_out resnet18_l4_b2_add_out (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, True, False, False, False, True, True, False)), (String
       ((Ascii (True, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, False, True, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, True, True, True, False)), (String
       ((Ascii (True, False, True, False, False, True, True, False)), (String
       ((Ascii (False, False, True, True, False, True, True, False)), (String
       ((Ascii (True, False, True, False, True, True, True, False)), (String
       ((Ascii (True, False, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, True, False, False, False, True, True, False)), (String
       ((Ascii (True, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, True, False, True, True, False)), (String
       ((Ascii (False, True, True, False, True, True, True, False)), (String
       ((Ascii (False, True, False, False, True, True, False, False)),
       (String ((Ascii (True, True, True, True, True, False, True, False)),
       (String ((Ascii (True, True, True, True, False, True, True, False)),
       (String ((Ascii (True, False, True, False, True, True, True, False)),
       (String ((Ascii (False, False, True, False, True, True, True, False)),
       EmptyString)))))))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (False, True, False, False, False, True, True, False)),
       (String ((Ascii (False, True, True, True, False, True, True, False)),
       (String ((Ascii (False, True, False, False, True, True, False,
       False)), (String ((Ascii (True, True, True, True, True, False, True,
       False)), (String ((Ascii (True, True, True, True, False, True, True,
       False)), (String ((Ascii (True, False, True, False, True, True, True,
       False)), (String ((Ascii (False, False, True, False, True, True, True,
       False)), EmptyString)))))))))))))))))))))))))) (String ((Ascii (False,
       False, True, True, False, True, True, False)), (String ((Ascii (False,
       False, True, False, True, True, False, False)), (String ((Ascii (True,
       True, True, True, True, False, True, False)), (String ((Ascii (False,
       True, False, False, False, True, True, False)), (String ((Ascii
       (False, True, False, False, True, True, False, False)), (String
       ((Ascii (True, True, True, True, True, False, True, False)), (String
       ((Ascii (True, False, False, False, False, True, True, False)),
       (String ((Ascii (False, False, True, False, False, True, True,
       False)), (String ((Ascii (False, False, True, False, False, True,
       True, False)), (String ((Ascii (True, True, True, True, True, False,
       True, False)), (String ((Ascii (True, True, True, True, False, True,
       True, False)), (String ((Ascii (True, False, True, False, True, True,
       True, False)), (String ((Ascii (False, False, True, False, True, True,
       True, False)), EmptyString))))))))))))))))))))))))))),
    (Seq (Pair
    ((globalAvgPool4d_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (S (S (S (S (S (S (S O))))))) (S (S (S (S (S (S (S O)))))))
       (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
         (Ary ((S (S (S (S (S (S (S O))))))),
         (fle_self (S (S (S (S (S (S (S O)))))))), (Ary ((S (S (S (S (S (S (S
         O))))))), (fle_self (S (S (S (S (S (S (S O)))))))), Num))))))))
         (String ((Ascii (False, False, True, True, False, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         False, False)), (String ((Ascii (True, True, True, True, True,
         False, True, False)), (String ((Ascii (False, True, False, False,
         False, True, True, False)), (String ((Ascii (False, True, False,
         False, True, True, False, False)), (String ((Ascii (True, True,
         True, True, True, False, True, False)), (String ((Ascii (True,
         False, False, False, False, True, True, False)), (String ((Ascii
         (False, False, True, False, False, True, True, False)), (String
         ((Ascii (False, False, True, False, False, True, True, False)),
         (String ((Ascii (True, True, True, True, True, False, True, False)),
         (String ((Ascii (True, True, True, True, False, True, True, False)),
         (String ((Ascii (True, False, True, False, True, True, True,
         False)), (String ((Ascii (False, False, True, False, True, True,
         True, False)), EmptyString)))))))))))))))))))))))))))
       resnet18_avgpool_out),
    (linear2d_par_comm (S O) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      resnet18_fc_w resnet18_fc_b
      (vrd (Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),
        Num)))) (String ((Ascii (True, False, False, False, False, True,
        True, False)), (String ((Ascii (False, True, True, False, True, True,
        True, False)), (String ((Ascii (True, True, True, False, False, True,
        True, False)), (String ((Ascii (False, False, False, False, True,
        True, True, False)), (String ((Ascii (True, True, True, True, False,
        True, True, False)), (String ((Ascii (True, True, True, True, False,
        True, True, False)), (String ((Ascii (False, False, True, True,
        False, True, True, False)), (String ((Ascii (True, True, True, True,
        True, False, True, False)), (String ((Ascii (True, True, True, True,
        False, True, True, False)), (String ((Ascii (True, False, True,
        False, True, True, True, False)), (String ((Ascii (False, False,
        True, False, True, True, True, False)),
        EmptyString)))))))))))))))))))))))
      resnet18_output)))))))))))))))))))))))))))))))))))))))
