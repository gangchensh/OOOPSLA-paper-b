
type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

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

(** val eqb : bool -> bool -> bool **)

let eqb b1 b2 =
  match b1 with
  | True -> b2
  | False -> (match b2 with
              | True -> False
              | False -> True)

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

  (** val iter : ('a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

  let rec iter f x = function
  | XI n' -> f (iter f (iter f x n') n')
  | XO n' -> iter f (iter f x n') n'
  | XH -> f x

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

  (** val pow_pos : z -> positive -> z **)

  let pow_pos z0 =
    Pos.iter (mul z0) (Zpos XH)

  (** val pow : z -> z -> z **)

  let pow x = function
  | Z0 -> Zpos XH
  | Zpos p -> pow_pos x p
  | Zneg _ -> Z0

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

  (** val min : z -> z -> z **)

  let min n m =
    match compare n m with
    | Gt -> m
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

(** val pow_pos0 : ('a1 -> 'a1 -> 'a1) -> 'a1 -> positive -> 'a1 **)

let rec pow_pos0 rmul x = function
| XI i0 -> let p = pow_pos0 rmul x i0 in rmul x (rmul p p)
| XO i0 -> let p = pow_pos0 rmul x i0 in rmul p p
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
  pow_pos0 qmult

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

(** val linear_search_conform : (nat -> sumbool) -> nat -> nat **)

let rec linear_search_conform p_dec start =
  match p_dec start with
  | Left -> start
  | Right -> linear_search_conform p_dec (S start)

(** val linear_search_from_0_conform : (nat -> sumbool) -> nat **)

let linear_search_from_0_conform p_dec =
  linear_search_conform p_dec O

(** val constructive_indefinite_ground_description_nat :
    (nat -> sumbool) -> nat **)

let constructive_indefinite_ground_description_nat =
  linear_search_from_0_conform

(** val p'_decidable : (nat -> 'a1) -> ('a1 -> sumbool) -> nat -> sumbool **)

let p'_decidable g p_decidable n =
  p_decidable (g n)

(** val constructive_indefinite_ground_description :
    ('a1 -> nat) -> (nat -> 'a1) -> ('a1 -> sumbool) -> 'a1 **)

let constructive_indefinite_ground_description _ g p_decidable =
  let h1 =
    constructive_indefinite_ground_description_nat
      (p'_decidable g p_decidable)
  in
  g h1

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

(** val z_inj_nat : z -> nat **)

let z_inj_nat = function
| Z0 -> O
| Zpos p -> Coq_Pos.to_nat (XO p)
| Zneg p -> Coq_Pos.to_nat (Coq_Pos.pred_double p)

(** val z_inj_nat_rev : nat -> z **)

let z_inj_nat_rev n = match n with
| O -> Z0
| S _ ->
  (match Coq_Pos.of_nat n with
   | XI p -> Zneg (Coq_Pos.succ p)
   | XO p -> Zpos p
   | XH -> Zneg XH)

(** val constructive_indefinite_ground_description_Z : (z -> sumbool) -> z **)

let constructive_indefinite_ground_description_Z x =
  constructive_indefinite_ground_description z_inj_nat z_inj_nat_rev x

type cReal = { seq : (z -> q); scale : z }

type cRealLt = z

type cReal_appart = (cRealLt, cRealLt) sum

(** val cRealLt_lpo_dec :
    cReal -> cReal -> (__ -> (nat -> sumbool) -> nat sumor) -> (cRealLt, __)
    sum **)

let cRealLt_lpo_dec x y lpo =
  let s =
    lpo __ (fun n ->
      let s =
        qlt_le_dec
          (qmult { qnum = (Zpos (XO XH)); qden = XH }
            (qpower { qnum = (Zpos (XO XH)); qden = XH } (z_inj_nat_rev n)))
          (qminus (y.seq (z_inj_nat_rev n)) (x.seq (z_inj_nat_rev n)))
      in
      (match s with
       | Left -> Right
       | Right -> Left))
  in
  (match s with
   | Inleft s0 -> Inl (z_inj_nat_rev s0)
   | Inright -> Inr __)

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

(** val cRealLowerBound : cReal -> cRealLt -> z **)

let cRealLowerBound _ xPos =
  xPos

(** val cReal_inv_pos_cm : cReal -> cRealLt -> z -> z **)

let cReal_inv_pos_cm x xPos n =
  Z.min (cRealLowerBound x xPos)
    (Z.add n (Z.mul (Zpos (XO XH)) (cRealLowerBound x xPos)))

(** val cReal_inv_pos_seq : cReal -> cRealLt -> z -> q **)

let cReal_inv_pos_seq x xPos n =
  qinv (x.seq (cReal_inv_pos_cm x xPos n))

(** val cReal_inv_pos_scale : cReal -> cRealLt -> z **)

let cReal_inv_pos_scale x xPos =
  Z.opp (cRealLowerBound x xPos)

(** val cReal_inv_pos : cReal -> cRealLt -> cReal **)

let cReal_inv_pos x hxpos =
  { seq = (cReal_inv_pos_seq x hxpos); scale = (cReal_inv_pos_scale x hxpos) }

(** val cReal_neg_lt_pos : cReal -> cRealLt -> cRealLt **)

let cReal_neg_lt_pos _ h =
  h

(** val cReal_inv : cReal -> cReal_appart -> cReal **)

let cReal_inv x = function
| Inl xNeg ->
  cReal_opp (cReal_inv_pos (cReal_opp x) (cReal_neg_lt_pos x xNeg))
| Inr xPos -> cReal_inv_pos x xPos

(** val cRealLtDisjunctEpsilon :
    cReal -> cReal -> cReal -> cReal -> (cRealLt, cRealLt) sum **)

let cRealLtDisjunctEpsilon a b c d =
  let h0 =
    constructive_indefinite_ground_description_Z (fun n ->
      let s =
        qlt_le_dec
          (qmult { qnum = (Zpos (XO XH)); qden = XH }
            (qpower { qnum = (Zpos (XO XH)); qden = XH } n))
          (qminus (b.seq n) (a.seq n))
      in
      (match s with
       | Left -> Left
       | Right ->
         qlt_le_dec
           (qmult { qnum = (Zpos (XO XH)); qden = XH }
             (qpower { qnum = (Zpos (XO XH)); qden = XH } n))
           (qminus (d.seq n) (c.seq n))))
  in
  let s =
    qlt_le_dec
      (qmult { qnum = (Zpos (XO XH)); qden = XH }
        (qpower { qnum = (Zpos (XO XH)); qden = XH } h0))
      (qminus (b.seq h0) (a.seq h0))
  in
  (match s with
   | Left -> Inl h0
   | Right -> Inr h0)

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

(** val iPR_2 : positive -> RbaseSymbolsImpl.coq_R **)

let rec iPR_2 = function
| XI p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
      RbaseSymbolsImpl.coq_R1)
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0))
| XO p0 ->
  RbaseSymbolsImpl.coq_Rmult
    (RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1
      RbaseSymbolsImpl.coq_R1)
    (iPR_2 p0)
| XH ->
  RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 RbaseSymbolsImpl.coq_R1

(** val iPR : positive -> RbaseSymbolsImpl.coq_R **)

let iPR = function
| XI p0 -> RbaseSymbolsImpl.coq_Rplus RbaseSymbolsImpl.coq_R1 (iPR_2 p0)
| XO p0 -> iPR_2 p0
| XH -> RbaseSymbolsImpl.coq_R1

(** val iZR : z -> RbaseSymbolsImpl.coq_R **)

let iZR = function
| Z0 -> RbaseSymbolsImpl.coq_R0
| Zpos n -> iPR n
| Zneg n -> RbaseSymbolsImpl.coq_Ropp (iPR n)

(** val total_order_T :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> sumbool sumor **)

let total_order_T r1 r2 =
  let s =
    cRealLt_lpo_dec (RbaseSymbolsImpl.coq_Rrepr r1)
      (RbaseSymbolsImpl.coq_Rrepr r2) (fun _ -> sig_forall_dec)
  in
  (match s with
   | Inl _ -> Inleft Left
   | Inr _ ->
     let s0 =
       cRealLt_lpo_dec (RbaseSymbolsImpl.coq_Rrepr r2)
         (RbaseSymbolsImpl.coq_Rrepr r1) (fun _ -> sig_forall_dec)
     in
     (match s0 with
      | Inl _ -> Inright
      | Inr _ -> Inleft Right))

(** val req_appart_dec :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> sumbool **)

let req_appart_dec x y =
  let s = total_order_T x y in
  (match s with
   | Inleft s0 -> (match s0 with
                   | Left -> Right
                   | Right -> Left)
   | Inright -> Right)

(** val rrepr_appart_0 : RbaseSymbolsImpl.coq_R -> cReal_appart **)

let rrepr_appart_0 x =
  cRealLtDisjunctEpsilon (RbaseSymbolsImpl.coq_Rrepr x)
    (inject_Q { qnum = Z0; qden = XH }) (inject_Q { qnum = Z0; qden = XH })
    (RbaseSymbolsImpl.coq_Rrepr x)

module type RinvSig =
 sig
  val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R
 end

module RinvImpl =
 struct
  (** val coq_Rinv : RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

  let coq_Rinv x =
    match req_appart_dec x RbaseSymbolsImpl.coq_R0 with
    | Left -> RbaseSymbolsImpl.coq_R0
    | Right ->
      RbaseSymbolsImpl.coq_Rabst
        (cReal_inv (RbaseSymbolsImpl.coq_Rrepr x) (rrepr_appart_0 x))

  (** val coq_Rinv_def : __ **)

  let coq_Rinv_def =
    __
 end

(** val rdiv :
    RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R -> RbaseSymbolsImpl.coq_R **)

let rdiv r1 r2 =
  RbaseSymbolsImpl.coq_Rmult r1 (RinvImpl.coq_Rinv r2)

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

(** val idx_2d_to_1d : nat -> nat -> fin -> fin -> fin **)

let idx_2d_to_1d m n i j =
  let i' = fin2nat m i in let j' = fin2nat n j in Nat.add (Nat.mul i' n) j'

(** val idx_1d_to_2d : nat -> nat -> fin -> (fin, fin) prod **)

let idx_1d_to_2d _ n x =
  match n with
  | O -> assert false (* absurd case *)
  | S n' ->
    let row = Nat.div x (S n') in
    let col = Nat.modulo x (S n') in Pair (row, col)

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

(** val one : exp **)

let one =
  Obj.magic (REconst (RbaseSymbolsImpl.coq_R1, (String ((Ascii (True, False,
    False, False, True, True, False, False)), EmptyString))))

(** val negate : exp -> exp **)

let negate x =
  Obj.magic (REopp (Obj.magic x))

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

(** val pExp : exp -> exp **)

let pExp x =
  Obj.magic (REexp (Obj.magic x))

(** val sqrt : exp -> exp **)

let sqrt x =
  Obj.magic (REsqrt (Obj.magic x))

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

(** val mt_eps : exp **)

let mt_eps =
  Obj.magic (REconst
    ((rdiv (iZR (Zpos XH))
       (iZR (Zpos (XO (XO (XO (XO (XO (XI (XO (XI (XO (XI (XI (XO (XO (XO (XO
         (XI XH))))))))))))))))))),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, False, True, True, False, True, False, False)),
    (String ((Ascii (True, False, True, False, True, True, False, False)),
    EmptyString))))))))))

(** val mt_neginf : exp **)

let mt_neginf =
  Obj.magic (REconst
    ((RbaseSymbolsImpl.coq_Ropp
       (iZR (Z.pow (Zpos (XO (XI (XO XH)))) (Zpos (XO (XI (XI (XI XH)))))))),
    (String ((Ascii (True, False, True, True, False, True, False, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, False, True, False, False, True, True, False)),
    (String ((Ascii (True, True, False, False, True, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, False, False)),
    EmptyString))))))))))))

(** val mt_half : exp **)

let mt_half =
  Obj.magic (REconst ((rdiv (iZR (Zpos XH)) (iZR (Zpos (XO XH)))), (String
    ((Ascii (False, False, False, False, True, True, False, False)), (String
    ((Ascii (False, True, True, True, False, True, False, False)), (String
    ((Ascii (True, False, True, False, True, True, False, False)),
    EmptyString))))))))

(** val mt_sqrt_2_pi : exp **)

let mt_sqrt_2_pi =
  Obj.magic (REconst
    ((rdiv
       (iZR (Zpos (XO (XI (XI (XI (XO (XI (XI (XI (XI (XO (XO (XI (XO (XI (XO
         (XO (XI (XI (XI (XI (XO (XI (XO (XO (XO (XI (XO (XO (XO (XO (XI (XI
         (XI (XI (XI (XO (XI (XI (XO (XI (XO (XO (XO (XI (XI (XO (XI (XO (XO
         (XO (XI (XI XH))))))))))))))))))))))))))))))))))))))))))))))))))))))
       (iZR (Z.pow (Zpos (XO (XI (XO XH)))) (Zpos (XO (XO (XO (XO XH)))))))),
    (String ((Ascii (False, False, False, False, True, True, False, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (True, True, True, False, True, True, False, False)),
    (String ((Ascii (True, False, False, True, True, True, False, False)),
    (String ((Ascii (True, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, False, True, True, True, False, False)),
    (String ((Ascii (False, False, False, True, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    (String ((Ascii (True, False, True, False, True, True, False, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, False, False)),
    (String ((Ascii (False, False, False, True, True, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, False, False)),
    (String ((Ascii (False, True, False, False, True, True, False, False)),
    (String ((Ascii (False, False, False, True, True, True, False, False)),
    (String ((Ascii (False, True, True, False, True, True, False, False)),
    (String ((Ascii (True, False, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    EmptyString))))))))))))))))))))))))))))))))))))))

(** val mt_cubic : exp **)

let mt_cubic =
  Obj.magic (REconst
    ((rdiv
       (iZR (Zpos (XI (XI (XO (XI (XO (XI (XO (XI (XO (XI (XI (XI (XO (XI (XO
         XH)))))))))))))))))
       (iZR (Zpos (XO (XO (XO (XO (XO (XO (XI (XO (XO (XI (XO (XO (XO (XO (XI
         (XO (XI (XI (XI XH)))))))))))))))))))))),
    (String ((Ascii (False, False, False, False, True, True, False, False)),
    (String ((Ascii (False, True, True, True, False, True, False, False)),
    (String ((Ascii (False, False, False, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    (String ((Ascii (False, False, True, False, True, True, False, False)),
    (String ((Ascii (True, True, True, False, True, True, False, False)),
    (String ((Ascii (True, False, False, False, True, True, False, False)),
    (String ((Ascii (True, False, True, False, True, True, False, False)),
    EmptyString))))))))))))))))))

(** val mt_attn_scale : exp **)

let mt_attn_scale =
  div0 one
    (sqrt
      (Obj.magic (REconst ((iZR (Zpos (XO (XO (XO (XO XH)))))), (String
        ((Ascii (True, False, False, False, True, True, False, False)),
        (String ((Ascii (False, True, True, False, True, True, False,
        False)), EmptyString))))))))

(** val mt_tanh_r : exp -> exp **)

let mt_tanh_r x =
  div0 (sub0 (pExp x) (pExp (negate x))) (add0 (pExp x) (pExp (negate x)))

(** val mt_gelu_r : exp -> exp **)

let mt_gelu_r x =
  mul0 (mul0 mt_half x)
    (add0 one
      (mt_tanh_r
        (mul0 mt_sqrt_2_pi (add0 x (mul0 mt_cubic (mul0 (mul0 x x) x))))))

(** val mt_ln_cell : exp -> exp -> exp -> exp -> exp -> exp **)

let mt_ln_cell x mean var g b =
  add0 (mul0 g (div0 (sub0 x mean) (sqrt (add0 var mt_eps)))) b

(** val t1 : data **)

let t1 =
  Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)

(** val t2 : data **)

let t2 =
  Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)))

(** val t3 : data **)

let t3 =
  Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)))))

(** val t4H : data **)

let t4H =
  Ary ((S O), (fle_self (S O)), (Ary ((S (S O)), (fle_self (S (S O))), (Ary
    ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))),
    Num)))))))

(** val t4S : data **)

let t4S =
  Ary ((S O), (fle_self (S O)), (Ary ((S (S O)), (fle_self (S (S O))), (Ary
    ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S (S
    (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num)))))))

(** val t2H : data **)

let t2H =
  Ary ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    (Ary ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), Num)))

(** val t3O : data **)

let t3O =
  Ary ((S O), (fle_self (S O)), (Ary ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S (S
    (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num)))))

(** val i0_1 : fin **)

let i0_1 =
  nat2fin (S O) O

(** val tok_tab : exp **)

let tok_tab =
  vrd (Ary ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)))) (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))

(** val pos_tab : exp **)

let pos_tab =
  vrd (Ary ((S (S (S (S (S (S (S (S O)))))))),
    (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)))) (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))

(** val l1_ln1_g : exp **)

let l1_ln1_g =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l1_ln1_b : exp **)

let l1_ln1_b =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l1_ln2_g : exp **)

let l1_ln2_g =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l1_ln2_b : exp **)

let l1_ln2_b =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l1_wq : exp **)

let l1_wq =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), EmptyString))))))))))

(** val l1_wk : exp **)

let l1_wk =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), EmptyString))))))))))

(** val l1_wv : exp **)

let l1_wv =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), EmptyString))))))))))

(** val l1_wo : exp **)

let l1_wo =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), EmptyString))))))))))

(** val l1_w1 : exp **)

let l1_w1 =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))

(** val l1_w2 : exp **)

let l1_w2 =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))

(** val l2_ln1_g : exp **)

let l2_ln1_g =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l2_ln1_b : exp **)

let l2_ln1_b =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l2_ln2_g : exp **)

let l2_ln2_g =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l2_ln2_b : exp **)

let l2_ln2_b =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))))))

(** val l2_wq : exp **)

let l2_wq =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), EmptyString))))))))))

(** val l2_wk : exp **)

let l2_wk =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), EmptyString))))))))))

(** val l2_wv : exp **)

let l2_wv =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), EmptyString))))))))))

(** val l2_wo : exp **)

let l2_wo =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), EmptyString))))))))))

(** val l2_w1 : exp **)

let l2_w1 =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))))

(** val l2_w2 : exp **)

let l2_w2 =
  vrd t2 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))))

(** val lnf_g : exp **)

let lnf_g =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))))

(** val lnf_b : exp **)

let lnf_b =
  vrd t1 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, True, False, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))

(** val whead : exp **)

let whead =
  vrd t2H (String ((Ascii (True, True, True, False, True, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, False, True, True,
    False)), EmptyString))))))))))

(** val l1_w : acc **)

let l1_w =
  vwt t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))

(** val l1_r : exp **)

let l1_r =
  vrd t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))

(** val l2_w : acc **)

let l2_w =
  vwt t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))

(** val l2_r : exp **)

let l2_r =
  vrd t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))

(** val l3_w : acc **)

let l3_w =
  vwt t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), EmptyString))))

(** val l3_r : exp **)

let l3_r =
  vrd t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, False,
    False)), EmptyString))))

(** val l4_w : acc **)

let l4_w =
  vwt t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), EmptyString))))

(** val l4_r : exp **)

let l4_r =
  vrd t3 (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, False,
    False)), EmptyString))))

(** val bln1_w : acc **)

let bln1_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))

(** val bln1_r : exp **)

let bln1_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))

(** val bmha_w : acc **)

let bmha_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))

(** val bmha_r : exp **)

let bmha_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, False, True, False, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), EmptyString))))))))

(** val br1_w : acc **)

let br1_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))

(** val br1_r : exp **)

let br1_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))

(** val bln2_w : acc **)

let bln2_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))

(** val bln2_r : exp **)

let bln2_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, True, False, True, True,
    False)), (String ((Ascii (False, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))

(** val btf1_w : acc **)

let btf1_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))

(** val btf1_r : exp **)

let btf1_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, False,
    False)), EmptyString))))))))

(** val btg_w : acc **)

let btg_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))

(** val btg_r : exp **)

let btg_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))

(** val btf2_w : acc **)

let btf2_w =
  vwt t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))

(** val btf2_r : exp **)

let btf2_r =
  vrd t3 (String ((Ascii (False, True, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, False,
    False)), EmptyString))))))))

(** val mtq_w : acc **)

let mtq_w =
  vwt t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), EmptyString))))))

(** val mtq_r : exp **)

let mtq_r =
  vrd t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), EmptyString))))))

(** val mtk_w : acc **)

let mtk_w =
  vwt t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), EmptyString))))))

(** val mtk_r : exp **)

let mtk_r =
  vrd t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), EmptyString))))))

(** val mtv_w : acc **)

let mtv_w =
  vwt t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), EmptyString))))))

(** val mtv_r : exp **)

let mtv_r =
  vrd t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), EmptyString))))))

(** val mtmg_w : acc **)

let mtmg_w =
  vwt t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))

(** val mtmg_r : exp **)

let mtmg_r =
  vrd t3 (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (True, True, True, False, False, True, True,
    False)), EmptyString))))))))

(** val mtqs_w : acc **)

let mtqs_w =
  vwt t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val mtqs_r : exp **)

let mtqs_r =
  vrd t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val mtks_w : acc **)

let mtks_w =
  vwt t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val mtks_r : exp **)

let mtks_r =
  vrd t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, True, False, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val mtvs_w : acc **)

let mtvs_w =
  vwt t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val mtvs_r : exp **)

let mtvs_r =
  vrd t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, True, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), EmptyString))))))))

(** val mtatt_w : acc **)

let mtatt_w =
  vwt t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))

(** val mtatt_r : exp **)

let mtatt_r =
  vrd t4H (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, False, False, False, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))

(** val mtscore_w : acc **)

let mtscore_w =
  vwt t4S (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), EmptyString))))))))))))))

(** val mtscore_r : exp **)

let mtscore_r =
  vrd t4S (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, True, True, True,
    False)), (String ((Ascii (True, True, False, False, False, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, False, True, True,
    False)), EmptyString))))))))))))))

(** val mtprob_w : acc **)

let mtprob_w =
  vwt t4S (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))

(** val mtprob_r : exp **)

let mtprob_r =
  vrd t4S (String ((Ascii (True, False, True, True, False, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (False, True, False, False, True, True, True,
    False)), (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (False, True, False, False, False, True, True,
    False)), EmptyString))))))))))))

(** val output_w : acc **)

let output_w =
  vwt t3O (String ((Ascii (True, True, True, True, False, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, False, False, True, True, True,
    False)), (String ((Ascii (True, False, True, False, True, True, True,
    False)), (String ((Ascii (False, False, True, False, True, True, True,
    False)), EmptyString))))))))))))

(** val mt_tok : nat -> fin **)

let mt_tok i =
  nat2fin (S (S (S (S (S (S (S (S O)))))))) i

(** val mt_embed_pos_comm : acc -> fin -> fin -> comm **)

let mt_embed_pos_comm out p tk =
  Seqfor ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fun j -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S O)))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))),
         Num))
         (idxAcc (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
           (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S O)))))))))))))))))))))))))))))))),
           (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))),
           Num)))) out i0_1)
         p)
       j),
    (add0
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
        (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num)) tok_tab tk)
        j)
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
        (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num)) pos_tab p)
        j)))))))

(** val mt_embed_comm : comm **)

let mt_embed_comm =
  Seq (Pair ((mt_embed_pos_comm l1_w (mt_tok O) (mt_tok (S (S (S O))))), (Seq
    (Pair ((mt_embed_pos_comm l1_w (mt_tok (S O)) (mt_tok (S O))), (Seq (Pair
    ((mt_embed_pos_comm l1_w (mt_tok (S (S O))) (mt_tok (S (S (S (S O)))))),
    (Seq (Pair
    ((mt_embed_pos_comm l1_w (mt_tok (S (S (S O)))) (mt_tok (S O))), (Seq
    (Pair
    ((mt_embed_pos_comm l1_w (mt_tok (S (S (S (S O)))))
       (mt_tok (S (S (S (S (S O))))))),
    (Seq (Pair
    ((mt_embed_pos_comm l1_w (mt_tok (S (S (S (S (S O))))))
       (mt_tok (S (S O)))),
    (Seq (Pair
    ((mt_embed_pos_comm l1_w (mt_tok (S (S (S (S (S (S O)))))))
       (mt_tok (S (S (S (S (S (S O)))))))),
    (mt_embed_pos_comm l1_w (mt_tok (S (S (S (S (S (S (S O)))))))) (mt_tok O))))))))))))))))))))))

(** val mt_ln_row_comm : exp -> exp -> exp -> acc -> comm **)

let mt_ln_row_comm x g b out =
  Loopacc (Num, (fun t4 ->
    let w1 = vwt Num t4 in
    let v1 = vrd Num t4 in
    Seq (Pair ((Assign (Num, (Pair (w1, zero)))), (Seq (Pair ((Seqfor ((S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))))))), (fun j -> Assign
    (Num, (Pair (w1,
    (add0
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num x
        j)
      v1))))))),
    (Loopacc (Num, (fun t5 ->
    let w2 = vwt Num t5 in
    let v2 = vrd Num t5 in
    Seq (Pair ((Assign (Num, (Pair (w2, zero)))), (Seq (Pair ((Seqfor ((S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))))))))))))))))))), (fun j -> Assign
    (Num, (Pair (w2,
    (add0
      (mul0
        (sub0
          (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) Num x j)
          (div_n v1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))))
        (sub0
          (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))) Num x j)
          (div_n v1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O)))))))))))))))))))))))))))))))))))
      v2))))))),
    (Seqfor ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fun j -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
       out j),
    (mt_ln_cell
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num x
        j)
      (div_n v1 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (div_n v2 (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))))
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num g
        j)
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num b
        j)))))))))))))))))))))))

(** val mt_layernorm_par_comm : exp -> exp -> exp -> acc -> comm **)

let mt_layernorm_par_comm x g b out =
  Seqfor ((S O), (fun bb -> Parfor ((S (S (S (S (S (S (S (S O)))))))), (Ary
    ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)),
    (idxAcc (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
      (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S O)))))))))))))))))))))))))))))))),
      (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
      Num)))) out bb),
    (fun ss o ->
    mt_ln_row_comm
      (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))),
        Num))
        (idx (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num)))) x bb)
        ss)
      g b o))))

(** val mt_bmm_row_par_comm : nat -> nat -> exp -> exp -> acc -> comm **)

let mt_bmm_row_par_comm n p x w out =
  Parfor ((S (S (S (S (S (S (S (S O)))))))), (Ary (p, (fle_self p), Num)),
    out, (fun ss o -> Seqfor (p, (fun j -> Loopacc (Num, (fun tmp ->
    let wa = vwt Num tmp in
    let va = vrd Num tmp in
    Seq (Pair ((Assign (Num, (Pair (wa, zero)))), (Seq (Pair ((Seqfor (n,
    (fun k -> Assign (Num, (Pair (wa,
    (add0
      (mul0
        (idx n Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary (n, (fle_self n), Num))
            x ss)
          k)
        (idx p Num (idx n (Ary (p, (fle_self p), Num)) w k) j))
      va))))))),
    (Assign (Num, (Pair ((idxAcc p Num o j), va)))))))))))))))

(** val mt_bmm_par_comm : nat -> nat -> exp -> exp -> acc -> comm **)

let mt_bmm_par_comm n p x w out =
  Seqfor ((S O), (fun bb ->
    mt_bmm_row_par_comm n p
      (idx (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary (n, (fle_self n),
        Num)))) x bb)
      w
      (idxAcc (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary (p, (fle_self p),
        Num)))) out bb)))

(** val mt_splitheads_comm : exp -> acc -> comm **)

let mt_splitheads_comm x out =
  Seqfor ((S O), (fun bb -> Seqfor ((S (S O)), (fun hh -> Seqfor ((S (S (S (S
    (S (S (S (S O)))))))), (fun ss -> Seqfor ((S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S O)))))))))))))))), (fun dd -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S O)))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))),
         Num))
         (idxAcc (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
           (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
           (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))),
           Num))))
           (idxAcc (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S
             (S (S (S (S (S (S O)))))))),
             (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
             (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
               O))))))))))))))))),
             Num)))))) out bb)
           hh)
         ss)
       dd),
    (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
      (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))))))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))))))))))))))))))),
        Num))
        (idx (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S (S (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num)))) x bb)
        ss)
      (idx_2d_to_1d (S (S O)) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O)))))))))))))))) hh dd)))))))))))))

(** val mt_mergeheads_comm : exp -> acc -> comm **)

let mt_mergeheads_comm x out =
  Seqfor ((S O), (fun bb -> Seqfor ((S (S (S (S (S (S (S (S O)))))))),
    (fun ss -> Seqfor ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))), (fun xx -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
         (S (S O)))))))))))))))))))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))))))))))))))))))),
         Num))
         (idxAcc (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
           (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
           (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           (S (S (S (S (S O)))))))))))))))))))))))))))))))),
           (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
             (S (S (S (S (S (S (S (S (S (S (S (S (S
             O))))))))))))))))))))))))))))))))),
           Num)))) out bb)
         ss)
       xx),
    (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))
      Num
      (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S O)))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))),
        Num))
        (idx (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))),
          Num))))
          (idx (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S
            (S (S (S (S O)))))))),
            (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))),
            Num)))))) x bb)
          (fst
            (idx_1d_to_2d (S (S O)) (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S O)))))))))))))))) xx)))
        ss)
      (snd
        (idx_1d_to_2d (S (S O)) (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S O)))))))))))))))) xx))))))))))))

(** val mt_attn_head_comm :
    exp -> exp -> exp -> exp -> exp -> acc -> acc -> acc -> comm **)

let mt_attn_head_comm q0 k v score_r prob_r score_a prob_a out =
  Seqfor ((S (S (S (S (S (S (S (S O)))))))), (fun i -> Seq (Pair ((Seqfor ((S
    (S (S (S (S (S (S (S O)))))))), (fun j -> If ((BLeb
    ((fin2nat (S (S (S (S (S (S (S (S O)))))))) j),
    (fin2nat (S (S (S (S (S (S (S (S O)))))))) i))), (Pair ((Loopacc (Num,
    (fun tmp ->
    let wa = vwt Num tmp in
    let va = vrd Num tmp in
    Seq (Pair ((Assign (Num, (Pair (wa, zero)))), (Seq (Pair ((Seqfor ((S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))), (fun kk ->
    Assign (Num, (Pair (wa,
    (add0
      (mul0
        (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S O)))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))),
            Num)) q0 i)
          kk)
        (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S O)))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))),
            Num)) k j)
          kk))
      va))))))),
    (Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S O)))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num))
         score_a i)
       j),
    (mul0 mt_attn_scale va))))))))))))), (Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S O)))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num))
         score_a i)
       j),
    mt_neginf)))))))))), (Seq (Pair ((Loopacc (Num, (fun tmp ->
    let wa = vwt Num tmp in
    let va = vrd Num tmp in
    Seq (Pair ((Assign (Num, (Pair (wa, zero)))), (Seq (Pair ((Seqfor ((S (S
    (S (S (S (S (S (S O)))))))), (fun j -> Assign (Num, (Pair (wa,
    (add0
      (pExp
        (idx (S (S (S (S (S (S (S (S O)))))))) Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
            (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num))
            score_r i)
          j))
      va))))))),
    (Seqfor ((S (S (S (S (S (S (S (S O)))))))), (fun j -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S O)))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num))
         prob_a i)
       j),
    (div0
      (pExp
        (idx (S (S (S (S (S (S (S (S O)))))))) Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
            (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num))
            score_r i)
          j))
      va))))))))))))))),
    (Seqfor ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))), (fun j -> Loopacc (Num, (fun tmp ->
    let wa = vwt Num tmp in
    let va = vrd Num tmp in
    Seq (Pair ((Assign (Num, (Pair (wa, zero)))), (Seq (Pair ((Seqfor ((S (S
    (S (S (S (S (S (S O)))))))), (fun l -> Assign (Num, (Pair (wa,
    (add0
      (mul0
        (idx (S (S (S (S (S (S (S (S O)))))))) Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
            (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), Num))
            prob_r i)
          l)
        (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O)))))))))))))))) Num
          (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S O)))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))),
            Num)) v l)
          j))
      va))))))),
    (Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))) Num
       (idxAcc (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S
         (S (S (S (S (S (S (S (S (S O)))))))))))))))),
         (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
           O))))))))))))))))),
         Num)) out i)
       j),
    va)))))))))))))))))))))

(** val mt_attnheads_par_comm : exp -> exp -> exp -> acc -> comm **)

let mt_attnheads_par_comm qs ks vs out =
  Seqfor ((S O), (fun bb -> Parfor ((S (S O)), (Ary ((S (S (S (S (S (S (S (S
    O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      O))))))))))))))))),
    Num)))),
    (idxAcc (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S (S
      (S (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary
      ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
      (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        O))))))))))))))))),
      Num)))))) out bb),
    (fun hh oh ->
    mt_attn_head_comm
      (idx (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))),
        Num))))
        (idx (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S
          (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))),
          Num)))))) qs bb)
        hh)
      (idx (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))),
        Num))))
        (idx (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S
          (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))),
          Num)))))) ks bb)
        hh)
      (idx (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
        (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          O))))))))))))))))),
        Num))))
        (idx (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S
          (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))),
          Num)))))) vs bb)
        hh)
      (idx (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
        Num))))
        (idx (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S
          (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
          Num)))))) mtscore_r bb)
        hh)
      (idx (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
        Num))))
        (idx (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S (S
          (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
          Num)))))) mtprob_r bb)
        hh)
      (idxAcc (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
        Num))))
        (idxAcc (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S
          (S (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
          Num)))))) mtscore_w bb)
        hh)
      (idxAcc (S (S O)) (Ary ((S (S (S (S (S (S (S (S O)))))))),
        (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
        (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
        Num))))
        (idxAcc (S O) (Ary ((S (S O)), (fle_self (S (S O))), (Ary ((S (S (S
          (S (S (S (S (S O)))))))),
          (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S
          (S (S (S O)))))))), (fle_self (S (S (S (S (S (S (S (S O))))))))),
          Num)))))) mtprob_w bb)
        hh)
      oh))))

(** val mt_gelu3d_par_comm : exp -> acc -> comm **)

let mt_gelu3d_par_comm x out =
  Seqfor ((S O), (fun bb -> Parfor ((S (S (S (S (S (S (S (S O)))))))), (Ary
    ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)),
    (idxAcc (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
      (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S O)))))))))))))))))))))))))))))))),
      (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
      Num)))) out bb),
    (fun ss o -> Seqfor ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))), (fun j -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
       o j),
    (mt_gelu_r
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
        (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num))
          (idx (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
            (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))))),
            Num)))) x bb)
          ss)
        j)))))))))))

(** val mt_add3d_par_comm : exp -> exp -> acc -> comm **)

let mt_add3d_par_comm x y out =
  Seqfor ((S O), (fun bb -> Parfor ((S (S (S (S (S (S (S (S O)))))))), (Ary
    ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
    (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
    Num)),
    (idxAcc (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
      (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S O)))))))))))))))))))))))))))))))),
      (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S (S (S O))))))))))))))))))))))))))))))))),
      Num)))) out bb),
    (fun ss o -> Seqfor ((S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
    O)))))))))))))))))))))))))))))))), (fun j -> Assign (Num, (Pair
    ((idxAcc (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
       o j),
    (add0
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
        (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num))
          (idx (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
            (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))))),
            Num)))) x bb)
          ss)
        j)
      (idx (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
        (S (S (S (S (S (S (S (S (S (S O)))))))))))))))))))))))))))))))) Num
        (idx (S (S (S (S (S (S (S (S O)))))))) (Ary ((S (S (S (S (S (S (S (S
          (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
          (S (S O)))))))))))))))))))))))))))))))),
          (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S
            O))))))))))))))))))))))))))))))))),
          Num))
          (idx (S O) (Ary ((S (S (S (S (S (S (S (S O)))))))),
            (fle_self (S (S (S (S (S (S (S (S O))))))))), (Ary ((S (S (S (S
            (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
            (S (S (S (S (S (S O)))))))))))))))))))))))))))))))),
            (fle_self (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              (S (S (S (S (S (S (S (S (S (S (S (S (S (S
              O))))))))))))))))))))))))))))))))),
            Num)))) y bb)
          ss)
        j)))))))))))

(** val mt_block_par_comm :
    exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp -> exp
    -> acc -> comm **)

let mt_block_par_comm x ln1_g ln1_b ln2_g ln2_b wq wk wv wo w1 w2 out =
  Seq (Pair ((mt_layernorm_par_comm x ln1_g ln1_b bln1_w), (Seq (Pair
    ((mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) bln1_r wq mtq_w),
    (Seq (Pair ((mt_splitheads_comm mtq_r mtqs_w), (Seq (Pair
    ((mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) bln1_r wk mtk_w),
    (Seq (Pair ((mt_splitheads_comm mtk_r mtks_w), (Seq (Pair
    ((mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) bln1_r wv mtv_w),
    (Seq (Pair ((mt_splitheads_comm mtv_r mtvs_w), (Seq (Pair
    ((mt_attnheads_par_comm mtqs_r mtks_r mtvs_r mtatt_w), (Seq (Pair
    ((mt_mergeheads_comm mtatt_r mtmg_w), (Seq (Pair
    ((mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) mtmg_r wo bmha_w),
    (Seq (Pair ((mt_add3d_par_comm x bmha_r br1_w), (Seq (Pair
    ((mt_layernorm_par_comm br1_r ln2_g ln2_b bln2_w), (Seq (Pair
    ((mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) bln2_r w1 btf1_w),
    (Seq (Pair ((mt_gelu3d_par_comm btf1_r btg_w), (Seq (Pair
    ((mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S (S (S (S (S
       (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
       O)))))))))))))))))))))))))))))))) btg_r w2 btf2_w),
    (mt_add3d_par_comm br1_r btf2_r out)))))))))))))))))))))))))))))))))))))))))))))

(** val minitransformer_ast_par_comm : comm **)

let minitransformer_ast_par_comm =
  Seq (Pair (mt_embed_comm, (Seq (Pair
    ((mt_block_par_comm l1_r l1_ln1_g l1_ln1_b l1_ln2_g l1_ln2_b l1_wq l1_wk
       l1_wv l1_wo l1_w1 l1_w2 l2_w),
    (Seq (Pair
    ((mt_block_par_comm l2_r l2_ln1_g l2_ln1_b l2_ln2_g l2_ln2_b l2_wq l2_wk
       l2_wv l2_wo l2_w1 l2_w2 l3_w),
    (Seq (Pair ((mt_layernorm_par_comm l3_r lnf_g lnf_b l4_w),
    (mt_bmm_par_comm (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S (S
      (S (S (S (S (S (S (S (S (S (S (S (S (S
      O)))))))))))))))))))))))))))))))) (S (S (S (S (S (S (S (S O))))))))
      l4_r whead output_w))))))))))))
