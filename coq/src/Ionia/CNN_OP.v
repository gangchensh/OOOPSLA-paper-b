From Stdlib Require Import Reals String Nat List Bool Arith Lra.
From Stdlib Require Import Extraction.
Require Export Ionia.CNN_Defs.
Import ListNotations.
Set Implicit Arguments.

(* ======================================================================== *)

(* ======================= Helper Functions & Lemmas for Safe Indexing ======================= *)

(* Explicit wrapper around nat2fin to avoid implicit-argument issues
   with Set Implicit Arguments. *)
Definition mkfin {n} (i : nat) (H : i < n) : fin n := nat2fin H.
Arguments mkfin n i H : clear implicits.

Lemma fin_plus_k_lt : forall m k (i : fin (m - k)), fin2nat i + k < m.
Proof.
  intros m k i.
  destruct (le_lt_dec k m).
  - assert (H : fin2nat i < m - k) by apply (fin_proof i). lia.
  - assert (H_lt : fin2nat i < m - k) by apply (fin_proof i).
    assert (H0 : m - k = 0) by lia.
    lia.
Qed.

Lemma fin_mul_add_lt_div : forall m k (i : fin (m / k)) (j : fin k), fin2nat i * k + fin2nat j < m.
Proof.
  intros m k i j.
  destruct k.
  - exfalso. assert (H_lt : fin2nat j < 0) by apply (fin_proof j). lia.
  - assert (Hi : fin2nat i < m / S k) by apply (fin_proof i).
    assert (Hj : fin2nat j < S k) by apply (fin_proof j).
    assert (H_le : S k * (m / S k) <= m).
    { pose proof (Nat.div_mod_eq m (S k)) as H_eq. lia. }
    assert (H_ik : fin2nat i * S k <= (m / S k - 1) * S k).
    { apply Nat.mul_le_mono_r. lia. }
    assert (H_le2 : (m / S k - 1) * S k + S k <= m / S k * S k).
    { destruct (m / S k). lia. simpl. lia. }
    lia.
Qed.
Arguments fin_mul_add_lt_div m k i j : clear implicits.

Lemma fin_ge_sub_lt : forall n1 n2 (c : fin (n1 + n2)), ~ (fin2nat c < n1) -> fin2nat c - n1 < n2.
Proof.
  intros n1 n2 c H_ge.
  assert (H_lt : fin2nat c < n1 + n2) by apply (fin_proof c).
  apply Nat.nlt_ge in H_ge.
  lia.
Qed.

Lemma fin_div_lt : forall k m (i : fin (k * m)), 0 < k -> fin2nat i / k < m.
Proof.
  intros k m i H_k.
  assert (H_lt : fin2nat i < k * m) by apply (fin_proof i).
  apply Nat.div_lt_upper_bound; lia.
Qed.

Lemma fin_add_lt_l : forall n m (i : fin n) (j : fin m), fin2nat i + fin2nat j < n + m.
Proof.
  intros n m i j.
  assert (Hi : fin2nat i < n) by apply (fin_proof i).
  assert (Hj : fin2nat j < m) by apply (fin_proof j).
  lia.
Qed.
Arguments fin_add_lt_l n m i j : clear implicits.

Lemma fin_add_lt_conv : forall m n (i0 : fin (m + n - 1)) (i1 : fin n), fin2nat i0 + fin2nat i1 < 2 * (n - 1) + m.
Proof.
  intros m n i0 i1.
  assert (Hi0 : fin2nat i0 < m + n - 1) by apply (fin_proof i0).
  assert (Hi1 : fin2nat i1 < n) by apply (fin_proof i1).
  lia.
Qed.
Arguments fin_add_lt_conv m n i0 i1 : clear implicits.

Lemma fin_add_lt_conv2 : forall m n (i0 : fin n) (i1 : fin m), fin2nat i0 + fin2nat i1 < m + n - 1.
Proof.
  intros m n i0 i1.
  assert (Hi0 : fin2nat i0 < n) by apply (fin_proof i0).
  assert (Hi1 : fin2nat i1 < m) by apply (fin_proof i1).
  lia.
Qed.
Arguments fin_add_lt_conv2 m n i0 i1 : clear implicits.

Lemma fin_div_lt' : forall k m (i : fin (k * m)), fin2nat i / k < m.
Proof.
  intros k m i.
  destruct k.
  - exfalso. assert (H_lt : fin2nat i < 0) by apply (fin_proof i). lia.
  - apply fin_div_lt. lia.
Qed.

Lemma fin_minus_lt : forall n (i : fin n), n - 1 - fin2nat i < n.
Proof.
  intros n i.
  assert (H_lt : fin2nat i < n) by apply (fin_proof i).
  lia.
Qed.
Arguments fin_minus_lt n i : clear implicits.

(* For Interpolation: if i < n + (n-1)*(s-1) = n*s - s + 1 and s > 0, then i/s < n.
   In practice Interpolation uses s=2 (hardcoded mod 2 / div 2). *)
Lemma fin_interp_div_lt : forall m s (i : fin (m + (m-1)*(s-1))),
  s > 0 -> Nat.div (fin2nat i) s < m.
Proof.
  intros m s i Hs.
  assert (Hi : fin2nat i < m + (m - 1) * (s - 1)) by apply (fin_proof i).
  assert (Hbound : m + (m - 1) * (s - 1) <= m * s).
  { destruct m; destruct s; simpl; try lia. }
  assert (Hlt : fin2nat i < m * s) by lia.
  apply Nat.div_lt_upper_bound; lia.
Qed.
Arguments fin_interp_div_lt m s i Hs : clear implicits.

(* For ConvTranspose: i >= offset -> i - offset < n *)
Lemma fin_ge_sub_lt' : forall n offset (i : fin n),
  offset < n -> ~ (fin2nat i < offset) -> fin2nat i - offset < n.
Proof.
  intros n offset i Hoffset Hge.
  assert (Hi : fin2nat i < n) by apply (fin_proof i).
  lia.
Qed.
Arguments fin_ge_sub_lt' n offset i Hoffset Hge : clear implicits.

(* ======================= End Helper Lemmas ======================= *)

Definition ReLU1d {m :nat}(input: exp(ary '{m} num)) :=
  mkvSeq (fun i:fin m => if (bexp2bool (leExp input|[i] zero)) then zero else input|[i]).

Open Scope nat_scope.
Definition ReLU2d {m1 m2:nat}(input: exp(ary '{m1} (ary '{m2} num)))
  : exp(ary '{m1} (ary '{m2} num)) :=
  mkvSeq (fun i0:fin m1 => mkvSeq (fun i1:fin m2 => 
    if (bexp2bool (leExp input|[i0]|[i1] zero)) then zero else input|[i0]|[i1])).

Definition ReLU3d {m1 m2 filernum:nat}(input: exp(ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp(ary '{filernum} (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun num: fin filernum => mkvSeq (fun i0:fin m1 => mkvSeq (fun i1:fin m2 => 
    if (bexp2bool (leExp input|[num]|[i0]|[i1] zero)) then zero else input|[num]|[i0]|[i1]))).

Definition ReLU4d {batch m1 m2 filernum:nat}(input: exp(ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp(ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin m1 => mkvSeq (fun i1:fin m2 => 
      if (bexp2bool (leExp input|[b]|[num]|[i0]|[i1] zero)) then zero else input|[b]|[num]|[i0]|[i1])))).

Definition Softmax1d {m:nat}(input: exp(ary '{m} num))
  : exp(ary '{m} num) :=
  tlet s := sum (mkvSeq (fun i:fin m => pExp input|[i])) in
    mkvSeq (fun j:fin m => div (pExp input|[j]) s).

Definition Softmax2d {batch m:nat}(input: exp(ary '{batch} (ary '{m} num)))
  : exp(ary '{batch} (ary '{m} num)) :=
  tlet s := mkvSeq (fun b:fin batch => 
    sum (mkvSeq (fun i:fin m => pExp input|[b]|[i]))) in 
  mkvSeq (fun b:fin batch => mkvSeq (fun j:fin m => 
    div (pExp input|[b]|[j]) s|[b])).

Definition Softmax3d {m1 m2 filernum:nat}(input: exp(ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp(ary '{filernum} (ary '{m1} (ary '{m2} num))) :=
  tlet s := sum (mkvSeq (fun i0:fin filernum => 
    sum (mkvSeq (fun j0:fin m1 => sum (mkvSeq (fun k0:fin m2 => 
      pExp input|[i0]|[j0]|[k0])))))) in
  mkvSeq (fun i1:fin filernum => mkvSeq (fun j1:fin m1 => mkvSeq (fun k1:fin m2 =>
    div (pExp input|[i1]|[j1]|[k1]) s))).

Definition Sigmoid2d {m1 m2 : nat}
  (input: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => mkvSeq (fun j: fin m2 =>
    div one (add one (pExp (negate input|[i]|[j]))))).

Definition Sigmoid4d {batch channel m1 m2 : nat}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun c: fin channel =>
    mkvSeq (fun i:fin m1 => mkvSeq (fun j: fin m2 =>
      div one (add one (pExp (negate input|[b]|[c]|[i]|[j]))))))).

Definition Tanh2d {ml m2 : nat }
  (input:exp(ary '{ml} (ary '{m2} num))) :=
  mkvSeq (fun i => mkvSeq (fun j =>
    div (sub (pExp input|[i]|[j])(pExp (negate input|[i]|[j])))
      (add (pExp input|[i]|[j])(pExp (negate input|[i]|[j]))))).

Definition Tanh4d {batch channel ml m2 : nat }
  (input:exp(ary '{batch} (ary '{channel} (ary '{ml} (ary '{m2} num))))) :=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i => mkvSeq (fun j =>
    div (sub (pExp input|[b]|[c]|[i]|[j])(pExp (negate input|[b]|[c]|[i]|[j])))
        (add (pExp input|[b]|[c]|[i]|[j])(pExp (negate input|[b]|[c]|[i]|[j]))))))).

Definition LeakyReLU4d {batch channel m1 m2 : nat}(negative_slope :exp num)
  (input:exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))):=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i=>
    mkvSeq (fun j => if (bexp2bool (gtExp input|[b]|[c]|[i]|[j] zero)) 
      then input|[b]|[c]|[i]|[j] else mul negative_slope input|[b]|[c]|[i]|[j])))).

Definition Randn2d{m1 m2}(input: exp (ary '{m1} (ary '{m2} num)))
  :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j: fin m2 => rand)).

Definition Fill2d {batch m : nat}(e: exp num)
  (input: exp (ary '{batch} (ary '{m} num))) :=
  mkvSeq (fun i:fin batch => 
    mkvSeq (fun j:fin m => e)).

Definition Exp2d {m1 m2 : nat}
  (input: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => pExp input|[i]|[j])).

Definition Addc2d {m1 m2 : nat}(e: exp num)
  (input: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => add input|[i]|[j] e )).

Definition Mulc2d {m1 m2 : nat}(v: exp num)
   (input: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => mul input|[i]|[j] v)).

Definition Add2d {m1 m2 : nat}(x: exp (ary '{m1} (ary '{m2} num)))
   (y: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => add x|[i]|[j] y|[i]|[j])).

Definition Sub2d {m1 m2 : nat}(x: exp (ary '{m1} (ary '{m2} num)))
   (y: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => sub x|[i]|[j] y|[i]|[j])).

Definition Mul2d {m1 m2 : nat}(x: exp (ary '{m1} (ary '{m2} num)))
   (y: exp (ary '{m1} (ary '{m2} num))) :=
  mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => mul x|[i]|[j] y|[i]|[j])).

Definition Add3d {channel m1 m2 : nat}(x: exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
   (y: exp (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun c: fin channel => mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin m2 => add x|[c]|[i]|[j] y|[c]|[i]|[j]))).

Definition Add4d {batch channel m1 m2 : nat}
  (x: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (y: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun c: fin channel => 
    mkvSeq (fun i:fin m1 => mkvSeq (fun j:fin m2 => 
      add x|[b]|[c]|[i]|[j] y|[b]|[c]|[i]|[j])))).



Definition Padding2d {n1 n2 d} (p : nat) (e: exp (ary '{n1} (ary '{n2} d)))
  : exp (ary '{(2*p+n1)} (ary '{(2*p+n2)} d)) := 
  mkvSeq (fun i : fin (2*p + n1) => mkvSeq (fun j : fin (2*p + n2) =>
    let i_val := fin2nat i in
    let j_val := fin2nat j in
    match Nat.ltb_spec0 i_val p with
    | ReflectT _ _ => exp_default d
    | ReflectF _ H_ge_i =>
      match Nat.ltb_spec0 i_val (p+n1) with
      | ReflectT _ H_lt_i =>
        match Nat.ltb_spec0 j_val p with
        | ReflectT _ _ => exp_default d
        | ReflectF _ H_ge_j =>
          match Nat.ltb_spec0 j_val (p+n2) with
          | ReflectT _ H_lt_j =>
            let H_i := @offset_proof_concise i_val p n1 H_lt_i H_ge_i in
            let H_j := @offset_proof_concise j_val p n2 H_lt_j H_ge_j in
            e|[nat2fin H_i]|[nat2fin H_j]
          | ReflectF _ _ => exp_default d
          end
        end
      | ReflectF _ _ => exp_default d
      end
    end)).

Definition Padding3d {n1 n2 channel} (p : nat) (e: exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  : exp (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num))) := 
 mkvSeq (fun c: fin channel => Padding2d p e|[c]).

Definition Padding4d {batch n1 n2 channel} (p : nat) (e: exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{(2*p+n1)} (ary '{(2*p+n2)} num)))) := 
  mkvSeq (fun b :fin batch => Padding3d p e|[b]).

Definition Conv2d {m1 m2 n1 n2:nat}(p:nat)(s:nat) (w: exp (ary '{n1} (ary '{n2} num)))(input: exp(ary '{m1} (ary '{m2} num)))
  : exp(ary '{((m1 - n1 + 2*p)/s + 1 )} (ary '{((m2 - n2 + 2*p)/s + 1)} num)):=
  tlet pad := Padding2d p input in 
    mkvSeq (fun i0:fin ((m1 - n1 + 2*p)/s + 1) => mkvSeq (fun j0:fin ((m2 - n2 + 2*p)/s + 1) =>
      sum (mkvSeq (fun i1:fin n1 => sum (mkvSeq ( fun j1: fin n2 => 
        mul (safe_idx_nat (safe_idx_nat pad (fin2nat i0 * s + fin2nat i1)) (fin2nat j0 * s + fin2nat j1)) w|[i1]|[j1])))))).

Definition Conv3d {m1 m2 n1 n2 channel filernum:nat}(p:nat)(s:nat)(bias: exp (ary '{filernum} num))
  (w: exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))(input: exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  : exp(ary '{filernum} (ary '{((m1 - n1 + 2*p)/s + 1 )} (ary '{((m2 - n2 + 2*p)/s + 1)} num))) :=
  tlet tmp := Padding3d p input in mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin ((m1 - n1 + 2*p)/s + 1) => mkvSeq (fun j0:fin ((m2 - n2 + 2*p)/s + 1) => 
      add (sum (mkvSeq (fun c:fin channel => 
        sum (mkvSeq ( fun i1: fin n1 => sum (mkvSeq (fun j1: fin n2 => 
          mul (safe_idx_nat (safe_idx_nat (tmp|[c]) (fin2nat i0 * s + fin2nat i1)) (fin2nat j0 * s + fin2nat j1)) w|[num]|[c]|[i1]|[j1]))))))) bias|[num]))).

Definition Conv4d {batch m1 m2 n1 n2 channel filernum:nat}(p:nat)(s:nat)
  (bias: exp (ary '{filernum} num))(w: exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp(ary '{batch} (ary '{filernum} (ary '{((m1 - n1 + 2*p)/s + 1 )} (ary '{((m2 - n2 + 2*p)/s + 1)} num)))):=
  tlet tmp := Padding4d p input in mkvSeq (fun b:fin batch => mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin ((m1 - n1 + 2*p)/s + 1) => mkvSeq (fun j0:fin ((m2 - n2 + 2*p)/s + 1) => 
      add (sum (mkvSeq (fun c:fin channel => 
        sum (mkvSeq ( fun i1: fin n1 => sum (mkvSeq (fun j1: fin n2 => 
          mul (safe_idx_nat (safe_idx_nat (tmp|[b]|[c]) (fin2nat i0 * s + fin2nat i1)) (fin2nat j0 * s + fin2nat j1)) w|[num]|[c]|[i1]|[j1]))))))) bias|[num])))).

Definition Avgpool2d {m1 m2:nat}(k:nat)(input: exp(ary '{m1} (ary '{m2} num)))
  : exp(ary '{(m1/k)} (ary '{(m2/k)} num)) :=
  mkvSeq (fun i0:fin (m1/k) => mkvSeq (fun i1:fin (m2/k) => div_n
    (sum (mkvSeq (fun j0:fin k => sum 
      (mkvSeq ( fun j1: fin k => input|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))(k*k))).

Definition Avgpool3d {filernum m1 m2:nat}(k:nat)(input: exp(ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp(ary '{filernum} ( ary '{(m1/k)} (ary '{(m2/k)} num))) :=
  mkvSeq (fun num: fin filernum => mkvSeq (fun i0:fin (m1/k) => mkvSeq (fun i1:fin (m2/k) => 
    div_n (sum (mkvSeq (fun j0:fin k => sum (mkvSeq ( fun j1: fin k => 
      input|[num]|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))(k*k)))).

Definition Avgpool4d {batch filernum m1 m2:nat}(k:nat)
  (input: exp(ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp(ary '{batch} (ary '{filernum} ( ary '{(m1/k)} (ary '{(m2/k)} num)))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin (m1/k) => mkvSeq (fun i1:fin (m2/k) => 
      div_n (sum (mkvSeq (fun j0:fin k => 
        sum (mkvSeq ( fun j1: fin k => 
          input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))(k*k))))).

(* Specialized convolutions for ResNet. *)
Definition Conv4d_p1_k3_s2 {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{3} (ary '{3} num)))))
  (bias: exp (ary '{outch} num))
  : exp (ary '{batch} (ary '{outch} (ary '{((m - 3 + 2 * 1) / 2 + 1)} (ary '{((m - 3 + 2 * 1) / 2 + 1)} num)))) :=
  @Conv4d batch m m 3 3 inch outch 1 (S (S O)) bias w input.

Definition Conv4d_p0_k1_s2 {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{1} (ary '{1} num)))))
  (bias: exp (ary '{outch} num))
  : exp (ary '{batch} (ary '{outch} (ary '{((m - 1 + 0) / 2 + 1)} (ary '{((m - 1 + 0) / 2 + 1)} num)))) :=
  @Conv4d batch m m 1 1 inch outch 0 (S (S O)) bias w input.


(* 7x7 convolution with padding=3, stride=2, for ImageNet ResNet stem.
   Input is m x m, output is ((m - 7 + 6)/2 + 1) x ((m - 7 + 6)/2 + 1). *)
Definition Conv4d_p3_k7_s2 {batch inch outch m}
  (input: exp (ary '{batch} (ary '{inch} (ary '{m} (ary '{m} num)))))
  (w: exp (ary '{outch} (ary '{inch} (ary '{7} (ary '{7} num)))))
  (bias: exp (ary '{outch} num))
  : exp (ary '{batch} (ary '{outch} (ary '{((m - 7 + 2 * 3) / 2 + 1)} (ary '{((m - 7 + 2 * 3) / 2 + 1)} num)))) :=
  @Conv4d batch m m 7 7 inch outch 3 (S (S O)) bias w input.

(* Global average pooling: reduce spatial dimensions to 1x1 per channel. *)
Definition GlobalAvgPool4d {batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} num)) :=
  mkvSeq (fun b: fin batch => mkvSeq (fun c: fin channel =>
    div_n (sum (mkvSeq (fun i: fin m1 => sum (mkvSeq (fun j: fin m2 =>
      input|[b]|[c]|[i]|[j]))))) (m1 * m2))).

Definition Maxpool2d {m1 m2:nat}(k:nat)(input: exp(ary '{m1} (ary '{m2} num)))
  : exp(ary '{(m1/k)} (ary '{(m2/k)} num)) :=
  mkvSeq (fun i0:fin (m1/k) => mkvSeq (fun j0:fin (m2/k) => 
    max (mkvSeq (fun i1: fin k => max (mkvSeq (fun j1: fin k => 
      input|[nat2fin (fin_mul_add_lt_div m1 k i0 i1)]|[nat2fin (fin_mul_add_lt_div m2 k j0 j1)])))))).

Definition Maxpool3d {filernum m1 m2:nat}(k:nat)(input: exp(ary '{filernum} (ary '{m1} (ary '{m2} num))))
  : exp(ary '{filernum} ( ary '{(m1/k)} (ary '{(m2/k)} num))) :=
  mkvSeq (fun num: fin filernum => mkvSeq (fun i0:fin (m1/k) => mkvSeq (fun i1:fin (m2/k) => 
    max (mkvSeq (fun j0: fin k => max (mkvSeq (fun j1: fin k => 
      input|[num]|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)]))))))).

Definition Maxpool4d {batch filernum m1 m2:nat}(k:nat)
  (input: exp(ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num)))))
  : exp(ary '{batch} (ary '{filernum} ( ary '{(m1/k)} (ary '{(m2/k)} num)))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin (m1/k) => mkvSeq (fun i1:fin (m2/k) => 
      max (mkvSeq (fun j0: fin k => max (mkvSeq (fun j1: fin k => 
        input|[b]|[num]|[nat2fin (fin_mul_add_lt_div m1 k i0 j0)]|[nat2fin (fin_mul_add_lt_div m2 k i1 j1)])))))))). 

Definition AdaptiveAvgPool4d {batch channel m1 m2} (n1 n2:nat)
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun c: fin channel => 
    mkvSeq (fun i0:fin n1 => mkvSeq (fun i1:fin n2 => 
      div_n (sum (mkvSeq (fun j0:fin m1 => 
        sum (mkvSeq ( fun j1: fin m2 => 
          input|[b]|[c]|[j0]|[j1])))))(n1*n2))))).

Definition Maxpool3d_pad {filernum m1 m2}(kersize stride padding : nat)
  (input: exp (ary '{filernum} (ary '{m1} (ary '{m2} num)))) :=
  tlet pad := Padding3d padding input in
  mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin ((m1 - kersize + 2*padding)/stride + 1) => 
      mkvSeq (fun j0:fin ((m2 - kersize + 2*padding)/stride + 1) => 
        max (mkvSeq ( fun i1: fin kersize => max (mkvSeq (fun j1: fin kersize => 
          safe_idx_nat (safe_idx_nat (pad|[num]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1)))))))).

Definition Maxpool4d_pad {batch filernum m1 m2}(kersize stride padding : nat)
  (input: exp (ary '{batch} (ary '{filernum} (ary '{m1} (ary '{m2} num))))) :=
  tlet pad := Padding4d padding input in
  mkvSeq (fun b: fin batch => mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0:fin ((m1 - kersize + 2*padding)/stride + 1) => 
      mkvSeq (fun j0:fin ((m2 - kersize + 2*padding)/stride + 1) => 
        max (mkvSeq ( fun i1: fin kersize => max (mkvSeq (fun j1: fin kersize => 
          safe_idx_nat (safe_idx_nat (pad|[b]|[num]) (fin2nat i0 * stride + fin2nat i1)) (fin2nat j0 * stride + fin2nat j1))))))))).

Definition Linear {m outnum:nat} (w: exp (ary '{outnum} (ary '{m} num)))
  (b: exp (ary '{outnum} num))(input: exp (ary '{m} num))
  : exp(ary '{outnum} num) :=
  mkvSeq (fun out:fin outnum => add (sum (mkvSeq (fun i:fin m => 
    mul input|[i] w|[out]|[i]))) b|[out]).

Definition Linear2d {batch m outnum:nat} (w: exp (ary '{outnum} (ary '{m} num)))
  (bias: exp (ary '{outnum} num))(input: exp (ary '{batch} (ary '{m} num)))
  : exp(ary '{batch} (ary '{outnum} num)) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun out:fin outnum => 
    add (sum (mkvSeq (fun i:fin m => 
      mul input|[b]|[i] w|[out]|[i]))) bias|[out])).

Definition Linear3d{c m1 m2 n} (input: exp (ary '{c} (ary '{m1} (ary '{m2} num))))
  (w: exp (ary '{n} (ary '{m2} num)))(b: exp (ary '{n} num))
  : exp (ary '{c} (ary '{m1} (ary '{n} num))):=
  mkvSeq (fun o:fin c => mkvSeq (fun i:fin m1 => 
    mkvSeq (fun j:fin n=> add (sum (mkvSeq (fun k:fin m2 => 
      mul input|[o]|[i]|[k] w|[j]|[k]))) b|[j]))).

Definition matrix_mul {m n p:nat} (ma: exp (ary '{m} (ary '{n} num)))
  (mb: exp (ary '{n} (ary '{p} num)))
  : exp(ary '{m} (ary '{p} num)) :=
  mkvSeq (fun o:fin m => mkvSeq (fun i:fin p => 
    sum (mkvSeq (fun k:fin n => 
      mul ma|[o]|[k] mb|[k]|[i])))).

Definition tensordot2d_3d {m h n s:nat} (ma: exp (ary '{m} (ary '{h} num)))
  (mb: exp (ary '{h} (ary '{n} (ary '{s} num))))
  : exp (ary '{m} (ary '{n} (ary '{s} num))) :=
  mkvSeq (fun o:fin m => mkvSeq (fun i:fin n => 
    mkvSeq (fun j:fin s => sum 
      (mkvSeq (fun k:fin h => mul ma|[o]|[k] mb|[k]|[i]|[j]))))).

Definition tensordot3d_2d {m h n s:nat} 
  (ma: exp (ary '{m} (ary '{n} (ary '{h} num))))
  (mb: exp (ary '{h} (ary '{s} num)))
  : exp (ary '{m} (ary '{n} (ary '{s} num))) :=
  mkvSeq (fun o:fin m => mkvSeq (fun i:fin n => 
    mkvSeq (fun j:fin s => sum
      (mkvSeq (fun k:fin h => mul ma|[o]|[i]|[k] mb|[k]|[j]))))).

Definition mm_mul{n d h:nat}
  (m1: exp (ary '{n} (ary '{d} num)))(w1: exp (ary '{d} (ary '{h} num)))
  (m2: exp (ary '{n} (ary '{h} num)))(w2: exp (ary '{h} (ary '{h} num)))
  (b: exp (ary '{h} num)) : exp (ary '{n} (ary '{h} num)) :=
  mkvSeq (fun i:fin n => mkvSeq (fun j:fin h => 
    add (add (sum (mkvSeq (fun k1:fin d => 
      mul m1|[i]|[k1] w1|[k1]|[j])))(sum (mkvSeq (fun k2:fin h => 
        mul m2|[i]|[k2] w2|[k2]|[j])))) b|[j])).

Definition Sum2d {m1 m2 : nat}
  (input: exp (ary '{m1} (ary '{m2} num))) :=
  sum (mkvSeq (fun i: fin m1 =>
    sum (mkvSeq (fun j: fin m2 => input|[i]|[j])))).

Definition Sum4d {batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num))))) :=
  sum (mkvSeq (fun b => sum (mkvSeq (fun c => 
    sum (mkvSeq (fun i: fin m1 =>
      sum (mkvSeq (fun j: fin m2 => input|[b]|[c]|[i]|[j])))))))).

Definition Dropout1d {n} (input:exp (ary '{n} num))
  (dropout_ratio: exp num) : exp (ary '{n} num) :=
  mkvSeq (fun i => if (bexp2bool (gtExp dropout_ratio rand)) then zero 
    else div input|[i] (sub one dropout_ratio)).

Definition Dropout2d {n1 n2} (input:exp (ary '{n1} (ary '{n2} num)))
  (dropout_ratio: exp num) :=
  mkvSeq (fun i => mkvSeq (fun j => 
    if (bexp2bool (gtExp dropout_ratio rand)) then zero 
      else div input|[i]|[j] (sub one dropout_ratio))).

Definition Dropout3d {channel n1 n2}
  (input:exp (ary '{channel} (ary '{n1} (ary '{n2} num))))
  (dropout_ratio: exp num) :=
  mkvSeq (fun c => mkvSeq (fun i => mkvSeq (fun j => 
    if (bexp2bool (gtExp dropout_ratio rand)) then zero 
      else div input|[c]|[i]|[j] (sub one dropout_ratio)))).

Definition Dropout4d {batch channel n1 n2}
  (input:exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (dropout_ratio: exp num) :=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i => 
    mkvSeq (fun j => if (bexp2bool (gtExp dropout_ratio rand)) then zero 
      else div input|[b]|[c]|[i]|[j] (sub one dropout_ratio))))).

(* Inference-time dropout: deterministic scaling by a pre-computed scale factor. *)
Definition Dropout4d_inference {batch channel n1 n2}
  (input:exp (ary '{batch} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (scale: exp num) :=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i =>
    mkvSeq (fun j => mul input|[b]|[c]|[i]|[j] scale)))).

(* 2-D analogue of [Dropout4d_inference]. *)
Definition Dropout2d_inference {n1 n2}
  (input:exp (ary '{n1} (ary '{n2} num)))
  (scale: exp num) :=
  mkvSeq (fun i => mkvSeq (fun j => mul input|[i]|[j] scale)).

Definition BatchNorm2d{batch filernum}(x:exp (ary '{batch} (ary '{filernum} num)))
  (gemma beta:exp num):=
  tlet mean := div_n (Sum2d x) (batch*filernum) in
  tlet var := div_n (sum (mkvSeq (fun i:fin batch => 
    sum (mkvSeq (fun j:fin filernum => 
      mul (sub x|[i]|[j] mean)(sub x|[i]|[j] mean))))))(batch*filernum) in
  mkvSeq (fun i:fin batch => mkvSeq (fun j:fin filernum => 
    add (mul (div (sub x|[i]|[j] mean) (sqrt var)) gemma) beta)).

Definition BatchNorm4d{batch m1 m2}(channel: nat)
  (x:exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  :=
  tlet mean := div_n (Sum4d x) (batch*channel*m1*m2) in
  tlet var := div_n (sum (mkvSeq (fun i:fin batch => 
    sum (mkvSeq (fun j:fin channel => 
      sum (mkvSeq (fun i0:fin m1 => 
        sum (mkvSeq (fun j0:fin m2 => 
          mul (sub x|[i]|[j]|[i0]|[j0] mean)
            (sub x|[i]|[j]|[i0]|[j0] mean))))))))))(batch*channel*m1*m2) in
  mkvSeq (fun i:fin batch => mkvSeq (fun j => 
    mkvSeq (fun i0=> mkvSeq (fun j0 =>
      div (sub x|[i]|[j]|[i0]|[j0] mean) (sqrt var))))).

(* Inference-mode BatchNorm4d.
   mean, var, gamma, beta are per-channel external parameters; eps is a scalar. *)
Definition BatchNorm4d_inference {batch channel m1 m2}
  (x: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  (mean var gamma beta: exp (ary '{channel} num))
  (eps: exp num)
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b: fin batch => mkvSeq (fun c: fin channel =>
    mkvSeq (fun i: fin m1 => mkvSeq (fun j: fin m2 =>
      let xmc := sub x|[b]|[c]|[i]|[j] mean|[c] in
      let norm := div xmc (sqrt (add var|[c] eps)) in
      add (mul norm gamma|[c]) beta|[c])))).

Definition Interpolation2d {m1 m2} (s : nat) (e: exp (ary '{m1} (ary '{m2} num)))
  : exp (ary '{(m1+(m1-1)*(s-1))} (ary '{(m2+(m2-1)*(s-1))} num)) := 
  mkvSeq (fun i : fin (m1+(m1-1)*(s-1)) => mkvSeq (fun j : fin (m2+(m2-1)*(s-1)) =>
    if (((i mod 2) =? 0) && ((j mod 2) =? 0)) 
    then safe_idx_nat (safe_idx_nat e (Nat.div (fin2nat i) 2)) (Nat.div (fin2nat j) 2) else exp_default num )).

Definition Interpolation3d {channel m1 m2} (s : nat) (e: exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{channel} (ary '{(m1+(m1-1)*(s-1))} (ary '{(m2+(m2-1)*(s-1))} num))) := 
  mkvSeq (fun c => mkvSeq (fun i : fin (m1+(m1-1)*(s-1)) => mkvSeq (fun j : fin (m2+(m2-1)*(s-1)) =>
    if (((i mod 2) =? 0) && ((j mod 2) =? 0)) 
    then safe_idx_nat (safe_idx_nat (e|[c]) (Nat.div (fin2nat i) 2)) (Nat.div (fin2nat j) 2) else exp_default num ))).

Definition Interpolation4d {batch channel m1 m2} (s : nat)
  (e: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{(m1+(m1-1)*(s-1))} (ary '{(m2+(m2-1)*(s-1))} num)))) := 
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i : fin (m1+(m1-1)*(s-1)) => 
    mkvSeq (fun j : fin (m2+(m2-1)*(s-1)) => if (((i mod 2) =? 0) && ((j mod 2) =? 0)) 
      then safe_idx_nat (safe_idx_nat (e|[b]|[c]) (Nat.div (fin2nat i) 2)) (Nat.div (fin2nat j) 2) else exp_default num )))).

Definition ConvTranspose2d {m1 m2 n1 n2} (p s : nat) (e: exp (ary '{m1} (ary '{m2} num)))
  (w: exp (ary '{n1} (ary '{n2} num))) : exp (ary '{((m1 + (m1-1)*(s-1) + 2*(n1-1-p) - n1 + 1))} (ary '{((m2 + (m2-1)*(s-1) + 2*(n2-1-p) - n2 + 1))} num)) := 
  tlet inter := Interpolation2d s e in
  tlet pad := mkvSeq (fun i : fin (m1 + (m1-1)*(s-1) + 2*(n1-1-p)) => 
    mkvSeq (fun j : fin (m2 + (m2-1)*(s-1) + 2*(n2-1-p)) =>
    if (i <? (n1-1-p)) && (j <? (n2-1-p)) then (exp_default num) else 
      if (((n1-1-p) <=? i) && (i <? ((n1-1-p)+n1)) && ((n2-1-p) <=? j) && (j <? ((n2-1-p)+n2))) 
        then safe_idx_nat (safe_idx_nat inter (fin2nat i - (n1 - 1 - p))) (fin2nat j - (n2 - 1 - p)) else (exp_default num))) in
  mkvSeq (fun i0 => mkvSeq (fun j0 => sum (mkvSeq (fun i1 => 
    sum (mkvSeq ( fun j1 => mul (safe_idx_nat (safe_idx_nat pad (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[i1]|[j1])))))).

Definition ConvTranspose3d {filernum channel m1 m2 n1 n2} (p s : nat)
  (bias: exp (ary '{filernum} num))(w: exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (e: exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{filernum} (ary '{((m1-1)*s - 2*p + n1)} (ary '{((m1-1)*s - 2*p + n2)} num))) := 
  tlet inter := Interpolation3d s e in
  tlet pad := mkvSeq (fun c:fin channel => mkvSeq (fun i: fin (m1 + (m1-1)*(s-1) + 2*(n1-1-p)) => 
    mkvSeq (fun j: fin (m2 + (m2-1)*(s-1) + 2*(n2-1-p)) => 
    if (i <? (n1-1-p)) && (j <? (n2-1-p)) then (exp_default num) 
    else if (((n1-1-p) <=? i) && (i <? ((n1-1-p)+n1)) && ((n2-1-p) <=? j) && (j <? ((n2-1-p)+n2))) 
        then safe_idx_nat (safe_idx_nat inter|[c] (fin2nat i - (n1 - 1 - p))) (fin2nat j - (n2 - 1 - p)) else (exp_default num)))) in
  mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0 => mkvSeq (fun j0 => 
      add (sum (mkvSeq (fun c:fin channel => 
        sum (mkvSeq ( fun i1:fin n1 => sum (mkvSeq (fun j1:fin n2 => 
          mul (safe_idx_nat (safe_idx_nat pad|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]))))))) bias|[num]))).

Definition ConvTranspose4d {batch filernum channel m1 m2 n1 n2} (p s : nat)
  (bias: exp (ary '{filernum} num))(w: exp (ary '{filernum} (ary '{channel} (ary '{n1} (ary '{n2} num)))))
  (e: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{filernum} (ary '{((m1-1)*s - 2*p + n1)} (ary '{((m1-1)*s - 2*p + n2)} num)))) := 
  tlet inter := Interpolation4d s e in
  tlet pad := mkvSeq (fun b => mkvSeq (fun c:fin channel => 
    mkvSeq (fun i: fin (m1 + (m1-1)*(s-1) + 2*(n1-1-p)) =>
      mkvSeq (fun j: fin (m2 + (m2-1)*(s-1) + 2*(n2-1-p)) => 
        if (i <? (n1-1-p)) && (j <? (n2-1-p)) then (exp_default num) 
        else if (((n1-1-p) <=? i) && (i <? ((n1-1-p)+n1)) && ((n2-1-p) <=? j) && (j <? ((n2-1-p)+n2))) 
        then safe_idx_nat (safe_idx_nat inter|[b]|[c] (fin2nat i - (n1 - 1 - p))) (fin2nat j - (n2 - 1 - p)) else (exp_default num))))) in
  mkvSeq (fun b => mkvSeq (fun num: fin filernum => 
    mkvSeq (fun i0 => mkvSeq (fun j0 => 
      add (sum (mkvSeq (fun c:fin channel => 
        sum (mkvSeq ( fun i1:fin n1 => sum (mkvSeq (fun j1:fin n2 => 
          mul (safe_idx_nat (safe_idx_nat pad|[b]|[c] (fin2nat i0 + fin2nat i1)) (fin2nat j0 + fin2nat j1)) w|[num]|[c]|[i1]|[j1]))))))) bias|[num])))).


Definition Log_Softmax2d {batch m}(input: exp (ary '{batch} (ary '{m} num))) 
  :=
  tlet sum := mkvSeq (fun b => sum 
    (mkvSeq (fun i => pExp input|[b]|[i]))) in 
  mkvSeq (fun b:fin batch => mkvSeq (fun j: fin m => 
    log (div (pExp input|[b]|[j]) sum|[b]))).

Fixpoint nth (l:list nat)(i:nat) : nat :=
  match i with
  |0 => match l with
        | [] => 0
        | x :: _ => x
        end
  |S i0 => match l with
          | [] => 0
          | _ :: l0 => nth l0 i0
          end
  end.

Definition NLLLoss2d {batch m}(input: exp (ary '{batch} (ary '{m} num)))
  (label: list nat) :=
  tlet sum := sum (mkvSeq (fun b:fin batch => 
    negate (safe_idx_nat (input|[b]) (nth label b)))) in
  div_n sum batch.

Definition BCELoss2d {batch m}(input: exp (ary '{batch} (ary '{m} num)))
  (label: exp (ary '{batch} (ary '{m} num))) :=
  mkvSeq (fun b:fin batch => (mkvSeq (fun i: fin m => 
    negate (add (mul label|[b]|[i] (log input|[b]|[i])) 
      (mul (sub one label|[b]|[i]) (log (sub one input|[b]|[i]))) )) )).

Definition BCELoss2d' {batch m}(input: exp (ary '{batch} (ary '{m} num)))
  (label: exp (ary '{batch} (ary '{m} num))) :=
  tlet sum := sum (mkvSeq (fun b:fin batch => 
    sum (mkvSeq (fun i: fin m => 
      negate (add (mul label|[b]|[i] (log input|[b]|[i]) ) 
        (mul (sub one label|[b]|[i]) (log (sub one input|[b]|[i])) ) )) ))) in
  div_n sum (batch*m).

Definition Flatten3d {channel m1 m2 : nat}
  (input: exp (ary '{channel} (ary '{m1} (ary '{m2} num)))) 
  :=
  join (join input).

Definition Flatten4d {batch channel m1 m2 : nat}
  (input: exp (ary '{batch} (ary '{channel} ( ary '{m1} (ary '{m2} num))))) 
  :=
  mkvSeq (fun i:fin batch => join (join input|[i])).

Definition Truncl1d {m : nat} (k:nat) (input:exp (ary '{m} num)) 
  :=
  mkvSeq (fun i:fin (m-k) => input|[nat2fin (fin_plus_k_lt m k i)]).

Definition Truncl2d {batch m : nat}(k:nat)
  (input: exp (ary '{batch} (ary '{m} num))) :=
  mkvSeq (fun i:fin (batch - k) => mkvSeq (fun j =>
    input|[nat2fin (fin_plus_k_lt batch k i)]|[j])).

Definition Concat4d {batch channel1 channel2 m1 m2}
  (x: exp (ary '{batch} (ary '{channel1} (ary '{m1} (ary '{m2} num)))))
  (y: exp (ary '{batch} (ary '{channel2} (ary '{m1} (ary '{m2} num))))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun c : fin (channel1 + channel2) =>
    mkvSeq (fun i:fin m1 => mkvSeq (fun j:fin m2 =>
      match Nat.ltb_spec0 (fin2nat c) channel1 with
      | ReflectT _ H_lt => x|[b]|[nat2fin H_lt]|[i]|[j]
      | ReflectF _ H_ge => y|[b]|[@exist nat (fun i => i < channel2) (fin2nat c - channel1) (@fin_ge_sub_lt channel1 channel2 c H_ge)]|[i]|[j]
      end)))).

Definition Reshape3d_2d{b m1 m2}(k:nat)
  (e: exp (ary '{b} (ary '{m1} (ary '{m2} num))))
  : exp (ary '{k} (ary '{((b*m1*m2)/k)} num)) :=
  tlet e0 := Flatten3d e in
  mkvSeq(fun i => mkvSeq(fun j => 
    e0|[nat2fin (fin_mul_add_lt_div (b*m1*m2) k j i)])).

Fixpoint ReshapeList2d (l: list (list nat))
  : list nat := 
  match l with
  | [] => []
  | h :: tl => h ++ ReshapeList2d tl
  end.

Definition m_nth {n m1 m2:nat}(v:exp (ary '{n} (ary '{m1} (ary '{m2} num))))(i: fin n) 
  : exp (ary '{m1} (ary '{m2} num)) := 
  mkvSeq (fun j=> mkvSeq(fun k => v|[i]|[j]|[k] )).

Notation " m [ i ] " := (m_nth m i) (at level 2).


(* ============================================================================================ *)

Definition loss{n}(p: exp (ary '{n} num)):=
  div_n (sum (mkvSeq (fun i=> negate (log p|[i])))) n.

Definition Softmax_loss{n}(y: exp (ary '{n} num)):=
  tlet tmp := Softmax1d y in mkvSeq (fun i=> negate (log tmp|[i])).

Definition Softmax_Loss{n}(z: exp (ary '{n} num))(label:nat):=
  tlet sum := sum (mkvSeq (fun i:fin n => pExp z|[i])) in
    negate (log (div (pExp (safe_idx_nat z label)) sum)).

Definition SparseCateCross_Loss{m n}
  (y: exp (ary '{m} (ary '{n} num)))(label: exp (ary '{m} (ary '{n} num)))
  :=
  negate (div_n (sum (mkvSeq (fun i: fin m => 
    sum (mkvSeq (fun j:fin n => 
      mul y|[i]|[j] (log label|[i]|[j])))))) m).

Definition MSE_loss{n}(y y': exp (ary '{n} num)):=
  div_n (sum (mkvSeq (fun i=> mul (sub y|[i] y'|[i]) (sub y|[i] y'|[i])))) n.

Definition Relu_grad {m filernum:nat}(input: exp(ary '{filernum} (ary '{m} (ary '{m} num)))):
  exp(ary '{filernum} (ary '{m} (ary '{m} num))) :=
    mkvSeq (fun num: fin filernum => mkvSeq (fun i0:fin m => mkvSeq (fun i1:fin m => 
      if (bexp2bool (leExp input|[num]|[i0]|[i1] zero)) then zero
      else one ))).

Definition relu (e: exp num): exp num :=
  if (bexp2bool (leExp e zero)) then zero else e.

Definition relu_grad (e: exp num): exp num :=
  if (bexp2bool (leExp e zero)) then zero else one.

Definition output_backward{n}(a y: exp (ary '{n} num)):=
  mkvSeq (fun i=> sub a|[i] y|[i]).

Definition nn_backward{n m}(d_l: exp (ary '{n} num))(w: exp (ary '{n} (ary '{m} num)))
  (z_l_1: exp (ary '{m} num)) : exp (ary '{m} num) :=
  mkvSeq (fun i:fin m => mul (sum (mkvSeq (fun j:fin n => 
    mul w|[j]|[i] d_l|[j])))(relu_grad z_l_1|[i])).

Definition average_pool_backward{m}(dout: exp (ary '{m} (ary '{m} num)))
  (k:nat)(z_l_1: exp (ary '{(k*m)} (ary '{(k*m)} num)))
  : exp (ary '{(k*m)} (ary '{(k*m)} num)) :=
  mkvSeq (fun i:fin (k*m) => mkvSeq (fun j:fin (k*m) => 
    mul dout|[nat2fin (fin_div_lt' k m i)]|[nat2fin (fin_div_lt' k m j)] z_l_1|[i]|[j])).

Definition averagepool_backward{m}(dout: exp (ary '{m} (ary '{m} num)))(k:nat)
  : exp (ary '{(k*m)} (ary '{(k*m)} num)) :=
  mkvSeq (fun i:fin (k*m) => mkvSeq (fun j:fin (k*m) => 
    dout|[nat2fin (fin_div_lt' k m i)]|[nat2fin (fin_div_lt' k m j)])).

Definition average_pool_backward_g{channel m}(dout: exp (ary '{channel} (ary '{m} (ary '{m} num))))
  (k:nat)(z_l_1: exp (ary '{channel} (ary '{(k*m)} (ary '{(k*m)} num))))
  : exp (ary '{channel} (ary '{(k*m)} (ary '{(k*m)} num))) :=
  mkvSeq (fun c:fin channel => mkvSeq (fun i:fin (k*m) => mkvSeq (fun j:fin (k*m) => 
    mul dout|[c]|[nat2fin (fin_div_lt' k m i)]|[nat2fin (fin_div_lt' k m j)] z_l_1|[c]|[i]|[j]))). 

Definition convolution_backward{m n}(dout: exp (ary '{m} (ary '{m} num)))
  (x: exp (ary '{(m+n-1)} (ary '{(m+n-1)} num)))(w: exp (ary '{n} (ary '{n} num))) 
  : exp (ary '{(m+n-1)} (ary '{(m+n-1)} num)) :=
  tlet dout_pad := Padding2d (n-1) dout in
    mkvSeq (fun i0:fin (m+n-1) => mkvSeq (fun j0:fin (m+n-1) => 
      mul (sum (mkvSeq (fun i1:fin n => 
        sum (mkvSeq ( fun j1: fin n => 
          mul dout_pad|[nat2fin (fin_add_lt_conv m n i0 i1)]|[nat2fin (fin_add_lt_conv m n j0 j1)] w|[nat2fin (fin_minus_lt n i1)]|[nat2fin (fin_minus_lt n j1)])))))
           (relu_grad x|[i0]|[j0]))).

Definition convolution_backward_g{filernum channel m n}(dout: exp (ary '{filernum} (ary '{m} (ary '{m} num))))
  (x: exp (ary '{channel} (ary '{(m+n-1)} (ary '{(m+n-1)} num))))(w: exp (ary '{filernum} (ary '{channel} (ary '{n} (ary '{n} num))))) 
  : exp (ary '{channel} (ary '{(m+n-1)} (ary '{(m+n-1)} num))) :=
  tlet dout_pad := Padding3d (n-1) dout in
    mkvSeq (fun c:fin channel => mkvSeq (fun i0:fin (m+n-1) => mkvSeq (fun j0:fin (m+n-1) => 
      mul (sum (mkvSeq (fun f:fin filernum => 
        sum (mkvSeq (fun i1:fin n => sum (mkvSeq ( fun j1: fin n => 
          mul dout_pad|[f]|[nat2fin (fin_add_lt_conv m n i0 i1)]|[nat2fin (fin_add_lt_conv m n j0 j1)] w|[f]|[c]|[nat2fin (fin_minus_lt n i1)]|[nat2fin (fin_minus_lt n j1)])))))))
            (relu_grad x|[c]|[i0]|[j0])))).

Definition convolution_backward_w{m n}(dout: exp (ary '{m} (ary '{m} num)))
  (x: exp (ary '{(m+n-1)} (ary '{(m+n-1)} num))) : exp (ary '{n} (ary '{n} num)) :=
  mkvSeq (fun i0:fin n => mkvSeq (fun j0:fin n => 
    sum (mkvSeq (fun i1:fin m => 
      sum (mkvSeq ( fun j1: fin m => 
        mul x|[nat2fin (fin_add_lt_conv2 m n i0 i1)]|[nat2fin (fin_add_lt_conv2 m n j0 j1)] dout|[i1]|[j1])))))).

Definition convolution_backward_b{m}(dout: exp (ary '{m} (ary '{m} num)))
  : exp num :=
  sum (mkvSeq (fun i:fin m => 
    sum (mkvSeq (fun j: fin m => dout|[i]|[j])))).

Definition convolution_backward_w_g{filernum channel m n}
  (dout: exp (ary '{filernum} (ary '{(m + n - 1)} (ary '{(m + n - 1)} num))))
  (x: exp (ary '{channel} (ary '{m} (ary '{m} num))))
  : exp (ary '{filernum} (ary '{channel} (ary '{n} (ary '{n} num)))) :=
  mkvSeq(fun f:fin filernum => mkvSeq (fun c:fin channel =>
    mkvSeq (fun i0:fin n => mkvSeq (fun j0:fin n => 
      sum (mkvSeq (fun i1:fin m => 
        sum (mkvSeq ( fun j1: fin m => 
          mul dout|[f]|[nat2fin (fin_add_lt_conv2 m n i0 i1)]|[nat2fin (fin_add_lt_conv2 m n j0 j1)] x|[c]|[i1]|[j1])))))))).

Definition convolution_backward_b_g{filernum m n}
  (dout: exp (ary '{filernum} (ary '{(m + n - 1)} (ary '{(m + n - 1)} num))))
  : exp (ary '{filernum} num) :=
  mkvSeq(fun f:fin filernum => 
    sum (mkvSeq (fun i:fin (m + n - 1) => 
      sum (mkvSeq (fun j: fin (m + n - 1) => dout|[f]|[i]|[j]))))).

Definition nn_backward_w{m n}(dout: exp (ary '{n} num))(a_l_1: exp (ary '{m} num))
  : exp (ary '{n} (ary '{m} num)) :=
  mkvSeq (fun i:fin n => mkvSeq (fun j:fin m => mul dout|[i] a_l_1|[j])).

Definition nn_backward_b{n}(dout: exp (ary '{n} num))
  : exp (ary '{n} num) :=
  mkvSeq (fun i:fin n => dout|[i]).


(* ********************************Type Conversion*************************************** *)

Definition convert_1{batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{((m1 - 1 + 2 * 0) / 1 + 1)} (ary '{((m2 - 1 + 2 * 0) / 1 + 1)} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b: fin batch => mkvSeq (fun c: fin channel => 
    mkvSeq (fun i: fin m1 => mkvSeq (fun j:fin m2 => 
      safe_idx_nat (safe_idx_nat (input|[b]|[c]) (fin2nat i)) (fin2nat j))))).

Definition convert_3{batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{((m1 - 3 + 2 * 1) / 1 + 1)} (ary '{((m2 - 3 + 2 * 1) / 1 + 1)} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i =>
    mkvSeq (fun j => safe_idx_nat (safe_idx_nat (input|[b]|[c]) (fin2nat i)) (fin2nat j))))).

Definition convert_5{batch channel m1 m2}
  (input: exp (ary '{batch} (ary '{channel} (ary '{((m1 - 5 + 2 * 2) / 1 + 1)} (ary '{((m2 - 5 + 2 * 2) / 1 + 1)} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))) :=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i =>
    mkvSeq (fun j => safe_idx_nat (safe_idx_nat (input|[b]|[c]) (fin2nat i)) (fin2nat j))))).

Definition convert_1_3{batch channel m1 m2}(s:nat)
  (input: exp (ary '{batch} (ary '{channel} (ary '{((m1 - 3 + 2 * 1) / s + 1)} (ary '{((m2 - 3 + 2 * 1) / s + 1)} num)))))
  : exp (ary '{batch} (ary '{channel} (ary '{((m1 - 1 + 2 * 0) / s + 1)} (ary '{((m2 - 1 + 2 * 0) / s + 1)} num)))) :=
  mkvSeq (fun b => mkvSeq (fun c => mkvSeq (fun i =>
    mkvSeq (fun j => safe_idx_nat (safe_idx_nat (input|[b]|[c]) (fin2nat i)) (fin2nat j))))).

Definition convert_in{batch out_channel in_channel m1 m2}(s : nat)
  (input: exp (ary '{batch} (ary '{in_channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{out_channel} (ary '{((m1 - 1 + 2 * 0) / s + 1)} (ary '{((m2 - 1 + 2 * 0) / s + 1)} num)))) :=
  mkvSeq (fun b:fin batch => mkvSeq (fun c: fin out_channel => 
    mkvSeq (fun i => mkvSeq (fun j => safe_idx_nat (safe_idx_nat (safe_idx_nat (input|[b]) (fin2nat c)) (fin2nat i)) (fin2nat j))))).

Definition convert_times{batch channel m1 m2 growth_rate p'}
  (input: exp (ary '{batch} (ary '{(channel + growth_rate * p' + growth_rate)} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{(channel + growth_rate * (S p'))} (ary '{m1} (ary '{m2} num)))):= 
  mkvSeq (fun b => mkvSeq (fun c => 
    mkvSeq (fun i => mkvSeq (fun j => (safe_idx_nat input|[b] (fin2nat c))|[i]|[j])))).

(* num_layers = 0 *)
Definition convert_times_1{batch channel m1 m2 growth_rate num_layers}(h:num_layers = 0)
  (input: exp (ary '{batch} (ary '{channel} (ary '{m1} (ary '{m2} num)))))
  : exp (ary '{batch} (ary '{(channel + growth_rate * num_layers)} (ary '{m1} (ary '{m2} num)))):= 
  mkvSeq (fun b => mkvSeq (fun c => 
    mkvSeq (fun i => mkvSeq (fun j => (safe_idx_nat input|[b] (fin2nat c))|[i]|[j])))).


(* a recursive function to calculate the length of inner lists in a nested list *)  
Definition innerList_length {A : Type} (l : list (list A)) : nat :=  
  match l with  
  | nil => 0  
  | cons inner_list tl => length inner_list
  end. 

(* Accessing elements at a specific position in a nested list. *)  
Fixpoint nested_list_access(l : list (list nat)) (i j : nat) : nat :=  
  match l with  
  | nil => 0  
  | cons inner_list tl =>  
    match i with  
    | 0 => nth inner_list j  
    | S i' => nested_list_access tl i' j
    end  
  end.  

Notation " l [ i ][ j ] " := (nested_list_access l i j) (at level 2).

(* Retrieve the element from tensor e based on the indices in the input. *)
Definition Embedding2d {n1 n2} (m1 m2: nat)
  (input: list (list nat))(e: exp (ary '{n1} (ary '{n2} num)))
  : exp (ary '{m1} (ary '{m2} (ary '{n2} num))) := 
  mkvSeq (fun i:fin m1 => mkvSeq (fun j:fin m2 => 
    mkvSeq (fun k: fin n2 => safe_idx_nat (safe_idx_nat e (input[i][j])) (fin2nat k)))).

Definition e: Tensor2 5 2 := 
  [[REconst 1%R "1",REconst 1%R "1"],[REconst 2%R "2",REconst 2%R "2"],[REconst 3%R "3",REconst 3%R "3"],[REconst 4%R "4",REconst 4%R "4"],[REconst 5%R "5",REconst 5%R "5"]].
Definition input: list (list nat) := [[1;2;1];[0;3;4]].

(* Compute (Embedding2d 2 3 input e). *)
(*      = [[[(R1 + R1)%R, (R1 + R1)%R],
        [(R1 + (R1 + R1))%R, (R1 + (R1 + R1))%R],
        [(R1 + R1)%R, (R1 + R1)%R]],
       [[R1, R1],
       [((R1 + R1) * (R1 + R1))%R,
       ((R1 + R1) * (R1 + R1))%R],
       [(R1 + (R1 + R1) * (R1 + R1))%R,
       (R1 + (R1 + R1) * (R1 + R1))%R]]]
     : exp (ary '{2} (ary '{3} (ary '{2} num))) *)


Definition e0: Tensor3 2 5 2 := 
  [[[REconst 1%R "1",REconst 1%R "1"],[REconst 2%R "2",REconst 2%R "2"],[REconst 3%R "3",REconst 3%R "3"],[REconst 4%R "4",REconst 4%R "4"],[REconst 5%R "5",REconst 5%R "5"]],
  [[REconst 0%R "0",REconst 0%R "0"],[REconst 0%R "0",REconst 0%R "0"],[REconst 0%R "0",REconst 0%R "0"],[REconst 0%R "0",REconst 0%R "0"],[REconst 0%R "0",REconst 0%R "0"]]].

(* Compute (Reshape3d_2d 5 e0). *)

(* Compute (ReshapeList2d input). *)


















