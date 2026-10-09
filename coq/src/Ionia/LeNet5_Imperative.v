(* Imperative counterparts of the R-based LeNet-5 operators.

   These are written entirely with the combinators from Ionia.DPIA_Rules,
   so that each one can be related to its functional version by a Leibniz
   equality.  To avoid a parsing conflict with the [match ... with | ...]
   keyword introduced by the safe-indexing lemmas, all array accesses are
   written explicitly with [idx] (read) and [idxAcc] (write). *)

Require Import Ionia.DPIA_Rules.
Require Import Ionia.Proof_CodeGen.
Import Proof_CodeGen.
From Stdlib Require Import String.
Open Scope string_scope.
Require Import Ionia.LeNet5_Utils.
Require Import Ionia.LeNet5_Functional.
Require Import Ionia.Ops_Conv.

Set Implicit Arguments.

(* -------------------------------------------------------------------------- *)
(* ReLU                                                                      *)
(* -------------------------------------------------------------------------- *)

Definition ReLU1d_comm {n:nat} (input : exp (ary '{n} num))
  (output : acc (ary '{n} num)) : comm :=
  seqfor (fun i : fin n =>
    If (leExp (idx input i) zero)
      (idxAcc output i |:= zero)
      (idxAcc output i |:= idx input i)).

Definition ReLU2d_comm {m1 m2:nat} (input : exp (ary '{m1} (ary '{m2} num)))
  (output : acc (ary '{m1} (ary '{m2} num))) : comm :=
  seqfor (fun i0 : fin m1 => seqfor (fun i1 : fin m2 =>
    If (leExp (idx (idx input i0) i1) zero)
      (idxAcc (idxAcc output i0) i1 |:= zero)
      (idxAcc (idxAcc output i0) i1 |:= idx (idx input i0) i1))).

Definition ReLU3d_comm {filernum m1 m2:nat}
  (input : exp (ary '{filernum} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{filernum} (ary '{m1} (ary '{m2} num)))) : comm :=
  seqfor (fun num : fin filernum => seqfor (fun i0 : fin m1 => seqfor (fun i1 : fin m2 =>
    If (leExp (idx (idx (idx input num) i0) i1) zero)
      (idxAcc (idxAcc (idxAcc output num) i0) i1 |:= zero)
      (idxAcc (idxAcc (idxAcc output num) i0) i1 |:= idx (idx (idx input num) i0) i1)))).

(* -------------------------------------------------------------------------- *)
(* Flatten3d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Flatten3d_comm {channel m1 m2 : nat}
  (input : exp (ary '{channel} (ary '{m1} (ary '{m2} num))))
  (output : acc (ary '{channel * m1 * m2} num)) : comm :=
  seqfor (fun x : fin (channel * m1 * m2) =>
    idxAcc output x |:=
      idx (idx (idx input
                   (fst (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
              (snd (idx_1d_to_2d (fst (idx_1d_to_2d x)))))
          (snd (idx_1d_to_2d x))).

(* -------------------------------------------------------------------------- *)
(* Linear1d                                                                   *)
(* -------------------------------------------------------------------------- *)

Definition Linear1d_comm {m outnum : nat}
  (w : exp (ary '{outnum} (ary '{m} num)))
  (bias : exp (ary '{outnum} num))
  (input : exp (ary '{m} num))
  (output : acc (ary '{outnum} num)) : comm :=
  seqfor (fun out : fin outnum =>
    suml (mkvSeq (fun i : fin m => mul (idx input i) (idx (idx w out) i)))
         (fun r => idxAcc output out |:= add r (idx bias out))
         (idxAcc output out)).

(* -------------------------------------------------------------------------- *)
(* Maxpool3d (2x2 non-overlapping windows)                                    *)
(* -------------------------------------------------------------------------- *)

Definition Maxpool3d_comm {channel m : nat}
  (input : exp (ary '{channel} (ary '{m} (ary '{m} num))))
  (output : acc (ary '{channel} (ary '{(m/2)} (ary '{(m/2)} num)))) : comm :=
  seqfor (fun c : fin channel => seqfor (fun i0 : fin (m/2) => seqfor (fun j0 : fin (m/2) =>
    maxl (mkvSeq (fun x : fin 4 =>
      idx (idx (idx input c)
               (nat2fin (maxpool_index_lt m i0 (fst (@idx_1d_to_2d 2 2 x)))))
          (nat2fin (maxpool_index_lt m j0 (snd (@idx_1d_to_2d 2 2 x))))))
         (fun r => idxAcc (idxAcc (idxAcc output c) i0) j0 |:= r)
         (idxAcc (idxAcc (idxAcc output c) i0) j0)))).

(* -------------------------------------------------------------------------- *)
(* Softmax1d                                                                  *)
(* -------------------------------------------------------------------------- *)

Definition Softmax1d_comm {n:nat} (input : exp (ary '{n} num))
  (output : acc (ary '{n} num)) : comm :=
  seqfor (fun i : fin n =>
    idxAcc output i |:= div (pExp (idx input i))
                            (sum (mkvSeq (fun j : fin n => pExp (idx input j))))).

(* -------------------------------------------------------------------------- *)
(* Conv3d                                                                     *)
(* -------------------------------------------------------------------------- *)

Definition Conv3dCell_comm {h w ic oc k p : nat} (Hk : k > 0)
  (kernel : exp (ary '{oc} (ary '{ic} (ary '{k} (ary '{k} num)))))
  (bias : exp (ary '{oc} num))
  (input : exp (ary '{ic} (ary '{h} (ary '{w} num))))
  (cout : fin oc)
  (i0 : fin (h + 2 * p - k + 1))
  (j0 : fin (w + 2 * p - k + 1))
  (output_cell : acc num)
  : comm :=
  suml (mkvSeq (fun flat : fin (ic * k * k) =>
    mul (pad_idx2d p (idx input (nat2fin (conv_flat_c_bound flat Hk)))
                    (fin2nat i0 + Nat.div (Nat.modulo (fin2nat flat) (k * k)) k)
                    (fin2nat j0 + Nat.modulo (fin2nat flat) k))
        (idx (idx (idx (idx kernel cout)
                       (nat2fin (conv_flat_c_bound flat Hk)))
                  (nat2fin (conv_flat_di_bound flat Hk)))
             (nat2fin (conv_flat_dj_bound flat Hk)))))
       (fun r : exp num => output_cell |:= add r (idx bias cout))
       output_cell.

Definition Conv3d_comm {h w ic oc k p : nat} (Hk : k > 0)
  (kernel : exp (ary '{oc} (ary '{ic} (ary '{k} (ary '{k} num)))))
  (bias : exp (ary '{oc} num))
  (input : exp (ary '{ic} (ary '{h} (ary '{w} num))))
  (output : acc (ary '{oc} (ary '{(h + 2 * p - k + 1)} (ary '{(w + 2 * p - k + 1)} num)))) : comm :=
  seqfor (fun cout : fin oc =>
    seqfor (fun i0 : fin (h + 2 * p - k + 1) =>
      seqfor (fun j0 : fin (w + 2 * p - k + 1) =>
        Conv3dCell_comm Hk kernel bias input cout i0 j0
          (idxAcc (idxAcc (idxAcc output cout) i0) j0)))).

(* -------------------------------------------------------------------------- *)
(* Full LeNet-5 imperative program (1×28×28 input, standard layer sizes)      *)
(* -------------------------------------------------------------------------- *)

(* Read a whole array/scalar accumulator back as an expression. *)
Definition bind_read {d:data} (a : acc d) (k : exp d -> comm) : comm :=
  fun rho => k (read_exp rho a) rho.

Definition lenet5_comm
  (input : exp (ary '{1} (ary '{28} (ary '{28} num))))
  (c1_w : exp (ary '{6} (ary '{1} (ary '{5} (ary '{5} num)))))
  (c1_b : exp (ary '{6} num))
  (c3_w : exp (ary '{16} (ary '{6} (ary '{5} (ary '{5} num)))))
  (c3_b : exp (ary '{16} num))
  (f5_w : exp (ary '{120} (ary '{400} num)))
  (f5_b : exp (ary '{120} num))
  (f6_w : exp (ary '{84} (ary '{120} num)))
  (f6_b : exp (ary '{84} num))
  (out_w : exp (ary '{10} (ary '{84} num)))
  (out_b : exp (ary '{10} num))
  (output : acc (ary '{10} num))
  : comm :=
  new (fun l1 =>
    seq (ReLU3d_comm (Conv3d (p:=2) H5 c1_w c1_b input) l1)
      (new (fun l2 =>
        seq (bind_read l1 (fun e => Maxpool3d_comm e l2))
          (new (fun l3 =>
            seq (bind_read l2 (fun e => ReLU3d_comm (Conv3d (p:=0) H5 c3_w c3_b e) l3))
              (new (fun l4 =>
                seq (bind_read l3 (fun e => Maxpool3d_comm e l4))
                  (new (fun l5 =>
                    seq (bind_read l4 (fun e => Flatten3d_comm e l5))
                      (new (fun l6 =>
                        seq (bind_read l5 (fun e => ReLU1d_comm (Linear1d f5_w f5_b e) l6))
                          (new (fun l7 =>
                            seq (bind_read l6 (fun e => ReLU1d_comm (Linear1d f6_w f6_b e) l7))
                              (bind_read l7 (fun e => Softmax1d_comm (Linear1d out_w out_b e) output)))
                            (acc' (Var "l7")))
                          ) (acc' (Var "l6")))
                      ) (acc' (Var "l5")))
                  ) (acc' (Var "l4")))
              ) (acc' (Var "l3")))
          ) (acc' (Var "l2")))
      ) (acc' (Var "l1")).
