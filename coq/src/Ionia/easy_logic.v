Require Import Coq.Logic.Classical_Prop.

(** option related lemmas. **)

Lemma match_some { A:Set } : forall (a: option A) (b c : A), 
  a <> None -> match a with Some _ => b | None => c end = b.
Proof. intros. destruct a. 
+ reflexivity.
+ contradiction H. auto.
Qed.

Lemma some_none {A:Set} : forall (a: option A),
  a <> None -> exists (b:A), a = Some b.
Proof.
  intros  a H.          (* Introduce the type A and the option a, and assume a <> None *)
  destruct a as [b |].   (* Case analysis on a: either a is Some b or None *)
  - exists b.            (* If a is Some b, then we can directly take b as the witness *)
    reflexivity.         (* a = Some b holds by definition *)
  - exfalso.             (* If a is None, we reach a contradiction *)
    apply H.             (* Apply the hypothesis H: a <> None *)
    reflexivity.         (* But a is None, which contradicts H *)
Qed.


Lemma some_equal {A B:Set} : forall (a c: A) (b d:B),
   Some(a,b)=Some(c,d) <-> a=c /\ b=d.
Proof. intros. split; intro H. 
+ inversion H. auto.
+ inversion  H. subst a b. auto.
Qed.

Lemma some_neq_none {A:Set} : forall (a:A), Some a <> None.
Proof. intros a H. inversion H. Qed. 

Lemma some_is_not_none {A:Set} : forall (a:A) (b:option A), 
  b = Some a -> b <> None.
Proof. intros a b H. rewrite H. apply some_neq_none. Qed. 


Lemma option_none_dec {A:Set} : forall (a:option A),
  {a = None}+{a <> None}.
Proof. destruct a. 
+ right. apply some_neq_none. 
+ left. reflexivity.
Qed.


Definition opt_pair_inv {A B:Set} (z:(option (A*B))) : (option A)*(option B) := 
  match z with
   | Some (a,b) => (Some a, Some b)
   | None       => (None, None)
  end.

Definition opt_pair {A B:Set} (z: (option A)*(option B)) : option (A*B) :=
  match z with
   | (Some a, Some b) => Some (a, b)
   | (_,_)            => None
  end.

Lemma opt_pair_left_none {A B:Set} : forall (b: option B),
  @opt_pair A B (None, b) = None.
Proof. intro b.  destruct b; reflexivity. Qed.

Lemma opt_pair_right_none {A B:Set} : forall (a: option A),
  @opt_pair A B (a, None) = None.
Proof. intro a.  destruct a; reflexivity. Qed.

Lemma opt_pair_not_none  {A B:Set} : forall (a: option A) (b:option B),
  @opt_pair A B (a,b) <> None <-> a<>None /\ b<>None.
Proof. split. 
+ intro H. split. 
  - destruct a,b. 
    * apply some_neq_none.
    * apply some_neq_none.
    * simpl in H. contradiction H; auto. 
    * simpl in H. contradiction H; auto. 
  - destruct a,b. 
    * apply some_neq_none.
    * simpl in H. contradiction H; auto. 
    * apply some_neq_none.
    * simpl in H. contradiction H; auto. 
+ intro H. destruct H.
  - destruct a,b; try(apply some_neq_none);
    try(simpl in H; contradiction H; auto).
    simpl in H0. contradiction H0; auto.
Qed.

(** logic lemmas **)

Lemma negation_equivalence : forall A B : Prop, (A <-> B) <-> (~B <-> ~A).
Proof.  split; tauto. Qed. (* require Classical_Prop. *)


Lemma contrapositive : forall A B : Prop, (A -> B) -> (~B -> ~A).
Proof. tauto. Qed.

Lemma inverse_contrapositive : forall A B : Prop, (~B -> ~A) -> (A -> B).
Proof.
  intros A B H HA.
  destruct (classic B) as [HB | HnotB]. (* require Classical_Prop *)
  - exact HB.
  - exfalso.
    apply H in HnotB.
    contradiction.
Qed.

Lemma not_all_ex_not : forall (A : Type) (P : A -> Prop),
  ~ (forall x, P x) <-> exists x, ~ P x.
Proof.
  split.
  - (* Direction 1: ~(forall x, P x) -> exists x, ~P x *)
    intros H.
    (* Use proof by contradiction *)
    apply NNPP. (* Double negation elimination *)
    intros Hcontra.
    apply H.
    intros x.
    (* Case analysis on P x using excluded middle *)
    destruct (classic (P x)) as [Hx | Hx].
    + exact Hx.
    + (* If ~P x, then we have a contradiction with Hcontra *)
      exfalso.
      apply Hcontra.
      exists x.
      exact Hx.
  - (* Direction 2: exists x, ~P x -> ~(forall x, P x) *)
    intros [x Hx] Hall.
    apply Hx.
    apply Hall.
Qed.

Lemma double_negation_iff : forall P : Prop, ~ ~ P <-> P.
Proof.
  split.
  - (* Direction 1: ~ ~ P -> P *)
    intros H.
    apply NNPP. (* Use double negation elimination *)
    exact H.
  - (* Direction 2: P -> ~ ~ P *)
    intros H Hneg.
    apply Hneg.
    exact H.
Qed.

Lemma negation_neq : forall e1 e2 : Set, ~ e1 <> e2 <-> e1=e2.
Proof. intros. rewrite double_negation_iff. reflexivity.  Qed.

Lemma all_ex_not : forall (A : Type) (P : A -> Prop),
   (forall x, P x) <-> ~ (exists x, ~ P x).
Proof. intros. rewrite negation_equivalence. 
rewrite double_negation_iff. rewrite not_all_ex_not.
reflexivity.
Qed.
Lemma a_false_iff_not_true : forall (a:bool),
  a = false <-> not (a = true).
Proof. intro a. split; destruct a. 
+ intro. inversion H.
+ intro. auto. 
+ intro. contradiction H. auto.
+ intro. auto.
Qed.

Lemma true_iff_not_false : forall (a:bool),
  a = true <-> not (a = false).
Proof. intro a. split; destruct a. 
+ intros H1 H2. inversion H2.
+ intros H1 H2. inversion H1.
+ intro. auto. 
+ intro H2. contradiction H2. auto.
Qed.

