Require Import Coq.Sets.Relations_1.
Require Import preliminaries.

Reserved Notation "x << y" (at level 70, no associativity).
Reserved Notation "x =*= y" (at level 70, no associativity).
Reserved Notation "x <<= y" (at level 70, no associativity).

Section AuxiliaryDefs.
Variable U : Type.

  Definition Irreflexive (R : Relation U) : Prop := forall x : U, ~ R x x.
  Definition sequence := nat -> U.

End AuxiliaryDefs.

Section CausalDef.
Variable U : Type.

  Class Causal :=
  { event := U
  ; precedence : Relation event
      where "x << y" := (precedence x y)
  ; synchronisation : Relation event
      where "x =*= y" := (synchronisation x y)
  ; causality := fun x y : event => x << y \/ x =*= y
      where "x <<= y" := (causality x y)
  ; constraint_precedence:
      Irreflexive event precedence /\ Transitive event precedence
  ; constraint_synchronisation : Equivalence event synchronisation
  ; constraint_congruence : forall x x' y y' : event,
      x =*= x' -> y =*= y' -> x << y -> x' << y'
  ; constraint_fincaus : forall (x : event) (s : sequence event),
      (forall n : nat, (s n) <<= x) -> exists m : nat, forall k : nat,
        k > m -> exists r : nat, r <= m /\ s r = s k
  }.

End CausalDef.

Notation "x << y" := (precedence x y).
Notation "x =*= y" := (synchronisation x y).
Notation "x <<= y" := (causality x y).

Instance timer : Causal nat :=
{ precedence := fun x y : nat => x < y
; synchronisation := fun x y : nat => x = y
}.
Proof.
  - unfold Irreflexive, Transitive. split; intros *.
    + apply lt_irrefl.
    + apply lt_trans.
  - constructor.
    + unfold Reflexive. reflexivity.
    + unfold Transitive. intros * H1 H2. rewrite H1. assumption.
    + unfold Symmetric. intros. symmetry. assumption.
  - intros * H1 H2 H3. rewrite <- H1. rewrite <- H2. assumption.
  - intros. unfold sequence in s.
    assert (H' : forall n : nat, s n <= x).
      intro. pose (H1 := H n). elim H1; intro H2.
      + apply lt_le. assumption.
      + rewrite H2. apply le_n.
    + apply ini_fin with x. assumption.
Defined.
