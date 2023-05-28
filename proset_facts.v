Require Import proset.
Require Import preliminaries.
Require Import Logic.Decidable.

Section ProsetFacts.
Variable (U : Type).
Context `{HPU : Preordered U}.

  Lemma same_refl : Reflexive proset same.
  Proof.
    destruct HPU as [proset prec pre_constr]. destruct pre_constr as [R T].
    compute. split; apply R.
  Qed.

  Lemma same_symm : Symmetric proset same.
  Proof.
    destruct pre_constr as [R T].
    compute. intros * H. elim H. intros H1 H2. split; assumption.
  Qed.

  Lemma same_trans : Transitive proset same.
  Proof.
    destruct pre_constr as [R T].
    compute. intros * H1 H2. elim H1; elim H2. intros H31 H32 H33 H34.
    split.
    - pose (H4 := T x y z). apply H4; assumption.
    - pose (H4 := T z y x). apply H4; assumption.
  Qed.

(* Thus same is an equivalence *)

  Lemma less_irrefl : Irreflexive proset less.
  Proof. intros x H. destruct H as [H']. contradiction. Qed.

  Lemma less_trans : Transitive proset less.
  Proof.
    destruct pre_constr as [R T].
    intros x y z H1 H2. elim H1; elim H2; intros H31 H32 H33 H34.
    split.
    - apply T with y; assumption.
    - intro.
      assert (H' : z << y). apply T with x; assumption.
      contradiction.
  Qed.

(* Thus, less is a strict order *)

  Lemma same_less_cong : forall x x' y y' : proset,
    x == x' -> y == y' -> x < y -> x' < y'.
  Proof.
    destruct pre_constr as [R T].
    intros * H11 H12 H13. elim H13; intros H131 H132.
    split.
    - pose (H11' := proj2 H11). pose (H12' := proj1 H12).
      assert (x' << y). apply T with x; assumption.
      apply T with y; assumption.
    - intro.
      assert (H21 : y << x').
        pose (H12' := proj1 H12). apply T with y'; assumption.
      assert (H22 : y << x).
        pose (H11' := proj2 H11). apply T with x'; assumption.
      contradiction.
  Qed.

  Lemma same_less_prec : forall x y : proset, x == y \/ x < y -> x << y.
  Proof. intros * H1. elim H1; intro H2; apply H2. Qed.


End ProsetFacts.