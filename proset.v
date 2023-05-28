Require Export Coq.Sets.Relations_1.
Require Import notation.

Definition Irreflexive (U : Type)(R : Relation U) : Prop
  := forall x : U, ~ R x x.

Class Preordered (U : Type) :=
{ proset := U
; prec : Relation proset
; pre_constr : Preorder proset prec
(* Derived Realtions *)
; same : Relation proset := fun x y => prec x y /\ prec y x
; less : Relation proset := fun x y => prec x y /\ ~ prec y x
}.

Notation "x << y" := (prec x y).
Notation "x == y" := (same x y).
Notation "x < y" := (less x y).
(*
Lemma new_lemma (U : Type) `(HPU : Preordered U) : Reflexive U (same U).
Proof.
  destruct HPU as [proset prec pre_constr]. destruct pre_constr as [R T].
  compute. split; apply R.
Qed.
*)