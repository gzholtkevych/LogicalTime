Require Export Coq.Sets.Relations_1.
Require Export Coq.Sets.Ensembles.
Require Export Coq.Sets.Finite_sets.


Reserved Infix "*->" (at level 70, no associativity).
Reserved Infix "*=*" (at level 70, no associativity).
Reserved Infix "*=>" (at level 70, no associativity).

Section AuxiliaryDefs.
Variable U : Type.

  Definition Irreflexive (R : Relation U) : Prop := forall x : U, ~ R x x.

End AuxiliaryDefs.

Class EventSet (U : Type) :=
{ event := U
; precedence : Relation event where "x *-> y" := (precedence x y)
; synchronisation : Relation event
    where "x *=* y" := (synchronisation x y)
; causality := fun x y : event => x *-> y \/ x *=* y
    where "x *=> y" := (causality x y)
; ax_precedence : Irreflexive event precedence /\ Transitive event precedence
; ax_syncronisation : Equivalence event synchronisation
; ax_pre_synchro : forall x x' y y' : event,
    x *=* x' -> y *=* y' -> x *-> y -> x' *-> y'
}.

Notation "x *-> y" := (precedence x y).
Notation "x *=* y" := (synchronisation x y).
Notation "x *=> y" := (causality x y).

Section Causet.
Variable U : Type.
Context `{EventSet U}.

  Definition Bot (x : event) : Ensemble event := fun y : event => y *=> x.

  Class Causet :=
  { ax_liveness : forall x : event, exists x' : event, x *-> x'
  ; ax_fincaused : forall x : event, Finite event (Bot x)
  }.

End Causet.
