Require Import causal_def.
Require Import preliminaries.

Instance evenat : EventSet nat :=
{ precedence := lt
; synchronisation := eq
}.
Proof.
  - split.
    + unfold Irreflexive. apply lt_irrefl.
    + unfold Transitive. apply lt_trans.
  - constructor.
    + unfold Reflexive. reflexivity.
    + unfold Transitive. intros * Exy Eyz.
      rewrite Exy. rewrite Eyz. reflexivity.
    + unfold Symmetric. intros * Exy. rewrite Exy. reflexivity.
  - intros * Exx' Eyy' Lxy. rewrite Exx' in Lxy. rewrite Eyy' in Lxy.
    assumption.
Defined.

Lemma Botnat_ininat : forall n : nat, Bot nat n = ininat n.
Proof.
  intro. pose (H := Extensionality_Ensembles nat). apply H.
  constructor; compute; intros m H1; elim H1.
  - intro H2. destruct H2 as [| n'].
    + constructor 2. constructor.
    + assert (H3 : m <= S m). constructor 2. constructor.
      pose (H4 := le_trans m (S m) n'). pose (H5 := H4 H3 H2).
      constructor 2. assumption.
  - intro H2. rewrite H2. constructor.
  - right. reflexivity.
  - intros k H2 H3. left. elim H3; intro H4.
    + constructor 2. assumption.
    + rewrite H4. constructor.
Qed.

Instance caunat : Causet nat.
Proof.
  constructor.
  - intro. exists (S x). simpl. apply le_n.
  - intro. rewrite Botnat_ininat. apply fin_ininat.
Defined.