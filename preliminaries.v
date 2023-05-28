Require Import Coq.Sets.Ensembles.
Require Import Coq.Sets.Finite_sets.

Lemma disj_conj : forall A B C : Prop, A \/ B /\ C <-> (A \/ B) /\ (A \/ C).
Proof.
  intros. split; intro H1.
  - split; elim H1; intro H2; (left; assumption) || (right; apply H2).
  - destruct H1 as [H11 H12]. elim H11; elim H12; intros H13 H14;
    (left; assumption) || right. split; assumption.
Qed.


Lemma Sn_n : forall n : nat, ~ S n = n.
Proof.
  intros. induction n as [| n' IHn].
  - intro. discriminate H.
  - intro H. apply IHn.
    inversion H. assumption.
Qed. 

Lemma le_trans : forall n m k : nat, n <= m -> m <= k -> n <= k.
Proof.
  intros * H1 H2. induction H2 as [| m'].
  - assumption.
  - constructor 2. assumption.
Qed.

Lemma S_le : forall n m :nat, n <= m -> S n <= S m .
Proof.
  intros * H. induction H.
  - constructor.
  - constructor 2. assumption.
Qed.

Lemma m_le_Sn : forall n m : nat, m <= S n <-> m <= n \/ m = S n.
Proof.
  intros. split; intro H.
  - destruct n as [| n']; inversion H as [| m' H1 H2].
    + right. reflexivity.
    + left. assumption. 
    + right. reflexivity.
    + left. assumption.
  - elim H; intro H1.
    + constructor 2. assumption.
    + rewrite H1. constructor.
Qed.

Lemma lt_irrefl : forall n : nat, ~ n < n.
Proof.
  intros * H.
  absurd (S n <= n).
  - contradict H. exfalso.
    induction n as [|n' IHn].
    + inversion H.
    + apply IHn.
      assert (H1 : pred (S (S n')) <= pred (S n')).
        apply le_pred. assumption.
    simpl in H1. assumption.
  - assumption.
Qed.

Lemma lt_trans : forall n m k : nat, n < m -> m < k -> n < k.
Proof.
  intros * H1 H2.
  induction H2 as [| k]; [apply le_S in H1 | apply le_S]; assumption.
Qed.

Definition ininat (n : nat) : Ensemble nat := fun m => m <= n.

Lemma ininat_0 : forall n : nat, In nat (ininat 0) n <-> n = 0.
Proof.
  intro. split; intro H.
  - destruct n as [| n'].
    + reflexivity.
    + compute in H. exfalso. inversion H.
  - rewrite H. apply le_n.
Qed.

Lemma ininat_n_Sn : forall n : nat, ~ In nat (ininat n) (S n).
Proof.
  intro. apply lt_irrefl.
Qed.

Lemma ininat_0_add : Same_set nat (ininat 0) (Add nat (Empty_set nat) 0).
Proof.
  constructor.
  - constructor 2. apply ininat_0 in H. rewrite H. compute. constructor.
  - compute. intros * H. destruct H as [|n H1].
    + compute in H. exfalso. contradiction.
    + compute in H1. destruct H1. constructor.
Qed.

Lemma fin_ininat_0 : Finite nat (ininat 0).
Proof.
  pose (H := Extensionality_Ensembles nat).
  pose (H1 := H (ininat 0) (Add nat (Empty_set nat) 0)).
  pose (H2 := H1 ininat_0_add). rewrite H2.
  constructor.
  - constructor.
  - intro H3. contradiction.
Qed.

Lemma ininat_Sn_add :
  forall n : nat, Same_set nat (ininat (S n)) (Add nat (ininat n) (S n)).
Proof.
  intro. split.
  - compute. intros * H.
    assert (H1 : x <= n \/ x = S n). apply m_le_Sn. assumption.
    elim H1; intro H2.
      + constructor. compute. assumption.
      + constructor 2. compute. rewrite H2. constructor.
  - compute. intros * H. destruct H; compute in H.
    + apply le_S. assumption.
    + destruct H. apply le_n.
Qed.

Lemma fin_ininat : forall n : nat, Finite nat (ininat n).
Proof.
  intro. induction n as [| n' IHn].
  - apply fin_ininat_0.
  - pose (H := Extensionality_Ensembles nat).
    pose (H1 := H (ininat (S n')) (Add nat (ininat n') (S n'))).
    pose (H2 := H1 (ininat_Sn_add n')). rewrite H2.
    constructor 2. assumption.
    apply ininat_n_Sn.
Qed.
