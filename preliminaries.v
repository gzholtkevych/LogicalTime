Lemma lt_irrefl : forall n : nat, ~ n < n.
Admitted.

Lemma lt_trans : forall n m k : nat, n < m -> m < k -> n < k.
Admitted.

Lemma le_lt_or_eq : forall n m : nat, n <= m <-> n < m \/ n = m.
Admitted.

Lemma lt_le : forall n m : nat, n < m -> n <= m.
Admitted.


Lemma ini_fin : forall (n : nat) (s : nat -> nat),
  (forall m : nat, (s m) <= n) -> exists k : nat, forall r : nat,
    r > k -> exists t : nat, t <= k /\ s t = s r.
Admitted.
