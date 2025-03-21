From LF Require Export Basics.

Theorem add_0_r : forall n : nat,
  n + 0 = n.
Proof.
  intros n. induction n as [|n'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem minus_n_n : forall n,
  minus n n = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Print minus_n_n.

Theorem mul_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity. 
Qed.

Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. rewrite add_0_r. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.

(*
Proof: 
  - First, suppose n = 0, we must show that
      0 + m = m + 0
    Left side 0 + m = m follows by defenition of +
    Right side m + 0 = m follows by add_0_r Theorem
  - Next, suppose n = S n', where
      n' + m = m + n'
    We must show that
      S n' + m = m + S n'
    By the defenition of +, this follows from
      S (n' + m) = m + S n'
    We can apply induction hypothesis 
    n' + m = m + n' to the Left side
      S (m + n') = m + S n'
    And Theorem plus_n_Sm to the right side
      S (m + n') = S (m + n') Qed.
*)

Theorem add_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn', plus_n_Sm. reflexivity.
Qed.

Print eqb.

Theorem eqb_refl : forall n : nat,
  (n =? n) = true.
Proof.
  intros n. induction n as [|n' IHn']. 
  - simpl. reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem even_S : forall n : nat,
  even (S n) = negb (even n).
Proof.
  intros n. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - rewrite IHn'. simpl. rewrite negb_involutive. reflexivity.
Qed.

Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem plus_rearrange: forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    { rewrite add_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

Theorem add_shuffle: forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p. rewrite add_comm.
  assert (H: n + p = p + n).
    { rewrite add_comm. reflexivity. }
  rewrite H. rewrite add_assoc. simpl. reflexivity.
Qed.

Theorem mult_n_0: forall n : nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  - reflexivity.
  - simpl. rewrite IHn'. reflexivity.
Qed.

Theorem plus_one_assoc: forall n m : nat,
  S (n + m) = S n + m.
Proof.
  intros n m. simpl. reflexivity.
Qed.


Theorem mult_distrub: forall n m : nat,
  n * S m = n * m + n.
Proof.
  intros n m. induction n as [|n' IHn'].
  - simpl. reflexivity.
  - simpl. rewrite IHn'. rewrite add_assoc. rewrite add_comm.
    rewrite plus_one_assoc. rewrite add_comm. simpl. reflexivity.
Qed.

Theorem mult_left_distrub: forall n m : nat,
  S n * m = n * m + m.
Proof.
  intros n m. simpl. rewrite add_comm. reflexivity.
Qed.

Theorem mul_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl. rewrite mult_n_0. reflexivity.
  - simpl. rewrite IHn'. rewrite add_comm. rewrite mult_distrub.
    rewrite add_comm. reflexivity.
Qed.
