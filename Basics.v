Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_working_day (d:day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Compute (next_working_day friday).
Compute (next_working_day (next_working_day friday)).

Example test_next_working_day:
  (next_working_day (next_working_day saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

From Coq Require Export String.

Inductive bool : Type :=
  | true
  | false.

Definition negb (b:bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1:bool) (b2:bool) :=
  match b1 with
  | true => b2 
  | false => false
  end.

Definition orb (b1:bool) (b2:bool) :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb2: (orb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb3: (orb true true) = true.
Proof. simpl. reflexivity. Qed.
Example test_orb4: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

(** test operation **)
Example test_andb1: (true && false) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb2: (false && true) = false.
Proof. simpl. reflexivity. Qed.
Example test_andb3: (true && true) = true.
Proof. simpl. reflexivity. Qed.
Example test_andb4: (false && false) = false.
Proof. simpl. reflexivity. Qed.

Inductive bw : Type :=
  | bw_black
  | bw_white.
Definition invert (x: bw) : bw :=
  if x then bw_white
  else bw_black.
Compute (invert bw_black).
(* ==> bw_white : bw *)
Compute (invert bw_white).
(* ==> bw_black : bw *)

Check negb true : bool.
Check bool.
Check negb: bool -> bool.
Check andb: bool -> bool -> bool.

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | white
  | black
  | primary (p : rgb).

Check color.

Definition isred (c : color) : bool :=
  match c with
  | white => false
  | black => false
  | primary red => true
  | primary _ => false
  end.

Compute isred (primary red).

Inductive bit : Type :=
  | B0
  | B1.

Inductive nybble : Type :=
  | bits (b1 b2 b3 b4 : bit).

Check (bits B1 B0 B1 B0) :
  nybble.

Definition iszero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.

Compute (iszero (bits B1 B0 B1 B0)).
Compute (iszero (bits B0 B0 B0 B0)).

Module NatPlayground.

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n' : nat) : nat :=
  match n' with
  | O => O
  | S n' => n'
  end.

End NatPlayground.

Compute pred (O).
Check (S (S O)).

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.
Compute (minustwo 4).
Compute (S 4).

Fixpoint even (n' : nat) : bool :=
  match n' with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Definition odd (n : nat) : bool :=
  negb (even n).

Compute even 5.

Example test_odd1: odd 3 = true.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.
Fixpoint plusee (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Compute plusee (S (S O)) (S O).
Compute plusee 1 5.
Example test_pluse: plusee 1 5 = 6.
Proof. simpl. reflexivity. Qed.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => (plusee m (mult n' m))
  end.

Compute mult 3 2.

Fixpoint minus (n m: nat) : nat :=
  match n, m with
  | O, _ => O
  | S _, O => n
  | S n', S m' => minus n' m'
  end.

Compute minus 5 3.
Compute minus 2 3.
Example test_minus: minus 4 4 = 0. 
Proof. simpl. reflexivity. Qed.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Compute exp 2 2.
Compute exp 3 4.
Example test_exp: exp 2 10 = 1024.
Proof. simpl. reflexivity. Qed.

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.

Notation "x !" := (factorial x) : nat_scope.
Compute 4!.

Compute factorial 0.
Compute factorial 1.
Compute factorial 2.
Example test_factorial: factorial 5 = 120.
Proof. simpl. reflexivity. Qed.

Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
         | O => true
         | S m' => false
         end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.

Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' => match m with
            | O => false
            | S m' => leb n' m'
            end
  end.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Compute eqb 3 4.
Compute eqb 5 5.
Compute eqb 0 0.
Compute eqb 4 3.

Compute leb 3 4.
Compute leb 4 3.
Compute leb 0 0.

Example test_leb1: (2 <=? 10) = true.
Proof. simpl. reflexivity. Qed.

Definition ltb (n m : nat) : bool :=
  (n <=? m) && negb (n =? m).

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Compute 3 <? 5.
Compute 3 <? 3.


Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity.
Qed.

Theorem pluse_1_n : forall n : nat, 1 + n = S n.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem pluse_n_m : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite <- H.
  reflexivity.
Qed.

Theorem pluse_n_m_o : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H1. rewrite H1.
  intros H2. rewrite H2.
  simpl. reflexivity.
Qed.

Theorem mult_n_0_m_0 : forall p q : nat,
  (p * 0) + (q * 0) = 0.
Proof.
  intros p q.
  rewrite <- mult_n_O.
  rewrite <- mult_n_O.
  simpl. reflexivity.
Qed.

Check mult_n_O.
Check mult_n_Sm.

Theorem mult_n_1 : forall p : nat,
  (p * 1) = p.
Proof.
  intros p.
  rewrite <- mult_n_Sm.
  rewrite <- mult_n_O.
  simpl. reflexivity.
Qed.

Theorem plus_1_neq_0_1 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b. destruct b eqn:E.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_true_elim : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct b eqn:Eb.
  - simpl. intros H. destruct c eqn:Ec.
    + reflexivity.
    + rewrite H. reflexivity.
  - simpl. intros H. destruct c eqn:Ec.
    + reflexivity.
    + simpl. rewrite H. reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c. destruct c eqn:Ec.
  - reflexivity.
  - destruct b.
    + simpl. intros H. rewrite H. reflexivity.
    + simpl. intros H. rewrite H. reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  0 =? (n + 1) = false.
Proof.
  intros [|n].
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem identity_fn_applied_twice :
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros. rewrite H. rewrite H. reflexivity.
Qed.

Theorem identity_fn_applied_twice_neg :
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros. rewrite H. rewrite H. destruct b.
  - simpl. reflexivity.
  - simpl. reflexivity.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c. destruct b.
  - simpl. intros H. rewrite H. reflexivity.
  - simpl. intros H. rewrite H. reflexivity. 
Qed.


End NatPlayground2.

