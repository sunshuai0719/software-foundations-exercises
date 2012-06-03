(* Basics.v *)
(* Basics - Functional Programming *)

(* Most uses of simpl have been replaced with more atomic actions like unfold
   to better understand what happens all the way through the proof. *)

(* Days of the Week *)

Inductive day : Type :=
  | monday : day
  | tuesday : day
  | wednesday : day
  | thursday : day
  | friday : day
  | saturday : day
  | sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
    | monday => tuesday
    | tuesday => wednesday
    | wednesday => thursday
    | thursday => friday
    | friday => monday
    | saturday => monday
    | sunday => monday
  end.

Eval simpl in (next_weekday friday).
(* ==> monday : day *)
Eval simpl in (next_weekday (next_weekday saturday)).
(* ==> tuesday : day *)

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof.
  unfold next_weekday.
  reflexivity.
Qed.

(* Booleans *)

Inductive bool : Type :=
  | true : bool
  | false : bool.

Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
    | true => b2
    | false => false
  end.

Definition orb (b1 b2 : bool) : bool :=
  match b1 with
    | true => true
    | false => b2
  end.

Example test_orb1: (orb true false) = true.
Proof. unfold orb. reflexivity. Qed.
Example test_orb2: (orb false false) = false.
Proof. unfold orb. reflexivity. Qed.
Example test_orb3: (orb false true) = true.
Proof. unfold orb. reflexivity. Qed.
Example test_orb4: (orb true true) = true.
Proof. unfold orb. reflexivity. Qed.

Definition admit {T : Type} : T. Admitted.

(* Exercise: 1 star (nandb) *)
Definition nandb (b1 b2 : bool) : bool :=
  match b1 with
    | true => negb(b2)
    | false => true
  end.

Example test_nandb1: (nandb true false) = true.
Proof. unfold nandb. unfold negb. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. unfold nandb. unfold negb. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. unfold nandb. unfold negb. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. unfold nandb. unfold negb. reflexivity. Qed.

(* Exercise: 1 star (andb3) *)
Definition andb3 (b1 b2 b3 : bool) : bool :=
  match b1 with
    | false => false
    | true => match b2 with
                | false => false
                | true => b3
              end
    end.

Example test_andb31: (andb3 true true true) = true.
Proof. unfold andb3. reflexivity. Qed.
Example test_andb32: (andb3 false true true) = false.
Proof. unfold andb3. reflexivity. Qed.
Example test_andb33: (andb3 true false true) = false.
Proof. unfold andb3. reflexivity. Qed.
Example test_andb34: (andb3 true true false) = false.
Proof. unfold andb3. reflexivity. Qed.

(* Function Types *)

Check true.
(* ==> true : bool *)
Check (negb true).
(* ==> negb true : bool *)
Check negb.
(* ==> negb : bool -> bool *)

(* Numbers *)

Module Playground1.

Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

Definition pred (n : nat) : nat :=
  match n with
    | O => O
    | S n' => n'
  end.

End Playground1.

Definition minustwo (n : nat) : nat :=
  match n with
    | O => O
    | S O => O
    | S (S n') => n'
  end.

Check (S (S (S (S O)))).
Eval simpl in (minustwo 4).

Check S.
Check pred.
Check minustwo.

Fixpoint evenb (n : nat) : bool :=
  match n with
    | O => true
    | S O => false
    | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool :=
  negb (evenb n).

Example test_oddb1: (oddb (S O)) = true.
Proof. unfold oddb. unfold evenb. unfold negb. reflexivity. Qed.
Example test_oddb2: (oddb (S (S (S (S O))))) = false.
Proof. unfold oddb. unfold evenb. unfold negb. reflexivity. Qed.

Module Playground2.

Fixpoint plus (n m : nat) : nat :=
  match n with
    | O => m
    | S n' => S (plus n' m)
  end.

Eval simpl in (plus (S (S (S O))) (S (S O))).

Fixpoint mult (n m : nat) : nat :=
  match n with
    | O => O
    | S n' => plus m (mult n' m)
  end.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
    | O, _ => O
    | S _,  O => n
    | S n', S m' => minus n' m'
  end.

End Playground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
    | O => S O
    | S p => mult base (exp base p)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. unfold mult. unfold plus. reflexivity. Qed.

(* Exercise: 1 star (factorial) *)

Fixpoint factorial (n : nat) : nat :=
  match n with
    | O => S O
    | S n' => mult n (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. unfold factorial. unfold mult. unfold plus. reflexivity. Qed.
Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. unfold factorial. unfold mult. unfold plus. reflexivity. Qed.

Notation "x + y" := (plus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x - y" := (minus x y)
  (at level 50, left associativity)
  : nat_scope.
Notation "x * y" := (mult x y)
  (at level 40, left associativity)
  : nat_scope.

Check ((0 + 1) + 1).
Fixpoint beq_nat (n m : nat) : bool :=
  match n with
    | O => match m with
             | O => true
             | S m' => false
           end
    | S n' => match m with
                | O => false
                | S m' => beq_nat n' m'
              end
    end.

Fixpoint ble_nat (n m : nat) : bool :=
  match n with
    | O => true
    | S n' => match m with
                | O => false
                | S m' => ble_nat n' m'
              end
    end.

Example test_ble_nat1: (ble_nat 2 2) = true.
Proof. unfold ble_nat. reflexivity. Qed.
Example test_ble_nat2: (ble_nat 2 4) = true.
Proof. unfold ble_nat. reflexivity. Qed.
Example test_ble_nat3: (ble_nat 4 2) = false.
Proof. unfold ble_nat. reflexivity. Qed.

(* Exercise: 2 stars (blt_nat) *)
Definition blt_nat (n m : nat) : bool :=
  andb (ble_nat n m) (negb (beq_nat n m)).

Example test_blt_nat1: (blt_nat 2 2) = false.
Proof. unfold blt_nat. unfold ble_nat. unfold negb.
unfold beq_nat. unfold andb. reflexivity. Qed.
Example test_blt_nat2: (blt_nat 2 4) = true.
Proof. unfold blt_nat. unfold ble_nat. unfold negb.
unfold beq_nat. unfold andb. reflexivity. Qed.
Example test_blt_nat3: (blt_nat 4 2) = false.
Proof. unfold blt_nat. unfold ble_nat. unfold negb.
unfold beq_nat. unfold andb. reflexivity. Qed.

(* Proof by Simplification *)

Theorem plus_O_n : forall n : nat, O + n = n.
Proof.
  simpl.
  reflexivity.
Qed.

Theorem plus_O_n' : forall n : nat, O + n = n.
Proof.
  reflexivity.
Qed.

(* Exercise: 1 star, optional (simpl_plus) *)

(* Eval simpl in (forall n : nat, n + O = n). *)
(* ==> forall n : nat, n + 0 = n : Prop *)

(* Eval simpl in (forall n : nat, O + n = n). *)
(* ==> forall n : nat, n = n : Prop *)

(* Since we have proven that O + n = n, the simplification tactic manages ton
   further simplify the second expression because it also examines the theorems
   we have proven so far, while it can't simplify the first one further because
   n + O = n hasn't been proved yet. *)

(* The [intros] Tactic *)

Theorem plus_O_n'' : forall n : nat, O + n = n.
Proof.
  intros n.
  unfold plus.
  reflexivity.
Qed.

Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n.
  unfold plus.
  reflexivity.
Qed.

Theorem mult_O_l : forall n : nat, O * n = O.
Proof.
  intros n.
  unfold mult.
  reflexivity.
Qed.

(* Proof by Rewriting *)

Theorem plus_id_example : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intro H.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_id_example' : forall n m : nat,
  n = m -> n + n = m + m.
Proof.
  intros n m.
  intro H.
  rewrite <- H.
  reflexivity.
Qed.

(* Exercise: 1 star (plus_id_exercise) *)
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H_n_eq_m H_m_eq_o.
  rewrite -> H_n_eq_m.
  rewrite <- H_m_eq_o.
  reflexivity.
Qed.

Theorem mult_O_plus : forall n m : nat,
  (O + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity.
Qed.

(* Exercise: 2 stars, recommended (mult_1_plus) *)
Theorem mult_1_plus : forall n m : nat,
  (1 + n) * m = m + (n * m).
Proof.
  intros n m.
  rewrite -> plus_1_l.
  unfold mult. fold mult.
  reflexivity.
Qed.

(* Case Analysis *)

Theorem plus_1_neg_O : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros n.
  destruct n as [ | n' ].

  unfold plus.
  unfold beq_nat.
  reflexivity.

  unfold plus.
  unfold beq_nat.
  reflexivity.
Qed.

Theorem negb_involutive : forall b : bool,
  negb (negb b) = b.
Proof.
  intros b.
  destruct b.

  unfold negb.
  reflexivity.

  unfold negb.
  reflexivity.
Qed.

(* Exercise: 1 star (zero_nbeg_plus_1) *)
Theorem zero_nbeg_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intro n.
  destruct n.

  unfold plus.
  unfold beq_nat.
  reflexivity.

  unfold plus.
  unfold beq_nat.
  reflexivity.
Qed.

(* Naming Cases *)

Require Export Cases.

Theorem andb_true_elim1 : forall b c : bool,
  andb b c = true -> b = true.
Proof.
  intros b c.
  intro H.
  destruct b.

  Case "b = true".
  reflexivity.

  Case "b = false".
  rewrite <- H.
  unfold andb.
  reflexivity.
Qed.

(* Exercise: 2 stars (andb_true_elim2) *)
Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c.
  intro H.
  destruct c.

  Case "c = true".
  reflexivity.

  Case "c = false".
  rewrite <- H.
  unfold andb.
  destruct b.

  SCase "b = true".
  reflexivity.

  SCase "b = false".
  reflexivity.
Qed.

(* Induction *)

Theorem plus_O_r : forall n : nat,
  n + O = n.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  unfold plus.
  reflexivity.

  Case "n = S n'".
  unfold plus. fold plus.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem minus_diag : forall n : nat,
  minus n n = O.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  unfold minus.
  reflexivity.

  Case "n = S n'".
  unfold minus. fold minus.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* Exercise: 2 stars, recommended (basic_induction) *)
Theorem mult_O_r : forall n : nat,
  n * O = O.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  rewrite -> mult_O_l.
  reflexivity.

  Case "n = S n'".
  unfold mult. fold mult.
  rewrite -> plus_O_n.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m.
  induction n as [ | n' ].

  Case "n = O".
  rewrite -> plus_O_n.
  rewrite -> plus_O_n.
  reflexivity.

  Case "n = S n'".
  unfold plus. fold plus.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m.
  induction n as [ | n' ].

  Case "n = O".
  rewrite -> plus_O_n.
  rewrite -> plus_O_r.
  reflexivity.

  Case "n = S n'".
  unfold plus. fold plus.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  reflexivity.
Qed.

Fixpoint double (n : nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

(* Exercise: 2 stars (double_plus) *)
Lemma double_plus : forall n : nat,
  double n = n + n.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  unfold double.
  rewrite -> plus_O_n.
  reflexivity.

  Case "n = S n'".
  unfold double. fold double.
  rewrite -> IHn'.
  rewrite -> plus_n_Sm.
  unfold plus. fold plus.
  reflexivity.
Qed.

(* Exercise: 1 star (destruct_induction) *)
(* Briefly explain the difference between the tactics destruct and induction:
   Induction gives you a hypothesis while destruct just expects you to prove
   each case without an induction hypothesis. *)

(* Formal vs. Informal Proof. *)

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p.
  induction n as [ | n' ].

  Case "n = O".
  rewrite -> plus_O_n.
  rewrite -> plus_O_n.
  reflexivity.

  Case "n = S n'".
  unfold plus. fold plus.
  rewrite -> IHn'.
  reflexivity.
Qed.

(* Exercise: 2 stars (plus_comm_informal) *)

(* Translate your solution for plus_comm into an informal proof.

Theorem: Addition is commutative.

Proof: (* FILL IN HERE *)

*)

(* Exercise: 2 stars, optional (beq_nat_refl_informal) *)

(* Write an informal proof of the following theorem, using the informal proof of
   plus_assoc as a model. Don't just paraphrase the Coq tactics into English!

Theorem: true = beq_nat n n for any n.

Proof: (* FILL IN HERE *)

*)

(* Exercise: 1 star, optional (beq_nat_refl) *)
Theorem beq_nat_refl : forall n : nat,
  true = beq_nat n n.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  unfold beq_nat.
  reflexivity.

  Case "n = S n'".
  unfold beq_nat. fold beq_nat.
  rewrite <- IHn'.
  reflexivity.
Qed.

(* Proofs within Proofs *)

Theorem mult_O_plus' : forall n m : nat,
  (O + n) * m = n * m.
Proof.
  intros n m.
  assert (H: O + n = n).

    Case "Proof of assertion".
    unfold plus.
    reflexivity.

  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).

    Case "Proof of assertion".
    rewrite -> plus_comm.
    reflexivity.

  rewrite -> H.
  reflexivity.
Qed.

(* We can avoid introducing H by being more specific in our rewrite *)
Theorem plus_rearrange' : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  rewrite -> (plus_comm n m).
  reflexivity.
Qed.

(* Exercise: 4 stars (mult_comm) *)
Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  rewrite -> (plus_comm n m).
  reflexivity.
Qed.

Lemma n_mult_m_plus_n : forall n m : nat,
  (n * m) + n = n * (S m).
Proof.
  intros n m.
  induction n as [ | n' ].

  Case "n = O".
  rewrite -> mult_O_l.
  rewrite -> mult_O_l.
  rewrite -> plus_O_r.
  reflexivity.

  Case "n = S n'".
  unfold mult. fold mult.
  rewrite <- plus_1_l.
  rewrite -> (plus_comm 1 n').
  rewrite -> plus_assoc.
  rewrite -> (plus_comm m (n' * m)).
  rewrite <-? plus_assoc.
  rewrite -> (plus_comm m (n' + 1)).
  rewrite <-? plus_assoc.
  rewrite -> plus_1_l.
  rewrite ->? plus_assoc.
  rewrite -> IHn'.
  rewrite (plus_comm (S m) (n' * (S m))).
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
  m * n = n * m.
Proof.
  intros n m.
  induction n as [ | n' ].

  Case "n = O".
  rewrite -> mult_O_r.
  rewrite -> mult_O_l.
  reflexivity.

  Case "n = S n'".
  unfold mult. fold mult.
  rewrite -> IHn'.
  rewrite <- n_mult_m_plus_n.
  rewrite -> plus_comm.
  reflexivity.
Qed.

(* Exercise: 2 stars, optional (evenb_n__oddb_S_n) *)
Theorem evenb_n__oddb_S_n : forall n : nat,
  evenb n = negb (evenb (S n)).
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  unfold evenb. unfold negb.
  reflexivity.

  Case "n = S n'".
  unfold evenb at 2. fold evenb.
  rewrite -> IHn'.
  rewrite -> negb_involutive.
  reflexivity.
Qed.

(* More Exercises *)

Lemma mult_1_r : forall n : nat,
  n * 1 = n.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  unfold mult.
  reflexivity.

  Case "n = S n'".
  unfold mult. fold mult.
  rewrite -> IHn'.
  rewrite -> plus_1_l.
  reflexivity.
Qed.

(* TODO *)

(* end-of-Basics.v *)


