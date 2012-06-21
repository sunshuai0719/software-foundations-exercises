(* File: Gen.v *)
(* Title: Gen - Generalizing Induction Hypotheses *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com *)
(* Version: 2011-06-21 *)

Require Export Poly.

Theorem double_injective' : forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  simpl.
  intros m eq.
  destruct m as [ | m' ].

  SCase "m = O".
  reflexivity.

  SCase "m = S m'".
  inversion eq.

  Case "n = S n'".
  intros m eq.
  destruct m as [ | m' ].

  SCase "m = O".
  inversion eq.

  SCase "m = S m'".
  assert (n' = m') as H.

  SSCase "Proof of assertion".
  apply IHn'.
  inversion eq.
  reflexivity.

  rewrite -> H.
  reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
  double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [ | m' ].

  Case "m = O".
  simpl.
  intros n eq.
  destruct n as [ | n' ].

  SCase "n = O".
  reflexivity.

  SCase "n = S n'".
  inversion eq.

  Case "m = S m'".
  intros n eq.
  destruct n as [ | n' ].

  SCase "n = O".
  inversion eq.

  SCase "n = S n'".
  assert (n' = m') as H.

  SSCase "Proof of assertion".
  apply IHm'.
  inversion eq.
  reflexivity.

  rewrite -> H.
  reflexivity.
Qed.

(* Exercise: 3 stars (gen_dep_practice) *)

Theorem plus_n_n_injective_take2 : forall n m,
  n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  simpl.
  intros m eq.
  induction m as [ | m' ].

  SCase "m = O".
  reflexivity.

  SCase "m = S m'".
  inversion eq.

  Case "n = S n'".
  intros m eq.
  induction m as [ | m' ].

  SCase "m = O".
  inversion eq.

  SCase "m = S m'".
  inversion eq.
  rewrite <- plus_n_Sm in H0.
  rewrite <- plus_n_Sm in H0.
  inversion H0.
  apply IHn' in H1.
  rewrite -> H1.
  reflexivity.
Qed.

Theorem index_after_last : forall (n : nat) (X : Type) (l : list X),
  length l = n -> index (S n) l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [ | n' l' ].

  Case "l = []".
  simpl.
  intros n0 eq.
  reflexivity.

  Case "l = n' :: l'".
  simpl.
  intros n0 eq.
  rewrite <- eq.
  apply IHl'.
  reflexivity.
Qed.

(* Exercise: 3 stars, optional (index_after_last_informal) *)

(* TODO *)

(* Exercise: 3 stars, optional (gen_dep_practice_opt) *)

Theorem length_snoc''' : forall (n : nat) (X : Type) (v : X) (l : list X),
  length l = n ->
  length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [ | n' l' ].

  Case "l = []".
  simpl.
  intros n eq.
  rewrite -> eq.
  reflexivity.

  Case "l = n' :: l'".
  simpl.
  rewrite <- IHl'.
  intros n eq.
  rewrite <- eq.
  reflexivity.
  reflexivity.
Qed.

(* Exercise: 3 stars, optional (app_length_cons) *)

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) (x : X) (n : nat),
  length (l1 ++ (x :: l2)) = n ->
  S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n.
  generalize dependent n.
  generalize dependent l2.
  induction l1 as [ | n1' l1' ].

  Case "l1 = []".
  simpl.
  intros l2 n' eq.
  apply eq.

  Case "l1 = n1' :: l1'".
  induction l2 as [ | n2' l2' ].

  SCase "l2 = []".
  intro n.
  simpl.
  intro eq.
  inversion eq.
  destruct n as [ | n' ].
  inversion eq.

  inversion H.
  apply IHl1' in H1.
  rewrite -> H1.
  rewrite -> eq.
  reflexivity.

  simpl.
  intros n eq.
  destruct n as [ | n' ].
  inversion eq.

  inversion eq.
  apply IHl1' in H0.
  rewrite eq.
  rewrite H0.
  reflexivity.
Qed.

(* Exercise: 4 stars, optional (app_length_twice) *)

Theorem app_length_twice : forall (X : Type) (n : nat) (l : list X),
  length l = n ->
  length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [ | n' l' ].

  Case "l' = []".
  simpl.
  intros n eq.
  rewrite <- eq.
  simpl.
  reflexivity.

  Case "l' = n' :: l'".
  simpl.
  intros n.
  destruct n.
  intros eq.
  inversion eq.

  simpl.
  intros eq.
  inversion eq.
  apply IHl' in H0.
  inversion eq.
  rewrite H1.
  rewrite <- plus_n_Sm.
  rewrite <- IHl'.
  symmetry.
Admitted. (* needs the last bit of work. *)

(* end-of-Gen.v *)