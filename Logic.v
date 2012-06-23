(* File: Logic.v *)
(* Title: Logic - Logic in Coq *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com *)
(* Version: 2011-06-24 *)

Require Export "Prop".

(* Quantification and Implication *)

Definition funny_prop1 := forall n, forall (E : ev n), ev (n + 4).

Definition funny_prop1' := forall n, forall (_ : ev n), ev (n + 4).

Definition funny_prop1'' := forall n, ev n -> ev (n + 4).

(* "P -> Q" is just syntactic sugar for "forall (_ : P), Q". *)

(* Conjunction *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Check conj.
(* ===> forall P Q : Prop, P -> Q -> P /\ Q *)

Theorem and_example :
  (ev O) /\ (ev 4).
Proof.
  apply conj.
  Case "left". apply ev_O.
  Case "right". apply ev_SS. apply ev_SS. apply ev_O.
Qed.

Print and_example.
(* ===> and_example =
   conj (ev 0) (ev 4) ev_O (ev_SS 2 (ev SS O ev_O))
   : ev 0 /\ ev 4 *)

Theorem and_example' :
  (ev O) /\ (ev 4).
Proof.
  split.
  Case "left". apply ev_O.
  Case "right". apply ev_SS. apply ev_SS. apply ev_O.
Qed.

Theorem proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [ HP HQ ].
  apply HP.
Qed.

(* Exercise: 1 star, optional (proj2) *)

Theorem proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [ HP HQ ].
  apply HQ.
Qed.

Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  inversion H as [ HP HQ ].
  split.
  Case "left". apply HQ.
  Case "right". apply HP.
Qed.

Print and_commut.
(* ===>
   and_commut =
     fun (P Q : Prop) (H : P /\ Q) =>
     let H0 := match H with
               | conj HP HQ => conj Q P HQ HP
               end in H0
     : forall P Q : Prop, P /\ Q -> Q /\ P *)

(* Exercise: 2 stars (and_assoc) *)

Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
  split.
  Case "P". apply HP.
  Case "Q". apply HQ.
  Case "R". apply HR.
Qed.

(* Exercise: 2 stars, recommended (even_ev) *)

Theorem even_ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  induction n as [ | n' ].
  split.

  Case "n = O".
  intro H.
  apply ev_O.

  Case "n = 1".
  intro H.
  inversion H.

  Case "n = S n'".
  split.

  SCase "Left".
  intro H.
  destruct IHn' as [ Hn' HSn' ].
  apply HSn' in H.
  apply H.

  SCase "Right".
  intro H.
  destruct IHn' as [ Hn' HSn' ].
  SearchAbout ev.
  apply ev_SS in Hn'.
  apply Hn'.
  inversion H as [ H' ].
  apply H'.
Qed.

(* Exercise: 2 stars *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  admit.

(* Iff *)






(* end-of-Logic.v *)