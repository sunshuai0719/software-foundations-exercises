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

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) (at level 95, no associativity) : type_scope.

Theorem iff_implies : forall P Q : Prop,
  (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  inversion H as [ HAB HBA ].
  apply HAB.
Qed.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  inversion H as [ HAB HBA ].
  split.
  Case "->". apply HBA.
  Case "<-". apply HAB.
Qed.

(* Exercise: 1 star (iff_properties) *)

Theorem iff_refl : forall P : Prop,
  P <-> P.
Proof.
  intros P.
  split.
  Case "->". intro H_P. apply H_P.
  Case "<-". intro H_P. apply H_P.
Qed.

Theorem iff_trans : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H_P_iff_Q H_Q_iff_R.
  inversion H_P_iff_Q as [ H_P__Q H_Q__P ].
  inversion H_Q_iff_R as [ H_Q__R H_R__Q ].
  split.

  Case "->".
  intro H_P.
  apply H_Q__R.
  apply H_P__Q.
  apply H_P.

  Case "<-".
  intro H_R.
  apply H_Q__P.
  apply H_R__Q.
  apply H_R.
Qed.

(* Exercise: 2 stars (MyProp_iff_ev) *)

Theorem MyProp_iff_ev' : forall n,
  MyProp n <-> ev n.
Proof.
  split.
  apply ev_MyProp.
  apply MyProp_ev.
Qed.

Print MyProp_iff_ev'.

Definition MyProp_iff_ev : forall n, MyProp n <-> ev n :=
  fun n => conj (MyProp n -> ev n) (ev n -> MyProp n)
    (ev_MyProp n) (MyProp_ev n).

(* Disjunction *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [ HP | HQ ].
  Case "right". apply or_intror. apply HP.
  Case "left". apply or_introl. apply HQ.
Qed.

Theorem or_commut' : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [ HP | HQ ].
  Case "right". right. apply HP.
  Case "left". left. apply HQ.
Qed.

(* Exercise: 2 stars, optional (or_commut'') *)

Definition or_commut''' : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q H =>
    match H with
      | or_introl HP => or_intror Q P HP
      | or_intror HQ => or_introl Q P HQ
    end.

Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R. intros H. inversion H as [ HP | [HQ HR] ].
  Case "left". split.
    SCase "left". left. apply HP.
    SCase "right". left. apply HP.
  Case "right". split.
    SCase "left". right. apply HQ.
    SCase "right". right. apply HR.
Qed.

(* Exercise: 2 stars, recommended (or_distributes_over_and_2) *)

Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R.
  intro H.
  inversion H as [[HP | HQ] [HP' | HR]].
  left. Case "left". apply HP.
  left. Case "left". apply HP.
  left. Case "left". apply HP'.
  right. Case "left". split.
    SCase "left". apply HQ.
    SCase "right". apply HR.
Qed.

(* Exercise: 1 star (or_distributes_over_and) *)

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
  apply or_distributes_over_and_1.
  apply or_distributes_over_and_2.
Qed.

(* Relating /\ and \/ with andb and orb *)

Theorem andb_true__and : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true". destruct c.
    SCase "c = true". apply conj. reflexivity. reflexivity.
    SCase "c = false". inversion H.
  Case "b = false". inversion H.
Qed.

Theorem and__andb_true : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  inversion H.
  rewrite H0.
  rewrite H1.
  unfold andb.
  reflexivity.
Qed.

(* Exercise: 1 star (bool_prop) *)

Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof.
  intros b c.
  destruct b.

  Case "b = true".
  destruct c.

  SCase "c = true".
  intro H.
  inversion H.

  SCase "c = false".
  intro H.
  right.
  reflexivity.

  Case "b = false".
  intro H.
  left.
  reflexivity.
Qed.

Theorem orb_true : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c.
  destruct b.

  Case "b = true".
  intro H.
  left.
  reflexivity.

  Case "b = false".
  intro H.
  right.
  rewrite <- H.
  unfold orb.
  reflexivity.
Qed.

Theorem orb_false : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof.
  intros b c.
  destruct b.

  Case "b = true".
  intro H.
  inversion H.

  Case "b = false".
  intro H.
  split.
  reflexivity.
  rewrite <- H.
  unfold orb.
  reflexivity.
Qed.

(* Falsehood *)

Inductive False : Prop :=.

(* Exercise: 1 star (False_ind_principle) *)

Check False_ind.
(* ===> False_ind : forall P : Prop, False -> P *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem ex_falso_quodlibet : forall (P : Prop),
  False -> P.
Proof.
  intros P contra.
  inversion contra.
Qed.

(* Truth *)

(* Exercise: 2 stars (True_induction) *)

Inductive Truth : Prop :=
  | truth : forall P, P -> Truth.

Check Truth_ind.

Lemma P_implies_Truth : forall (P : Prop),
  P -> Truth.
Proof.
  intros.
  apply truth in H.
  apply H.
Qed.

(* Negation *)

Definition not (P : Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> not : Prop -> Prop *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. inversion H.
Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  intros P Q H. inversion H as [ HP HNA ]. unfold not in HNA.
  apply HNA in HP. inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

(* Exercise: 2 stars, recommended (double_neg_inf) *)

(* TOOD *)

(* Exercise: 2 stars, recommended (contrapositive) *)

Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H_P__Q.
  unfold not.
  intros H_not_Q H_P.
  apply H_not_Q.
  apply H_P__Q.
  apply H_P.
Qed.

(* Exercise: 1 star (not_both_true_and_false) *)

Theorem not_both_true_and_false : forall P : Prop,
  ~(P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros [ HP H_not_P ].
  apply H_not_P.
  apply HP.
Qed.

Theorem five_not_even :
  ~ ev 5.
Proof.
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn].
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.
Qed.

(* Exercise: 1 star (ev_not_ev_S) *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof.
  unfold not.
  intros n H.
  induction H.

  Case "~ ev 1".
  intro contra.
  inversion contra.

  Case "~ ev (S (S (S n)))".
  intro H_SSSn.
  apply IHev.
  inversion H_SSSn.
  apply H1.
Qed.

(* Exercise: 1 star (informal_not_PNP) *)

(* TODO *)

Theorem classic_double_neg : forall P : Prop,
  ~~ P -> P.
Proof.
  intros P H.
  unfold not in H.
  Admitted. (* Cannot be proved *)

(* Exercise: 5 stars, optional (classic_axioms) *)

Definition peirce := forall P Q : Prop,
  ((P -> Q) -> P) -> P.

Definition classic := forall P : Prop,
  ~~ P -> P.

Definition excluded_middle := forall P : Prop,
  P \/ ~P.

Definition de_morgan_not_and_not := forall P Q : Prop,
  ~(~P /\ ~Q) -> P \/ Q.

Definition implies_to_or : forall P Q : Prop,
  (P -> Q) -> (~ P \/ Q).

(* TODO *)

(* Inequality *)

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
  unfold not in H.
  apply ex_falso_quodlibet.
  apply H.
  reflexivity.
Qed.

(* Exercise: 2 stars, recommended (not_eq_beq_false) *)

Theorem not_eq_beq_false : forall n n' : nat,
  n <> n' -> beq_nat n n' = false.
Proof.
  unfold not.
  intros n n' H.
  case beq_nat.
  apply ex_falso_quodlibet.
  apply H.
  apply beq_nat_eq.
Admitted.

(* Exercise: 2 stars, optional (beq_false_not_eq) *)

Theorem beq_false_not_eq : forall n m,
  false = beq_nat n m -> n <> m.
Proof.
  unfold not.
  intros n m.
  intro H.
  intro H'.
Admitted.

(* Existential Quantification *)

(* TODO *)





(* end-of-Logic.v *)