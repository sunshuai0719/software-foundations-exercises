(* File: Rel.v *)
(* Title: Rel - Properties of Relations *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com *)
(* Version: 2011-06-26 *)

Require Export Logic.

Definition relation (X : Type) := X -> X -> Prop.

(* Basic Properties of Relations *)

Definition partial_function {X : Type} (R : relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 P Q.
  inversion P.
  inversion Q.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not.
  unfold partial_function.
  intros H.
  assert (O = 1) as Nonsense.
    Case "Proof of assertion".
    apply H with O.
    apply le_n.
    apply le_S.
    apply le_n.
  inversion Nonsense.
Qed.

(* Exercise: 2 stars, optional *)

(* TOOD *)

(* Exercise: 2 stars, optional *)

(* TOOD *)

Definition reflexive {X : Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive.
  intros n.
  apply le_n.
Qed.

Definition transitive {X : Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.
Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold lt.
  unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo.
Qed.

(* Exercise: 2 stars, optional *)

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [ | m' Hm'o ].

  apply le_S.
  apply Hnm.

  apply le_S.
  apply IHHm'o.
Qed.

(* Exercise: 2 stars, optional *)

Theorem lt_trans'' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction o as [ | o' ].

  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := 0).
  apply Hnm.
  apply Hmo.

  apply le_trans with (a := (S n)) (b := (S m)) (c := S o').
  apply le_S.
  apply Hnm.
  apply Hmo.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  apply le_S. apply le_n.
  apply H.
Qed.

(* Exercise: 1 star, optional *)

Theorem le_S_n : forall n m,
  (S n <= S m) -> (n <= m).
Proof.
  apply Sn_le_Sm__n_le_m.
Qed.

(* TODO *)

(* Exercise: 2 stars, optional (le_S_n_inf) *)

(* TODO *)

(* Exercise: 1 star, optional *)

Theorem le_Sn_n : forall n,
  ~ (S n <= n).
Proof.
  Admitted.

Definition symmetric {X : Type} (R: relation X) :=
  forall a b : X, (R a b) -> (R b a).

(* Exercise: 2 stars, optional *)

Theorem le_not_symmetric :
  ~ (symmetric le).
Proof.
  unfold symmetric.
  unfold not.
  intro H.
  assert (Nonsense: 1 <= 0).
  apply (H 0 1).
  apply le_S.
  apply le_n.
  inversion Nonsense.
Qed.

Definition antisymmetric {X : Type} (R : relation X) :=
  forall a b : X, (R a b) -> (R b a) -> a = b.

(* Exercise: 2 stars, optional *)

Theorem le_antisymmetric :
  antisymmetric le.
Proof.
  unfold antisymmetric.
  intros n m H1 H2.
  Admitted.

(* TOOD *)

(* Exercise: 2 stars, optional *)

Theorem le_step : forall n m p,
  n < m ->
  m <= S p ->
  n <= p.
Proof.
  Admitted.

(* TODO *)

Definition equivalence {X : Type} (R: relation X) :=
  (reflexive R) /\ (symmetric R) /\ (transitive R).

Definition order {X : Type} (R: relation X) :=
  (reflexive R) /\ (antisymmetric R) /\ (transitive R).

Definition preorder {X : Type} (R: relation X) :=
  (reflexive R) /\ (transitive R).

Theorem le_order :
  order le.
Proof.
  unfold order. split.
  Case "refl". apply le_reflexive. split.
  Case "antisym". apply le_antisymmetric.
  Case "transitive". apply le_trans.
Qed.

(* Reflexive, Transitive Closure *)

Inductive clos_refl_trans {A : Type} (R: relation A) : relation A :=
  | rt_step : forall x y, R x y -> clos_refl_trans R x y
  | rt_refl : forall x, clos_refl_trans R x x
  | rt_trans : forall x y z,
    clos_refl_trans R x y ->
    clos_refl_trans R y z ->
    clos_refl_trans R x z.

Theorem next_nat_closure_is_le : forall n m,
  (n <= m) <-> ((clos_refl_trans next_nat) n m).
Proof.
  intros n m.
  split.
  Case "->".
    intro H. induction H.
    apply rt_refl.
    apply rt_trans with m.
    apply IHle.
    apply rt_step. apply nn.

  Case "<-".
    intro H. induction H.
    SCase "rt_step". inversion H. apply le_S. apply le_n.
    SCase "rt_refl". apply le_n.
    SCase "rt_trans".
      apply le_trans with y.
      apply IHclos_refl_trans1.
      apply IHclos_refl_trans2.
Qed.

Inductive refl_step_closure {X : Type} (R: relation X) : X -> X -> Prop :=
  | rsc_refl : forall (x : X), refl_step_closure R x x
  | rsc_step : forall (x y z : X), R x y ->
    refl_step_closure R y z ->
    refl_step_closure R x z.

Tactic Notation "rt_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "rt_step" | Case_aux c "rt_refl"
    | Case_aux c "rt_trans" ].

Tactic Notation "rsc_cases" tactic(first) ident(c) :=
  first;
    [ Case_aux c "rsc_refl" | Case_aux c "rsc_step" ].

Theorem rsc_R : forall (X : Type) (R : relation X) (x y : X),
  R x y -> refl_step_closure R x y.
Proof.
  intros X R x y r.
  apply rsc_step with y. apply r. apply rsc_refl.
Qed.

(* Exercise: 2 stars, optional (rsc_trans) *)

Theorem rsc_trans :
  forall (X:Type) (R: relation X) (x y z : X),
      refl_step_closure R x y ->
      refl_step_closure R y z ->
      refl_step_closure R x z.
Proof.
  Admitted.

(* TODO *)

(* Exercise: 3 stars, optional (rtc_rsc_coincide) *)

Theorem rtc_rsc_coincide :
  forall (X:Type) (R: relation X) (x y : X),
  clos_refl_trans R x y <-> refl_step_closure R x y.
Proof.
  Admitted.

(* end-of-Rel.v *)