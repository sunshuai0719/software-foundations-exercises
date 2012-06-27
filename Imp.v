(* File: Imp.v *)
(* Title: Imp - Simple Imperative Programs *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com *)
(* Version: 2011-06-26 *)

(*
 Z ::= X;
 Y ::= 1;
 WHILE not (Z = 0) DO
   Y ::= Y * Z;
   Z ::= Z - 1
 END
*)

(* SfLib *)

Require Export SfLib.

(* Arithmetic and Boolean Expressions *)

Module AExp.

(* Syntax *)

Inductive aexp : Type :=
  | ANum : nat -> aexp
  | APlus : aexp -> aexp -> aexp
  | AMinus : aexp -> aexp -> aexp
  | AMult : aexp -> aexp -> aexp.

Inductive bexp : Type :=
  | BTrue : bexp
  | BFalse : bexp
  | BEq : aexp -> aexp -> bexp
  | BLe : aexp -> aexp -> bexp
  | BNot : bexp -> bexp
  | BAnd : bexp -> bexp -> bexp.

(*
aexp ::= nat
       | aexp '+' aexp
       | aexp '-' aexp
       | aexp '*' aexp

bexp ::= true
       | false
       | aexp '=' aexp
       | aexp '<=' aexp
       | bexp 'and' bexp
       | 'not' bexp
*)

(* Evaluation *)

Fixpoint aeval (e : aexp) : nat :=
  match e with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
  end.

Example test_aeval1 :
  aeval (APlus (ANum 2) (ANum 2)) = 4.
Proof.
  unfold aeval.
  reflexivity.
Qed.

Fixpoint beval (e : bexp) : bool :=
  match e with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => beq_nat (aeval a1) (aeval a2)
    | BLe a1 a2 => ble_nat (aeval a1) (aeval a2)
    | BNot b1 => negb (beval b1)
    | BAnd b1 b2 => andb (beval b1) (beval b2)
  end.

(* Optimization *)

Fixpoint optimize_Oplus (e : aexp) : aexp :=
  match e with
    | ANum n => ANum n
    | APlus (ANum O) e2 => optimize_Oplus e2
    | APlus e1 e2 => APlus (optimize_Oplus e1) (optimize_Oplus e2)
    | AMinus e1 e2 => AMinus (optimize_Oplus e1) (optimize_Oplus e2)
    | AMult e1 e2 => AMult (optimize_Oplus e1) (optimize_Oplus e2)
  end.

Example test_optimize_Oplus :
  optimize_Oplus
  (APlus (ANum 2)
         (APlus (ANum 0)
                (APlus (ANum 0)
                       (ANum 1))))
  = APlus (ANum 2) (ANum 1).
Proof. reflexivity. Qed.

Theorem optimize_Oplus_sound : forall e,
  aeval (optimize_Oplus e) = aeval e.
Proof.
  intros e. induction e.
  Case "ANum". reflexivity.
  Case "APlus". destruct e1.
  SCase "e1 = ANum n". destruct n.
  SSCase "n = 0". simpl. apply IHe2.
  SSCase "n <> 0". simpl. rewrite IHe2. reflexivity.
  SCase "e1 = APlus e1_1 e1_2".
  simpl. simpl in IHe1. rewrite IHe1.
  rewrite IHe2. reflexivity.
  SCase "e1 = AMinus e1_1 e1_2".
  simpl. simpl in IHe1. rewrite IHe1.
  rewrite IHe2. reflexivity.
  SCase "e1 = AMult e1_1 e1_2".
  simpl. simpl in IHe1. rewrite IHe1.
  rewrite IHe2. reflexivity.
  Case "AMinus".
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
  Case "AMult".
  simpl. rewrite IHe1. rewrite IHe2. reflexivity.
Qed.

(* Coq Automation *)





(* end-of-Imp.v *)