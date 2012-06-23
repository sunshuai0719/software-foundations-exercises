(* File: Prop.v *)
(* Title: Prop - Propositions and Evidence *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com *)
(* Version: 2011-06-21 *)

Require Export Poly.

(* Programming with Propositions *)

Check (2 + 2) = 4.
(* ==> 2 + 2 = 4 : Prop *)

Check (ble_nat 3 2 = false).
(* ==> ble_nat 3 2 = false : Prop *)

Check (2 + 2) = 5.
(* ==> 2 + 2 = 5 : Prop *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity. Qed.

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ==> plus_fact : Prop *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity. Qed.

Definition strange_prop1 : Prop :=
  (2 + 2 = 5) -> (99 + 26 = 42).

Definition strange_prop2 : Prop :=
  forall n, (ble_nat n 17 = true) -> (ble_nat n 99 = true).

Definition even (n : nat) : Prop :=
  evenb n = true.

Check even.
(* ===> even : nat -> Prop *)

Check (even 4).
(* ==> even 4 : Prop *)

Check (even 3).
(* ==> even 3 : Prop *)

Definition even_n__even_SSn (n : nat) : Prop :=
  (even n) -> (even (S (S n))).

Definition between (n m o : nat) : Prop :=
  andb (ble_nat n o) (ble_nat o m) = true.

Definition teen : nat -> Prop := between 13 19.

Definition true_for_zero (P : nat -> Prop) : Prop :=
  P O.

Definition true_for_n__true_for_Sn (P : nat -> Prop) (n : nat) : Prop :=
  P n -> P (S n).

Definition preserved_by_S (P : nat -> Prop) : Prop :=
  forall n', P n' -> P (S n').

Definition true_for_all_numbers (P : nat -> Prop) : Prop :=
  forall n, P n.

Definition our_nat_induction (P : nat -> Prop) : Prop :=
  (true_for_zero P) ->
  (preserved_by_S P) ->
  (true_for_all_numbers P).

(* Evidence *)

(* Inductively Defined Propositions *)

Inductive good_day : day -> Prop :=
  | gd_sat : good_day saturday
  | gd_sun : good_day sunday.

Theorem gds : good_day sunday.
Proof. apply gd_sun. Qed.

Inductive day_before : day -> day -> Prop :=
  | db_tue : day_before tuesday monday
  | db_wed : day_before wednesday tuesday
  | db_thu : day_before thursday wednesday
  | db_fri : day_before friday thursday
  | db_sat : day_before saturday friday
  | db_sun : day_before sunday saturday
  | db_mon : day_before monday sunday.

Inductive fine_day_for_singing : day -> Prop :=
  | fdfs_any : forall d : day, fine_day_for_singing d.

Theorem fdfs_wed : fine_day_for_singing wednesday.
Proof. apply fdfs_any. Qed.

(* Proof Objects *)

Definition fdfs_wed' : fine_day_for_singing wednesday :=
  fdfs_any wednesday.

Check fdfs_wed'.
Check fdfs_wed.

Inductive ok_day : day -> Prop :=
  | okd_gd : forall d, good_day d -> ok_day d
  | okd_before : forall d1 d2, ok_day d2 -> day_before d2 d1 -> ok_day d1.

Definition okdw : ok_day wednesday :=
  okd_before wednesday thursday
    (okd_before thursday friday
       (okd_before friday saturday
         (okd_gd saturday gd_sat)
         db_sat)
       db_fri)
    db_thu.

Theorem okdw' : ok_day wednesday.
Proof.
  (* wednesday is OK because it's the day before an OK day *)
  apply okd_before with (d2:=thursday).
  (* "subgoal: show that thursday is ok". *)
    (* thursday is OK because it's the day before an OK day *)
    apply okd_before with (d2:=friday).
    (* "subgoal: show that friday is ok". *)
      (* friday is OK because it's the day before an OK day *)
      apply okd_before with (d2:=saturday).
        (* "subgoal: show that saturday is ok". *)
          (* saturday is OK because it's good! *)
          apply okd_gd. apply gd_sat.
        (* "subgoal: show that the day before saturday is friday". *)
          apply db_sat.
    (* "subgoal: show that the day before friday is thursday". *)
      apply db_fri.
  (* "subgoal: show that the day before thursday is wednesday". *)
  apply db_thu.
Qed.

Print okdw'.
(* ===> okdw' = okd_before wednesday thursday
                  (okd_before thursday friday
                    (okd_before friday saturday
                      (okd_gd saturday gd_sat) db_sat)
                    db_fri)
                  db_thu
              : ok_day wednesday *)

(* The Curry-Howard Correspondence *)

(*
   propositions - sets / types
   proofs       - data values
*)

(* Implication *)

Definition okd_before2 := forall d1 d2 d3,
  ok_day d3 ->
  day_before d2 d1 ->
  day_before d3 d2 ->
  ok_day d1.

(* Exercise: 1 star, optional (okd_before2_valid) *)

Theorem okd_before2_valid : okd_before2.
Proof.
  unfold okd_before2.
  intros d1 d2 d3 H_okd_d3 H_db_d2_d1 H_db_d3_d2.
  apply okd_before with (d2:=d2).
  apply okd_before with (d2:=d3).
  apply H_okd_d3.
  apply H_db_d3_d2.
  apply H_db_d2_d1.
Qed.

Definition okd_before2_valid' : okd_before2 :=
  fun (d1 d2 d3 : day) =>
    fun (H : ok_day d3) =>
      fun (H0 : day_before d2 d1) =>
        fun (H1 : day_before d3 d2) =>
          okd_before d1 d2 (okd_before d2 d3 H H1) H0.

(* Exercise: 1 star, optional (okd_before2_valid_defn) *)

(*
   ===> okd_before2_valid =
          fun (d1 d2 d3 : day)
            (H_okd_d3 : ok_day d3)
              (H_db_d2_d1 : day_before d2 d1)
                (H_db_d3_d2 : day_before d3 d2)
            => okd_before d1 d2
                (okd_before d2 d3 H_okd_d3 H_db_d3_d2)
                  H_db_d2_d1 : okd_before2
*)

(* Induction Principles for Inductively Defined Types *)

Check nat_ind.
(*  ===> nat_ind : forall P : nat -> Prop,
                      P 0  ->
                      (forall n : nat, P n -> P (S n))  ->
                      forall n : nat, P n  *)

Theorem mult_O_r' : forall n : nat,
  n * O = O.
Proof.
  apply nat_ind.
  Case "O". reflexivity.
  Case "S". simpl. intros n IHn. rewrite -> IHn.
  reflexivity.
Qed.

(* Exercise: 2 stars (plus_one_r') *)

(* Okay, so we are probably supposed to use nat_ind for this guy, since it would
   otherwise be quite trivial by just using plus_comm and plus_1_l. *)
Theorem plus_one_r' : forall n : nat,
  n + 1 = S n.
Proof.
  apply nat_ind.
  Case "O".
  unfold plus.
  reflexivity.

  Case "S".
  intros n IHn.
  rewrite <- plus_n_Sm.
  rewrite <- IHn.
  rewrite <- plus_n_O.
  reflexivity.
Qed.

Inductive yesno : Type :=
  | yes : yesno
  | no : yesno.

Check yesno_ind.
(* ===> yesno_ind : forall P : yesno -> Prop,
                      P yes  ->
                      P no  ->
                      forall y : yesno, P y *)

(* Exercise: 1 star (rgb) *)

Inductive rgb : Type :=
  | red : rgb
  | green : rgb
  | blue : rgb.

Check rgb_ind.
(* ===> rgb_ind : forall P : rgb -> Prop,
                    P red ->
                    P green ->
                    P blue ->
                    forall r : rgb, P r *)

Inductive natlist : Type :=
  | nnil : natlist
| ncons : nat -> natlist -> natlist.

Check natlist_ind.
(* ===> natlist_ind : forall P : natlist -> Prop,
                        P nnil ->
                        (forall (n : nat) (n0 : natlist), P n0 -> P (ncons n n0)) ->
                        forall n : natlist, P n *)

(* Exercise: 1 star (natlist1) *)

Inductive natlist1 : Type :=
  | nnil1 : natlist1
  | nsnoc1 : natlist1 -> nat -> natlist1.

Check natlist1_ind.
(* ===> natlist1_ind : forall P : natlist1 -> Prop,
                         P nnil1 ->
                         (forall n : natlist1, P n -> forall n0 : nat,
                                          P (nsnoc1 n n0)) ->
                         forall n : natlist1, P n *)

(* Exercise: 1 star (ExSet) *)

(* ExSet_ind :
          forall P : ExSet -> Prop,
              (forall b : bool, P (con1 b)) ->
              (forall(n : nat) (e : ExSet), P e -> P (con2 n e)) →
              forall e : ExSet, P e *)

Inductive ExSet : Type :=
  | con1 : bool -> ExSet
  | con2 : nat -> ExSet -> ExSet.

Check ExSet_ind.

(*
Inductive list (X:Type) : Type :=
        | nil : list X
        | cons : X -> list X -> list X.

 ===> list_ind :
         forall (X : Type) (P : list X -> Prop),
            P [] ->
            (forall (x : X) (l : list X), P l -> P (x :: l)) →
            forall l : list X, P l
*)

(* Exercise: 1 star (tree) *)

Inductive tree (X : Type) : Type :=
  | leaf : X -> tree X
  | node : tree X -> tree X -> tree X.

Check tree_ind.
(* ===> tree_ind : forall (X : Type) (P : tree X -> Prop),
       (forall x : X, P (leaf X x)) ->
       (forall t : tree X, P t -> forall t0 : tree X, P t0 -> P (node X t t0)) ->
       forall t : tree X, P t *)

(* Exercise: 1 star (mytype) *)

(* mytype_ind :
        forall (X : Type) (P : mytype X -> Prop),
            (forall x : X, P (constr1 X x)) ->
            (forall n : nat, P (constr2 X n)) ->
            (forall m : mytype X, P m ->
               forall n : nat, P (constr3 X m n)) ->
            forall m : mytype X, P m *)

Inductive mytype (X : Type) : Type :=
  | constr1 : X -> mytype X
  | constr2 : nat -> mytype X
  | constr3 : mytype X -> nat -> mytype X.

Check mytype_ind.

(* Exercise: 1 star, optional (foo) *)

(* foo_ind :
        forall (X Y : Type) (P : foo X Y -> Prop),
             (forall x : X, P (bar X Y x)) ->
             (forall y : Y, P (baz X Y y)) ->
             (forall f1 : nat -> foo X Y,
               (forall n : nat, P (f1 n)) -> P (quux X Y f1)) ->
             forall f2 : foo X Y, P f2 *)

Inductive foo (X Y : Type) : Type :=
  | bar  : X -> foo X Y
  | baz  : Y -> foo X Y
  | quux : (nat -> foo X Y) -> foo X Y.

Check foo_ind.

(* Exercise: 1 star, optional (foo') *)

Inductive foo' (X:Type) : Type :=
  | C1 : list X -> foo' X -> foo' X
  | C2 : foo' X.

Check foo'_ind.
(* ===> foo'_ind : forall (X : Type) (P : foo' X -> Prop),
       (forall (l : list X) (f : foo' X), P f -> P (C1 X l f)) ->
       P (C2 X) -> forall f1 : foo' X, P f1 *)

(* Induction Hypotheses *)

Definition P_mOr (n : nat) : Prop :=
  n * O = O.

Definition P_mOr' : nat -> Prop :=
  fun n => n * O = O.

Theorem mult_O_r'' : forall n : nat,
  P_mOr n.
Proof.
  apply nat_ind.
  Case "n = O". reflexivity.
  Case "n = S n'".
  unfold P_mOr. simpl. intros n' IHn'.
  apply IHn'.
Qed.

(* Evenness Again *)

Inductive ev : nat -> Prop :=
  | ev_O : ev O
  | ev_SS : forall n : nat, ev n -> ev (S (S n)).

(* Exercise: 1 star, optional (four_ev) *)

Theorem four_ev' : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_O.
Qed.

Definition four_ev : ev 4 :=
  (ev_SS 2 (ev_SS 0 ev_O)).

(* Exercise: 2 stars (ev_plus4) *)

Theorem ev_plus' : forall n, ev n -> ev (4 + n).
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  unfold plus.
  intro H.
  apply ev_SS. apply ev_SS. apply ev_O.

  Case "n = S n'".
  intro H.
  simpl.
  apply ev_SS. apply ev_SS.
  apply H.
Qed.

Definition ev_plus4 : forall n, ev n -> ev (4 + n) :=
  ev_plus'. (* Probably not correct. *)

(* Exercise: 2 stars (double_even) *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  simpl.
  apply ev_O.

  Case "n = S n'".
  simpl.
  apply ev_SS.
  apply IHn'.
Qed.

(* Exercise: 4 stars, optional (double_even_pfobj) *)

Print double_even.
(* ===> double_even =
   fun n : nat =>
   nat_ind (fun n0 : nat => ev (double n0)) (let Case := "n = O" in ev_O)
      (fun (n' : nat) (IHn' : ev (double n')) =>
      let Case := "n = S n'" in ev_SS (double n') IHn') n
         : forall n : nat, ev (double n) *)

(* Reasoning by Induction Over Evidence *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [ | n' E' ].

  Case "E = ev_O".
  simpl.
  apply ev_O.

  Case "E = ev_SS n'".
  simpl.
  apply E'.
Qed.

(* Exercise: 1 star (ev_minus2_n) *)

(* If we destruct on n we have to prove ev O and ev S n', which we can't. *)

Theorem ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [ | n' E' ].

  Case "E = ev_O".
  unfold even.
  unfold evenb.
  reflexivity.

  Case "E = ev_SS n' E'".
  unfold even.
  unfold evenb.
  fold @evenb.
  apply IHE'.
Qed.

(* Exercise: 1 star (ev_even_n) *)

(* We would end up in the same situation as the exercise before. *)

(* Exercise: 1 star (l_fails) *)

(* The proofs fails because it want us to proof ev (S n) forall n : nat, which is not
   true. *)

(* Exercise: 2 stars (ev_sum) *)

Theorem ev_sum : forall n m,
  ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En as [ | n' En' ].

  Case "En = ev_O".
  destruct Em as [ | m' Em' ].

  SCase "Em = ev_O".
  unfold plus.
  apply ev_O.

  SCase "Em = ev_SS m' E'".
  unfold plus.
  apply ev_SS.
  apply Em'.

  Case "En = ev_SS n' E'".
  destruct Em as [ | m' Em' ].

  SCase "Em = ev_O".
  rewrite <- plus_n_O.
  apply ev_SS.
  apply En'.

  SCase "Em = ev_SS m' E'".
  rewrite <-2 plus_n_Sm.
  simpl.
  apply ev_SS.
  rewrite ->2 plus_n_Sm.
  apply IHEn'.
Qed.

Theorem SSev_even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [ | n' E' ].
  apply E'.
Qed.

Print SSev_even.

(* Exercise: 1 star (inversion_practice) *)

Theorem SSSSev_even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [ | n' E' ].
  inversion E' as [ | n'' E'' ].
  apply E''.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  inversion E as [ | n' E' ].
  inversion E' as [ | n'' E'' ].
  inversion E''.
Qed.

Theorem ev_minus2' : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [ | n' E' ].

  Case "E = ev_O".
  simpl.
  apply ev_O.

  Case "E = ev_SS n' E'".
  simpl.
  apply E'.
Qed.

(* Exercise: 3 stars (ev_ev_even) *)

Theorem ev_ev_even : forall n m,
  ev (n + m) -> ev n -> ev m.
Proof.
  intros n m E_n_m E_n.
  induction E_n as [ | n' E_n' ].

  Case "E = ev_O".
  apply E_n_m.

  Case "E = ev_SS n' E'".
  apply IHE_n'.
  inversion E_n_m.
  apply H0.
Qed.

(* Exercise: 3 stars, optional (ev_plus_plus) *)

Theorem ev_plus_plus : forall n m p,
  ev (n + m) -> ev (n + p) -> ev (m + p).
Proof.
  intros n m p.
  intros E_n_m.
  rewrite (plus_comm m p).
  apply ev_ev_even.
  rewrite (plus_comm n p).
  rewrite plus_swap.
  rewrite -> plus_assoc.
  rewrite -> plus_assoc.
  rewrite <- plus_assoc.
  apply ev_sum.
  rewrite <- double_plus.
  apply double_even.
  apply E_n_m.
Qed.

(* Why Define Propositions Inductively? *)

Inductive MyProp : nat -> Prop :=
  | MyProp1 : MyProp 4
  | MyProp2 : forall n : nat, MyProp n -> MyProp (4 + n)
  | MyProp3 : forall n : nat, MyProp (2 + n) -> MyProp n.

Theorem MyProp_ten : MyProp 10.
Proof.
  apply MyProp3.
  simpl.
  assert (12 = 4 + 8) as H12.
    Case "Proof of assertion". reflexivity.
  rewrite -> H12.
  apply MyProp2.
  assert (8 = 4 + 4) as H8.
    Case "Proof of assertion". reflexivity.
  rewrite -> H8.
  apply MyProp2.
  apply MyProp1.
Qed.

(* Exercise: 2 stars (MyProp) *)

Theorem MyProp_O : MyProp O.
Proof.
  apply MyProp3.
  apply MyProp3.
  assert (4 = 2 + 2) as H4.
    Case "Proof of assertion". reflexivity.
  rewrite -> plus_assoc.
  rewrite <- H4.
  rewrite <- plus_n_O.
  apply MyProp1.
Qed.

Theorem MyProp_plustwo : forall n : nat,
  MyProp n -> MyProp (S (S n)).
Proof.
  intros n E.
  destruct E as [ | n' E' | n' E' ].

  Case "E = MyProp 4".
  apply MyProp3.
  assert (8 = 2 + 6) as H8.
    SCase "Proof of assertion". reflexivity.
  rewrite <- H8.
  assert (8 = 4 + 4) as H4.
    SCase "Proof of assertion". reflexivity.
  rewrite -> H4.
  apply MyProp2.
  apply MyProp1.

  Case "E = MyProp (4 + n)".
  apply MyProp3.
  assert (8 + n' = 2 + S (S (4 + n'))) as H2S.
    SCase "Proof of assertion". reflexivity.
  rewrite <- H2S.
  assert (8 + n' = 4 + 4 + n') as H4.
    SCase "Proof of assertion". reflexivity.
  rewrite -> H4.
  rewrite <- plus_assoc.
  apply MyProp2.
  apply MyProp2.
  apply E'.

  Case "E = MyProp (S (S n'))".
  apply E'.
Qed.

Theorem MyProp_ev : forall n : nat,
  ev n -> MyProp n.
Proof.
  intros n E.
  induction E as [ | n' E' ].

  Case "E = ev_O".
  apply MyProp_O.

  Case "E = ev_SS n' E'".
  apply MyProp_plustwo.
  apply IHE'.
Qed.

(* Exercise: 3 stars (ev_MyProp) *)

Theorem ev_MyProp : forall n : nat,
  MyProp n -> ev n.
Proof.
  intros n E.
  induction E as [ | n' E' | n' E' ].

  Case "E = MyProp 4".
  apply ev_SS. apply ev_SS. apply ev_O.

  Case "E = MyProp (4 + n')".
  apply ev_plus4.
  apply IHE'.

  Case "E = MyProp (2 + n')".
  apply SSev_even.
  apply IHE'.
Qed.

(* Exercise: 3 stars, optional (ev_MyProp_informal) *)

(* TODO *)

(* The Big Picture: Coq's Two Universes *)





(* end-of-Prop.v *)