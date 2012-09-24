(* File: Poly.v *)
(* Title: Poly - Polymorphism and Higher-Order Functions. *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com> *)
(* Version: 2012-09-24 *)

Require Export Lists.

(* Polymorphism *)

(* Polymorphic Lists *)

Inductive boollist : Type :=
  | bool_nil : boollist
  | bool_cons : bool -> boollist -> boollist.

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Check nil.
Check cons.

Check (cons nat 2 (cons nat 1 (nil nat))).

Fixpoint length (X : Type) (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length X t)
  end.

Example test_length1 :
  length nat (cons nat 1 (cons nat 2 (nil nat))) = 2.
Proof. reflexivity. Qed.

Example test_length2 :
  length bool (cons bool true (nil bool)) = 1.
Proof. reflexivity. Qed.

Fixpoint app (X : Type) (l1 l2 : list X) : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X : Type) (l : list X) (v : X) : list X :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X : Type) (l : list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Example test_rev1 :
  rev nat (cons nat 1 (cons nat 2 (nil nat)))
  = (cons nat 2 (cons nat 1 (nil nat))).
Proof. reflexivity. Qed.

Example test_rev2 :
  rev bool (nil bool) = nil bool.
Proof. reflexivity. Qed.

(* Type Inference *)

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Check app'.
Check app.

(* Argument Synthesis *)

Fixpoint length' (X : Type) (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length' _ t)
  end.

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* Implicit Arguments *)

Implicit Arguments nil [[X]].
Implicit Arguments cons [[X]].
Implicit Arguments length [[X]].
Implicit Arguments app [[X]].
Implicit Arguments rev [[X]].
Implicit Arguments snoc [[X]].

Definition list123'' :=
  cons 1 (cons 2 (cons 3 nil)).

Fixpoint length'' {X : Type} (l : list X) : nat :=
  match l with
    | nil => O
    | cons h t => S (length'' t)
  end.

(* Definition mynil := nil *)

Definition mynil : list nat := nil.

Check @nil.
Definition mynil' := @nil nat.

Notation "x :: y" := (cons x y) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y) (at level 60, right associativity).

Definition list123''' := [1, 2, 3].

(* Exercises: Polymorphic Lists *)

(* Exercise: 2 stars, optional (poly_exercises) *)

Fixpoint repeat' (X : Type) (n : X) (count : nat) : list X :=
  match count with
    | O => nil
    | S n' => n :: (repeat' X n n')
  end.

Example test_repeat1 :
  repeat' bool true 2 = cons true (cons true nil).
Proof.
  reflexivity. Qed.

Theorem nil_app : forall (X : Type) (l : list X),
  app [ ] l = l.
Proof.
  intros X l.
  unfold app.
  reflexivity.
Qed.

Theorem rev_snoc : forall (X : Type) (v : X) (s : list X),
  rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s.
  induction s as [ | v' s' ].

  Case "s = nil".
  unfold rev.
  unfold snoc.
  reflexivity.

  Case "s = cons v' s'".
  unfold snoc.
  fold @snoc.
  unfold rev.
  fold @rev.
  rewrite -> IHs'.
  unfold snoc.
  fold @snoc.
  reflexivity.
Qed.

Theorem snoc_with_append : forall (X : Type) (l1 l2 : list X) (v : X),
  snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v.
  induction l1 as [ | v' l1' ].

  Case "l1 = nil".
  unfold app.
  reflexivity.

  Case "l1 = cons v' l1'".
  unfold app.
  fold @app.
  unfold snoc.
  fold @snoc.
  rewrite -> IHl1'.
  reflexivity.
Qed.

(* Polymorphic Pairs *)

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Implicit Arguments pair [[X] [Y]].

Notation "( x , y )" := (pair x y).

Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x, y) => x end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with (x, y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match (lx, ly) with
    | ([],_) => []
    | (_,[]) => []
    | (x::tx, y::ty) => (x,y) :: (combine tx ty)
  end.

Fixpoint combine' {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
    | [], _ => []
    | _, [] => []
    | x::tx, y::ty => (x,y) :: (combine' tx ty)
  end.

(* Exercise: 1 star (combine_check) *)

(* What is the type of combine:
   forall X Y : Type , list X -> list  Y -> list (X * Y) *)

(* What does
   eval simpl in (combine [1,2] [false, false, true, true]
   print?
   [(1, false) , (2, false)] : list (nat * bool)
*)

(* Exercise: 2 stars, recommended (split) *)

Compute [(1, false) , (2, false)].
Compute ([1,2] , [false,false]).

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X * list Y) :=
  match l with
    | [] => ([], [])
    | (hx , hy) :: t =>
      ( (hx :: (fst (split t))), (hy :: (snd (split t))) )
  end.

Example test_split :
  split [ (1, false) , (2, false) ] = ([1,2] , [false, false]).
Proof. reflexivity. Qed.

(* Polymorphic Options *)

Inductive option (X : Type) : Type :=
  | Some : X -> option X
  | None : option X.

Implicit Arguments Some [[X]].
Implicit Arguments None [[X]].

Fixpoint index {X : Type} (n : nat) (l : list X) : option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 : index O [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1],[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

(* Exercise: 1 star (hd_opt_poly) *)

Definition hd_opt {X : Type} (l : list X) : option X :=
  match l with
    | nil => None
    | h :: t => Some h
  end.

Check @hd_opt.

Example test_hd_opt1 : hd_opt [1,2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1],[2]] = Some [1].
Proof. reflexivity. Qed.

(* Functions as Data *)

(* High-Order Functions *)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).

Check @doit3times.
(* ===> doit3times : forall X : Type, (X -> X) -> X -> X *)

Example test_doit3times : doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times' : doit3times negb true = false.
Proof. reflexivity. Qed.

(* Partial Application *)

Check plus.

Definition plus3 := plus 3.
Check plus3.

Example test_plus3 : plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' : doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* Digression: Currying *)

(* Exercise: 2 stars, optional (currying) *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x , y).

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z := f (fst p) (snd p).

Check @prod_curry.
Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type) (f: X -> Y -> Z) x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  unfold prod_uncurry.
  unfold prod_curry.
  unfold fst.
  unfold snd.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f: (X * Y) -> Z) (p: X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  unfold prod_curry.
  unfold prod_uncurry.
  destruct p.
  unfold fst.
  unfold snd.
  reflexivity.
Qed.

(* Filter *)

Fixpoint filter {X : Type} (test: X -> bool) (l : list X) : (list X) :=
  match l with
    | [] => []
    | h :: t => if test h
      then h :: (filter test t)
      else filter test t
  end.

Example testfilter1 : filter evenb [1,2,3,4] = [2,4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2 :
  filter length_is_1
  [ [1,2], [3], [4], [5,6,7], [], [8] ] =
  [ [3], [4], [8] ].
Proof. reflexivity. Qed.

Definition countoddmembers' (l : list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1: countoddmembers' [1,0,3,1,4,5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2: countoddmembers' [0,2,4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3: countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* Anonymous Functions *)

Example test_anon_fun' :
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

Example test_filter2' :
  filter (fun l => beq_nat (length l) 1)
  [ [1,2], [3], [4], [5,6,7], [], [8] ] =
  [ [3], [4], [8] ].
Proof. reflexivity. Qed.

(* Exercise: 2 stars, optional (filter_even_gt7) *)

Definition filter_even_gt7 ( l : list nat) : list nat :=
  filter (ble_nat 7) (filter evenb l).

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1,2,6,9,10,3,12,8] = [10,12,8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5,2,6,19,129] = [].
Proof. reflexivity. Qed.

(* Exercise: 3 stars, optional (partition) *)

Definition partition {X : Type} (test: X -> bool) (l : list X)
  : list X * list X :=
  ( (filter test l), (filter (fun n => negb (test n)) l) ).

Example test_partition1: partition oddb [1,2,3,4,5] = ([1,3,5], [2,4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5,9,0] = ([], [5,9,0]).
Proof. reflexivity. Qed.

(* Map *)

Fixpoint map {X Y : Type} (f: X -> Y) (l : list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Example test_map1 : map (plus 3) [2,0,2] = [5,3,5].
Proof. reflexivity. Qed.

Example test_map2 : map oddb [2,1,2,5] = [false, true, false, true].
Proof. reflexivity. Qed.

Example test_map3 : map (fun n => [evenb n, oddb n]) [2,1,2,5]
  = [[true, false], [false, true], [true, false], [false, true]].
Proof. reflexivity. Qed.

(* Exercise: 3 stars, optional (map_rev) *)

Lemma map_snoc : forall (X Y : Type) (f: X -> Y) (l : list X) (n : X),
  map f (snoc l n) = snoc (map f l) (f n).
Proof.
  intros X Y f l n.
  induction l as [ | n' l' ].

  Case "l = []".
  unfold snoc.
  fold @snoc.
  unfold map.
  unfold snoc.
  reflexivity.

  Case "l = n' :: l'".
  unfold snoc.
  fold @snoc.
  unfold map.
  fold @map.
  rewrite -> IHl'.
  unfold snoc.
  fold @snoc.
  reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f: X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l as [ | n l' ].

  Case "l = []".
  unfold map.
  fold @map.
  unfold rev.
  fold @rev.
  unfold map.
  reflexivity.

  Case "l = n :: l'".
  unfold map.
  fold @map.
  unfold rev.
  fold @rev.
  rewrite <- IHl'.
  rewrite -> map_snoc.
  reflexivity.
Qed.

(* Exercise: 2 stars, recommended (flat_map) *)

Fixpoint flat_map {X Y : Type} (f: X -> list Y) (l : list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (app (f h) (flat_map f t))
  end.

Example test_flat_map1:
  flat_map (fun n => [n,n,n]) [1,5,4]
  = [1, 1, 1, 5, 5, 5, 4, 4, 4].
Proof. reflexivity. Qed.

Definition option_map {X Y : Type} (f: X -> Y) (xo : option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(* Exercise: 2 stars, optional (implicit_args) *)

Fixpoint filter' (X : Type) (test: X -> bool) (l : list X) : (list X) :=
  match l with
    | [] => []
    | h :: t => if test h
      then h :: (filter' X test t)
      else filter' X test t
  end.

Fixpoint map' (X Y : Type) (f: X -> Y) (l : list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map' X Y f t)
  end.

(* Fold *)

Fixpoint fold {X Y : Type} (f: X -> Y -> Y) (l : list X) (b : Y) : Y :=
  match l with
    | nil => b
    | h :: t => f h (fold f t b)
  end.

Check (fold plus).
Eval simpl in (fold plus [1,2,3,4] 0).

Example fold_example1 : fold mult [1,2,3,4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true,true,false,true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1], [], [2,3], [4]] [] = [1,2,3,4].
Proof. reflexivity. Qed.

(* Exercise: 1 star, optional (fold_types_different) *)

(* E.g. When needing to check if all nats of a list are even. *)

(* Functions For Constructing Functions *)

Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue O = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

Definition override {X : Type} (f: nat -> X) (k : nat) (x : X) : nat -> X :=
  fun (k' : nat) => if beq_nat k k' then x else f k'.

Definition fmostlytrue := override (override ftrue 1 false) 3 false.

Example override_example1 : fmostlytrue 0 = true.
Proof. reflexivity. Qed.

Example override_example2 : fmostlytrue 1 = false.
Proof. reflexivity. Qed.

Example override_example3 : fmostlytrue 2 = true.
Proof. reflexivity. Qed.

Example override_example4 : fmostlytrue 3 = false.
Proof. reflexivity. Qed.

(* Exercise: 1 star (override_example) *)

Theorem override_example : forall (b : bool),
  (override (constfun b) 3 true) 2 = b.
Proof.
  intros b.
  unfold override.
  unfold beq_nat.
  unfold constfun.
  reflexivity.
Qed.

(* More About Coq *)

(* The apply Tactic *)

Theorem silly1 : forall (n m o p : nat),
  n = m ->
  [n,o] = [n,p] ->
  [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  apply eq2.
Qed.

Theorem silly2 : forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
  [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

Theorem silly2' : forall (n m o p : nat),
  n = m ->
  (forall (q r : nat), q = r -> [q,o] = [r,p]) ->
  [n,o] = [m,p].
Proof.
  intros n m o p eq1 eq2.
  rewrite -> (eq2 n m).
  reflexivity.
  rewrite -> eq1.
  reflexivity.
Qed.

Theorem silly2a : forall (n m : nat),
  (n,n) = (m,m) ->
  (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
  [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.

(* Exercise: 2 stars, optional (silly_ex) *)

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq1.
  apply eq2.
Qed.

Theorem silly3 : forall (n : nat),
  true = beq_nat n 5 ->
  beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  unfold beq_nat.
  fold beq_nat.
  apply H.
Qed.

(* Exercise: 3 stars, recommended (apply_exercise1) *)

Theorem rev_involutive : forall {X : Type} (l : list X),
  rev (rev l) = l.
Proof.
  intros X l.
  induction l as [ | n l' ].

  Case "l = nil".
  unfold rev.
  reflexivity.

  Case "l n :: l'".
  unfold rev.
  fold @rev.
  rewrite -> rev_snoc.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

(* Exercise: 1 star (apply_rewrite) *)

(* TODO *)

(* The unfold Tactic *)

(*
   In these solutions, we have used the unfold tactic from the very start of Basics.v
   since it lets the reader know exactly what is going on at every step of the
   way. Too heavy use of simpl can become a crutch that the student ends up
   relying too much upon. This is quite unfortunate since simpl can at times act
   as a double-edge sword that can unfold/fold too much so that the proof
   becomes harder to finish than if the unfolding and folding had been done in a
   manual step-by-step manner.
*)

Theorem unfold_example : forall m n,
  3 + n = m ->
  plus3 n + 1 = m + 1.
Proof.
  intros m n H.
  unfold plus3.
  rewrite -> H.
  reflexivity.
Qed.

Theorem override_eq : forall {X : Type} x k (f: nat -> X),
  (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

(* Exercise: 2 stars (override_neq) *)

Theorem override_neq : forall {X : Type} x1 x2 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  beq_nat k2 k1 = false ->
  (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f Hf Heq.
  unfold override.
  rewrite -> Heq.
  apply Hf.
Qed.

(* Inversion *)

Theorem eq_add_S : forall (n m : nat),
  S n = S m -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem silly4 : forall (n m : nat),
  [n] = [m] -> n = m.
Proof.
  intros n m H.
  inversion H.
  reflexivity.
Qed.

Theorem silly5 : forall (n m o : nat),
  [n,m] = [o,o] ->
  [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

(* Exercise: 1 star (sillyex1) *)

Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = z :: j ->
  y :: l = x :: j ->
  x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
  subst.
  inversion H2.
  reflexivity.
Qed.

Theorem silly6 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra.
  inversion contra.
Qed.

Theorem silly7 : forall (n m : nat),
  false = true ->
  [n] = [m].
Proof.
  intros n m contra.
  inversion contra.
Qed.

(* Exercise: 1 star (sillyex2) *)

Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
  x :: y :: l = [ ] ->
  y :: l = z :: j ->
  x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Lemma eq_remove_S : forall n m,
  n = m -> S n = S m.
Proof.
  intros n m eq.
  rewrite -> eq.
  reflexivity.
Qed.

Theorem beq_nat_eq : forall n m,
  true = beq_nat n m -> n = m.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  intro m.
  destruct m as [ | m' ].

  SCase "m = O".
  reflexivity.

  SCase "m = S m".
  unfold beq_nat.
  intros contra.
  inversion contra.

  Case "n = S n'".
  intros m.
  destruct m as [ | m' ].

  SCase "m = O".
  unfold beq_nat.
  intro contra.
  inversion contra.

  SCase "m = S m'".
  unfold beq_nat.
  fold beq_nat.
  intro H.
  apply eq_remove_S.
  apply IHn'.
  apply H.
Qed.

(* Exercise: 2 stars (beq_nat_eq_informal) *)

(* TODO *)

(* Exercise: 3 stars (beq_nat_eq') *)

Theorem beq_nat_eq' : forall m n,
  beq_nat n m = true -> n = m.
Proof.
  intros m.
  induction m as [ | m' ].

  Case "m = O".
  intro n.
  induction n as [ | n' ].

  SCase "n = O".
  reflexivity.

  SCase "n = S n'".
  unfold beq_nat.
  intro contra.
  inversion contra.

  Case "m = S m'".
  intro n.
  induction n as [ | n' ].

  SCase "n = O".
  unfold beq_nat.
  intro contra.
  inversion contra.

  SCase "n = S n'".
  unfold beq_nat.
  fold beq_nat.
  intro H.
  apply eq_remove_S.
  apply IHm'.
  apply H.
Qed.

Theorem length_snoc' : forall (X : Type) (v : X) (l : list X) (n : nat),
  length l = n -> length (snoc l v) = S n.
Proof.
  intros X v l.
  induction l as [ | v' l' ].

  Case "l = []".
  intros n eq.
  unfold snoc.
  rewrite <- eq.
  unfold length.
  reflexivity.

  Case "l = v' :: l'".
  intros n eq.
  rewrite <- eq.
  unfold snoc.
  fold @snoc.
  unfold length.
  fold @length.
  destruct n as[ | n' ].

  SCase "n = O".
  inversion eq.

  SCase "n = S n'".
  apply eq_remove_S.
  apply IHl'.
  reflexivity.
Qed.

(* Practice Session *)

(* Exercise: 2 stars, optional (practice) *)

Theorem beq_nat_O_l : forall n,
  true = beq_nat O n -> O = n.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  reflexivity.

  Case "n = S n'".
  unfold beq_nat.
  intro contra.
  inversion contra.
Qed.

Theorem beq_nat_O_r : forall n,
  true = beq_nat n O -> O = n.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  reflexivity.

  Case "n = S n'".
  unfold beq_nat.
  intro contra.
  inversion contra.
Qed.

Theorem double_injective : forall n m,
  double n = double m -> n = m.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  unfold double.
  fold @double.
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
  apply eq_remove_S.
  apply IHn'.
  inversion eq.
  reflexivity.
Qed.

(* Varying the Induction Hypothesis *)

(* Exercise: 2 stars, optional (app_ass') *)

Theorem app_ass' : forall (l1 l2 l3 : list nat),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1.
  induction l1 as [ | n l1' ].

  Case "l1 = []".
  intros l2 l3.
  unfold app.
  fold @app.
  reflexivity.

  Case "l1 = n :: l1'".
  intros l2 l3.
  unfold app.
  fold @app.
  rewrite -> IHl1'.
  reflexivity.
Qed.

(* Exercise: 3 stars (apply_exercise2) *)

Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  intro.
  induction m as [ | n' ].

  SCase "m = O".
  reflexivity.

  SCase "m = S m'".
  unfold beq_nat.
  reflexivity.

  Case "n = S n'".
  intro m.
  induction m as [ | m' ].

  SCase "m = O".
  unfold beq_nat.
  reflexivity.

  SCase "m = S m'".
  unfold beq_nat.
  fold beq_nat.
  apply IHn'.
Qed.

(* Exercise: 3 stars, recommended (beq_nat_sym_informal) *)

(* TODO *)

(* Using Tactics on Hypotheses *)

Theorem S_inj : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem S_inj' : forall (n m : nat) (b : bool),
  beq_nat (S n) (S m) = b ->
  beq_nat n m = b.
Proof.
  intros n m b H.
  unfold beq_nat in H.
  fold beq_nat in H.
  apply H.
Qed.

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
  true = beq_nat n 5 ->
  true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

(* Exercise: 3 stars, recommended (plus_n_n_injective) *)

Theorem plus_n_n_injective : forall n m,
  n + n = m + m ->
  n = m.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  unfold plus.
  fold plus.
  intros m.
  induction m as [ | m' ].

  SCase "m = O".
  reflexivity.

  SCase "m = S m'".
  intro contra.
  inversion contra.

  Case "n = S n'".
  intro m.
  induction m as [ | m' ].

  SCase "m = O".
  intro contra.
  inversion contra.

  SCase "m = S m'".
  intro eq.
  inversion eq.
  rewrite <-  plus_n_Sm in H0.
  rewrite <-  plus_n_Sm in H0.
  inversion H0.
  apply IHn' in H1.
  rewrite -> H1.
  reflexivity.
Qed.

(* Using destruct on Compound Expressions *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
    else if beq_nat n 5 then false
      else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intro n.
  unfold sillyfun.
  destruct (beq_nat n 3).

  Case "(beq_nat n 3) = true".
  reflexivity.

  Case "(beq_nat n 3) = false".
  destruct (beq_nat n 5).

  SCase "(beq_nat n 5) = true".
  reflexivity.

  SCase "(beq_nat n 5) = false".
  reflexivity.
Qed.

(* Exercise: 1 star (override_shadow) *)

Theorem override_shadow : forall {X : Type} x1 x2 k1 k2 (f: nat -> X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).

  Case "(beq_nat k1 k2) = true".
  reflexivity.

  Case "(beq_nat k1 k2) = false".
  reflexivity.
Qed.

(* Exercise: 3 stars, recommended (combine_split) *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [ | [ x y ] l' ].

  Case "l = []".
  intros l1 l2.
  unfold split.
  intro contra.
  inversion contra.
  subst.
  unfold combine.
  reflexivity.

  Case "l = (x,y) :: l'".
  intros l1 l2.
  unfold split.
  fold @split.
  destruct (split l') as [xs ys].
  unfold fst.
  unfold snd.
  destruct l1.

  SCase "l1 = []".
  unfold combine.
  intro contra.
  inversion contra.

  SCase "l2 = (x,y) :: l'".
  intro H.
  inversion H.
  subst.
  unfold combine.
  fold @combine.
  rewrite IHl'.
  reflexivity.
  reflexivity.
Qed.

(* Exercise: 3 stars, optional (split_combine) *)

(* Helper lemma *)
Lemma length_O_implies_nil : forall {X : Type} (l : list X),
  length l = O -> l = [].
Proof.
  intros X l H.
  destruct l as [ | n l' ].

  Case "l = nil".
  reflexivity.

  Case "l = n :: l'".
  inversion H.
Qed.

Theorem split_combine : forall (X Y : Type) (l1 : list X) (l2 : list Y),
  length l1 = length l2 -> split (combine l1 l2) = (l1, l2).
Proof.
  intros X Y.
  induction l1 as [ | n1' l1' ].

  Case "l1 = nil".
  intros l2 H.
  unfold combine.
  unfold split.
  unfold length in H.
  fold @length in H.
  rewrite (length_O_implies_nil l2).
  reflexivity.
  rewrite <- H.
  reflexivity.

  Case "l1 = n' :: l1'".
  intros l2.
  induction l2 as [ | n2' l2' ].

  SCase "l2 = []".
  unfold combine.
  fold @combine.
  unfold split.
  intro H.
  inversion H.

  SCase "l2 = n2' :: l2'".
  unfold combine.
  fold @combine.
  intro H.
  inversion H.
  unfold split.
  fold @split.
  apply IHl1' in H1.
  rewrite H1.
  reflexivity.
Qed.

(* The remember Tactic *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
    else if beq_nat n 5 then true
      else false.

Theorem sillyfun1_odd : forall (n : nat),
  sillyfun1 n = true ->
  oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  remember (beq_nat n 3) as e3.
  destruct e3.

  Case "e3 = true".
  apply beq_nat_eq in Heqe3.
  rewrite -> Heqe3.
  unfold oddb. unfold evenb. unfold negb.
  reflexivity.

  Case "e3 = false".
  remember (beq_nat n 5) as e5.
  destruct e5.

  SCase "e5 = true".
  apply beq_nat_eq in Heqe5.
  rewrite -> Heqe5.
  unfold oddb. unfold evenb. unfold negb.
  reflexivity.

  SCase "e5 = false".
  inversion eq.
Qed.

(* Exercise: 2 stars (override_same) *)

Theorem override_same : forall {X : Type} x1 k1 k2 (f : nat -> X),
  f k1 = x1 ->
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq.
  unfold override.
  remember (beq_nat k1 k2) as ek1k2.
  destruct ek1k2.

  Case "ek1k2 = true".
  rewrite <- eq.
  apply beq_nat_eq in Heqek1k2.
  rewrite Heqek1k2.
  reflexivity.

  Case "ek1k2 = false".
  reflexivity.
Qed.

(* Exercise: 3 stars, optional (filter_exercise) *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
  (x : X) (l lf : list X),
  filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l.
  induction l as [ | n' l' ].

  Case "l = []".
  unfold filter.
  intro lf.
  intro contra.
  inversion contra.

  Case "l = n' :: l'".
  unfold filter.
  fold @filter.
  remember (test n') as en'.
  destruct en'.

  SCase "en' = true".
  intros lf eq.
  rewrite Heqen'.
  inversion eq.
  reflexivity.

  intros lf eq.
  apply IHl' in eq.
  apply eq.
Qed.

(* The apply ... with ... Tactic *)

Example trans_eq_example : forall (a b c d e f : nat),
  [a,b] = [c,d] ->
  [c,d] = [e,f] ->
  [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Theorem trans_eq : forall {X : Type} (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
  [a,b] = [c,d] ->
  [c,d] = [e,f] ->
  [a,b] = [e,f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c,d]). (* could also just 'with (c,d)' *)
  apply eq1.
  apply eq2.
Qed.

(* Exercise: 3 stars, recommended (apply_exercises) *)

Example trans_eq_exercise : forall (n m o p : nat),
  m = (minustwo o) ->
  (n + p) = m ->
  (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with m.
  apply eq2.
  apply eq1.
Qed.

Theorem beq_nat_trans : forall n m p,
  true = beq_nat n m ->
  true = beq_nat m p ->
  true = beq_nat n p.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_eq in eq1.
  rewrite -> eq1.
  apply eq2.
Qed.

Theorem override_permute : forall {X : Type} x1 x2 k1 k2 k3 (f : nat -> X),
  false = beq_nat k2 k1 ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f.
  unfold override.
  remember (beq_nat k1 k3) as k1k3.
  remember (beq_nat k2 k3) as k2k3.
  destruct k1k3.
  destruct k2k3.
  apply beq_nat_eq in Heqk1k3.
  apply beq_nat_eq in Heqk2k3.
  rewrite <- Heqk2k3 in Heqk1k3.
  assert (k2 = k1 -> true = beq_nat k1 k2).

  Case "Proof of Assertion".
    destruct k1.
    destruct k2.
    reflexivity.

    intro contra.
    inversion contra.

    destruct k1.
    intro H.
    inversion H.
    unfold beq_nat.
    reflexivity.

    intro eq.
    rewrite <- eq.
    apply beq_nat_refl.

  symmetry in Heqk1k3.
  apply H in Heqk1k3.
  intro contra.
  rewrite beq_nat_sym in contra.
  rewrite <- contra in Heqk1k3.
  inversion Heqk1k3.

  intro eq.
  reflexivity.

  destruct k2k3.
  intro eq.
  reflexivity.

  intro eq.
  reflexivity.
Qed.

(* Review *)

(* No code in this section. *)

(* Additional Exercises *)

(* Exercise: 2 stars, optional (fold_length) *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l O.

Example test_fold_length1 : fold_length [4,7,0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l as [ | n l' ].

  Case "l = []".
  unfold fold_length.
  unfold fold.
  unfold length.
  reflexivity.

  Case "l = n :: l'".
  unfold length.
  fold @length.
  rewrite <- IHl'.
  unfold fold_length.
  unfold fold.
  fold @fold.
  reflexivity.
Qed.

(* Exercise: 3 stars, recommended (fold_map) *)

Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => cons (f x) y) l nil.

Theorem fold_map_correct : forall X Y (f: X -> Y) (l : list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l.
  induction l as [ | n l' ].

  Case "l = []".
  unfold map.
  unfold fold_map.
  unfold fold.
  reflexivity.

  Case "l = n :: l'".
  unfold map.
  fold @map.
  rewrite <- IHl'.
  unfold fold_map.
  unfold fold.
  fold @fold.
  reflexivity.
Qed.

(* Exercise: 2 stars, optional (mumble_grumble) *)

Module MumbleBaz.

Inductive mumble : Type :=
  | a : mumble
  | b : mumble -> nat -> mumble
  | c : mumble.

Inductive grumble (X : Type) : Type :=
  | d : mumble -> grumble X
  | e : X -> grumble X.

(*
   Q: Which of the following are well-typed elements of grumble X for some type X?
   a: d (b a 5)
   b: d mumble (b a 5)
   c: d bool (b a 5)
   d: e bool true
   e: e mumble (b c 0)
   f: e bool (b c 0)
   g: c

   A: b, c, d, e, g
*)

(* Exercise: 2 stars, optional (baz_num_elts) *)

Inductive baz : Type :=
  | x : baz -> baz
  | y : baz -> bool -> baz.

(* It has exactly two, x and y, since you cannot create more. *)

End MumbleBaz.

(* Exercise: 4 stars, recommended (forall_exists_challenge) *)

Fixpoint forallb {X: Type} (f : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | h :: t => andb (f h) (forallb f t)
  end.

Example forallb1 : forallb oddb [1,3,5,7,9] = true.
Proof. reflexivity. Qed.
Example forallb2 : forallb negb [false,false] = true.
Proof. reflexivity. Qed.
Example forallb3 : forallb evenb [0,2,4,5] = false.
Proof. reflexivity. Qed.
Example forallb4 : forallb (beq_nat 5) [] = true.
Proof. reflexivity. Qed.

Fixpoint existsb {X: Type} (f : X -> bool) (l : list X) : bool :=
  match l with
    | [] => false
    | h :: t => orb (f h) (existsb f t)
  end.

Example existsb1 : existsb (beq_nat 5) [0,2,3,6] = false.
Proof. reflexivity. Qed.
Example existsb2 : existsb (andb true) [true,true,false] = true.
Proof. reflexivity. Qed.
Example existsb3 : existsb oddb [1,0,0,0,0,3] = true.
Proof. reflexivity. Qed.
Example existsb4 : existsb evenb [] = false.
Proof. reflexivity. Qed.

Definition existsb' {X:Type} (f : X -> bool) (l : list X) : bool :=
  negb (forallb (fun n => negb (f n)) l).

Theorem existsb_existsb' :
  forall (X : Type) (f : X -> bool) (l : list X),
    existsb f l = existsb' f l.
Proof.
  intros X f l.
  induction l as [ | n l' ].

  Case "l = []".
  unfold existsb.
  unfold existsb'.
  unfold forallb.
  unfold negb.
  reflexivity.

  Case "l = n :: l'".
  unfold existsb.
  fold @existsb.
  rewrite -> IHl'.
  unfold existsb'.
  unfold forallb.
  fold @forallb.
  destruct (forallb (fun n0 : X => negb (f n0)) l').

  SCase "forallb... = true".
  unfold negb.
  unfold orb.
  destruct (f n).

  SSCase "(f n) = true".
  unfold andb.
  reflexivity.

  SSCase "(f n) = false".
  reflexivity.

  SCase "forallb... = false".
  destruct (f n).

  SSCase "(f n) = true".
  unfold negb.
  unfold andb.
  unfold orb.
  reflexivity.

  SSCase "(f n) = false".
  unfold negb.
  unfold andb.
  unfold orb.
  reflexivity.
Qed.

(* Exercise: 2 stars, optional (index_informal) *)

(* TODO *)

(* end-of-Poly.v *)