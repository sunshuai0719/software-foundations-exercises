(* File: Lists.v *)
(* Title: Lists - Data Structures in Coq *)
(* Author: Peter Urbak <peteru@dragonwasrobot.com *)
(* Version: 2011-06-21 *)

Require Export Basics.

Module NatList.

(* Pairs of Numbers *)

Inductive natprod : Type :=
  pair : nat -> nat -> natprod.

Definition fst (p : natprod) : nat :=
  match p with
    | pair x y => x
  end.

Definition snd (p : natprod) : nat :=
  match p with
    | pair x y => y
  end.

Notation "( x , y )" := (pair x y).

Eval simpl in (fst (3,4)).

Definition fst' (p : natprod) : nat :=
  match p with
    (x,y) => x
  end.

Definition snd' (p : natprod) : nat :=
  match p with
    (x,y) => y
  end.

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  intros n m.
  unfold fst.
  unfold snd.
  reflexivity.
Qed.

Theorem surjective_pairing : forall (p : natprod),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p as (n, m).
  unfold fst.
  unfold snd.
  reflexivity.
Qed.

(* Exercise: 1 star (snd_fst_is_swap) *)

Theorem snd_fst_is_swap : forall (p : natprod),
  (snd p, fst p) = swap_pair p.
Proof.
  intros p.
  destruct p as (n, m).
  unfold swap_pair.
  unfold snd.
  unfold fst.
  reflexivity.
Qed.

(* Exercise: 1 star, optional (fst_swap_is_snd) *)

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
  intros p.
  destruct p as (n, m).
  unfold swap_pair.
  unfold fst.
  unfold snd.
  reflexivity.
Qed.

(* Lists of Numbers *)

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition l_123 := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l " := (cons x l) (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x , .. , y ]" := (cons x .. (cons y nil) ..).

Definition l_123' := 1 :: (2 :: (3 :: nil)).
Definition l_123'' := 1 :: 2 :: 3 :: nil.
Definition l_123''' := [1,2,3].

(* Added the ' on repeat to avoid wrong syntax highlighting in emacs. *)
Fixpoint repeat' (n count : nat) : natlist :=
  match count with
    | O => nil
    | S count' => n :: (repeat' n count')
  end.

Fixpoint length (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => S (length t)
  end.

Fixpoint app (l1 l2 : natlist) : natlist :=
  match l1 with
    | nil => l2
    | h :: t => h :: (app t l2)
  end.

Notation "x ++ y" := (app x y) (at level 60, right associativity).

Example test_app1 : [1,2,3] ++ [4,5] = [1,2,3,4,5].
Proof. unfold app. reflexivity. Qed.

Example test_app2 : nil ++ [4,5] = [4,5].
Proof. unfold app. reflexivity. Qed.

Example test_app3 : [1,2,3] ++ nil = [1,2,3].
Proof. unfold app. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat :=
  match l with
    | nil => default
    | h :: t => h
  end.

Definition tail (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => t
  end.

Example test_hd1 : hd 0 [1,2,3] = 1.
Proof. unfold hd. reflexivity. Qed.

Example test_hd2 : hd 0 [] = 0.
Proof. unfold hd. reflexivity. Qed.

Example test_tail : tail [1,2,3] = [2,3].
Proof. unfold tail. reflexivity. Qed.

(* Exercise: 2 stars, recommended (list_funs) *)

Fixpoint nonzeros (l : natlist) : natlist :=
  match l with
    | nil => nil
    | O :: t => (nonzeros t)
    | h :: t => h :: (nonzeros t)
  end.

Example test_nonzeros : nonzeros [0,1,0,2,3,0,0] = [1,2,3].
Proof. unfold nonzeros. reflexivity. Qed.

Fixpoint oddmembers (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => match (evenb h) with
                  | true => (oddmembers t)
                  | false => h :: (oddmembers t)
                end
  end.

Example test_oddmembers : oddmembers [0,1,0,2,3,0,0] = [1,3].
Proof. unfold oddmembers. unfold evenb. reflexivity. Qed.

Fixpoint countoddmembers (l : natlist) : nat :=
  match l with
    | nil => O
    | h :: t => match (evenb h) with
                  | true => (countoddmembers t)
                  | false => S (countoddmembers t)
                end
  end.

Example test_countoddmembers1: countoddmembers [1,0,3,1,4,5] = 4.
Proof. unfold countoddmembers. unfold evenb. reflexivity. Qed.

Example test_countoddmembers2: countoddmembers [0,2,4] = 0.
Proof. unfold countoddmembers. unfold evenb. reflexivity. Qed.

Example test_countoddmembers3: countoddmembers nil = 0.
Proof. unfold countoddmembers. unfold evenb. reflexivity. Qed.

(* Exercise: 2 stars (alternate) *)

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match l1, l2 with
    | nil, l2 => l2
    | l1, nil => l1
    | h1 :: t1, h2 :: t2 => h1 :: h2 :: (alternate t1 t2)
  end.

Lemma unfold_alternate_inductive_case : forall (h1 h2 : nat) (t1 t2 : natlist),
  alternate (h1 :: t1) (h2 :: t2) = h1 :: h2 :: (alternate t1 t2).
Proof.
  intros h1 h2 t1 t2.
  unfold alternate.
  fold alternate.
  reflexivity.
Qed.

Example test_alternate1 : alternate [1,2,3] [4,5,6] = [1,4,2,5,3,6].
Proof. unfold alternate. reflexivity. Qed.
Example test_alternate2: alternate [1] [4,5,6] = [1,4,5,6].
Proof. unfold alternate. reflexivity. Qed.
Example test_alternate3: alternate [1,2,3] [4] = [1,4,2,3].
Proof. unfold alternate. reflexivity. Qed.
Example test_alternate4: alternate [] [20,30] = [20,30].
Proof. unfold alternate. reflexivity. Qed.

(* Bags via Lists *)

Definition bag := natlist.

(* Exercise: 3 stars (bag_functions) *)

Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => O
    | h :: t => match (beq_nat h v) with
                  | true => S (count v t)
                  | false => (count v t)
                end
    end.

Lemma unfold_count_inductive_case : forall (v h : nat) (t : bag),
  count v (h :: t) = match (beq_nat h v) with
                       | true => S (count v t)
                       | false => (count v t)
                     end.
Proof.
  intros v h t.
  unfold count.
  fold count.
  reflexivity.
Qed.

Example test_count1: count 1 [1,2,3,1,4,1] = 3.
Proof. unfold count. unfold beq_nat. reflexivity. Qed.
Example test_count2: count 6 [1,2,3,1,4,1] = 0.
Proof. unfold count. unfold beq_nat. reflexivity. Qed.

Definition sum : bag -> bag -> bag :=
  alternate.

Lemma sum_eq_alternate : sum = alternate.
Proof. unfold sum. reflexivity. Qed.

Example test_sum1: count 1 (sum [1,2,3] [1,4,1]) = 3.
Proof. unfold sum. unfold alternate. unfold count.
unfold beq_nat. reflexivity. Qed.

Definition add (v : nat) (s : bag) : bag :=
  app [v] s.

Example test_add1 : count 1 (add 1 [1,4,1]) = 3.
Proof. unfold add. unfold app. unfold count.
unfold beq_nat. reflexivity. Qed.
Example test_add2 : count 5 (add 1 [1,4,1]) = 0.
Proof. unfold add. unfold app. unfold count.
unfold beq_nat. reflexivity. Qed.

Definition member (v : nat) (s : bag) : bool :=
  blt_nat O (count v s).

Example test_member1 : member 1 [1,4,1] = true.
Proof. unfold member. unfold count. unfold beq_nat.
unfold blt_nat. unfold ble_nat. unfold beq_nat.
unfold negb. unfold andb. reflexivity. Qed.

Example test_member1' : member 1 [1,4,1] = true.
Proof. reflexivity. Qed.

Example test_member2 : member 2 [1,4,1] = false.
Proof. unfold member. unfold count. unfold beq_nat.
unfold blt_nat. unfold ble_nat. unfold beq_nat.
unfold negb. unfold andb. reflexivity. Qed.

Example test_member2' : member 2 [1,4,1] = false.
Proof. reflexivity. Qed.

(* Exercise: 3 stars, optional (bag_more_functions) *)

Fixpoint remove_one (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | h :: t => match (beq_nat v h) with
                  | true => t
                  | false => h :: (remove_one v t)
                end
  end.

Example test_remove_one1: count 5 (remove_one 5 [2,1,5,4,1]) = 0.
Proof. unfold remove_one. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Example test_remove_one2: count 5 (remove_one 5 [2,1,4,1]) = 0.
Proof. unfold remove_one. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Example test_remove_one3: count 4 (remove_one 5 [2,1,4,5,1,4]) = 2.
Proof. unfold remove_one. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Example test_remove_one4:
  count 5 (remove_one 5 [2,1,5,4,5,1,4]) = 1.
Proof. unfold remove_one. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
  match s with
    | nil => nil
    | h :: t => match (beq_nat v h) with
                  | true => (remove_all v t)
                  | false => h :: (remove_all v t)
                end
  end.

Example test_remove_all1: count 5 (remove_all 5 [2,1,5,4,1]) = 0.
Proof. unfold remove_all. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Example test_remove_all2: count 5 (remove_all 5 [2,1,4,1]) = 0.
Proof. unfold remove_all. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Example test_remove_all3: count 4 (remove_all 5 [2,1,4,5,1,4]) = 2.
Proof. unfold remove_all. unfold beq_nat. unfold count. unfold beq_nat.
reflexivity. Qed.

Example test_remove_all4: count 5 (remove_all 5 [2,1,5,4,5,1,4,5,1,4]) = 0.
Proof. reflexivity. Qed.
(* From now on I won't do all the unfolding for Examples unless I feel it is
   important for the particular example. *)

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | nil => true
    | h :: t => match member h s2 with
                  | true => (subset t (remove_one h s2))
                  | false => false
                end
    end.

Example test_subset1: subset [1,2] [2,1,4,1] = true.
Proof. reflexivity. Qed.

Example test_subset2: subset [1,2,2] [2,1,4,1] = false.
Proof.  reflexivity. Qed.

(* Exercise: 3 stars, recommended (bag_theorem) *)

(* Hmm, will simply show that count increment when another of the element type
   being looked for is added to the list. *)

Theorem bag_theorem : forall (v : nat) (s : bag),
  count v (add v s) = S (count v s).
Proof.
  intros v s.
  unfold add.
  unfold app.
  unfold count.
  fold count.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

(* Reasoning about Lists *)

Theorem nil_app : forall (l : natlist),
  [] ++ l = l.
Proof.
  intro l.
  unfold app.
  reflexivity.
Qed.

Theorem tl_length_pred : forall (l : natlist),
  pred (length l) = length (tail l).
Proof.
  intro l.
  destruct l as [ | l' ].

  Case "l = nil".
  unfold tail.
  unfold length.
  unfold pred.
  reflexivity.

  Case "l = cons n l'".
  unfold tail.
  unfold pred.
  unfold length.
  reflexivity.
Qed.

(* Induction on Lists *)

Theorem app_ass : forall (l1 l2 l3 : natlist),
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
  intros l1 l2 l3.
  induction l1 as [ | n l1' ].

  Case "l1 = nil".
  unfold app.
  fold app.
  reflexivity.

  Case "l1 = cons n l1'".
  unfold app.
  fold app.
  rewrite -> IHl1'.
  reflexivity.
Qed.

Theorem app_length : forall (l1 l2 : natlist),
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
  intros l1 l2.
  induction l1 as [ | n l1' ].

  Case "l1 = nil".
  unfold app.
  unfold length.
  fold length.
  unfold plus.
  reflexivity.

  Case "l1 = cons n l1'".
  unfold app.
  fold app.
  unfold length.
  fold length.
  rewrite -> IHl1'.
  rewrite -> plus_Sn_m.
  reflexivity.
Qed.

Fixpoint snoc (l : natlist) (v : nat) : natlist :=
  match l with
    | nil => [v]
    | h :: t => h :: (snoc t v)
  end.

Fixpoint rev (l : natlist) : natlist :=
  match l with
    | nil => nil
    | h :: t => snoc (rev t) h
  end.

Example test_rev1: rev [1,2,3] = [3,2,1].
Proof. reflexivity. Qed.

Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Theorem length_snoc : forall (n : nat), forall (l : natlist),
  length (snoc l n) = S (length l).
Proof.
  intros n l.
  induction l as [ | n' l' ].

  Case "l = nil".
  unfold snoc.
  unfold length.
  reflexivity.

  Case "l = cons n' l'".
  unfold snoc.
  fold snoc.
  unfold length.
  fold length.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem rev_length : forall (l : natlist),
  length (rev l) = length l.
Proof.
  intro l.
  induction l as [ | n l' ].

  Case "l = nil".
  unfold rev.
  unfold length.
  reflexivity.

  Case "l = cons n l'".
  unfold rev.
  fold rev.
  unfold length.
  fold length.
  rewrite -> length_snoc.
  rewrite -> IHl'.
  reflexivity.
Qed.

(* List Exercises, Part 1 *)

(* Exercise: 3 stars, recommended (list_exercises) *)

Theorem app_nil_end : forall (l : natlist),
  l ++ [] = l.
Proof.
  intro l.
  induction l as [ | n l' ].

  Case "l = nil".
  unfold app.
  reflexivity.

  Case "l = cons n l'".
  unfold app.
  fold app.
  rewrite -> IHl'.
  reflexivity.
Qed.

Lemma unfold_app_inductive_case : forall (h : nat) (t l : natlist),
  app (h :: t) l = h :: (app t l).
Proof.
  intros h t l.
  unfold app.
  fold app.
  reflexivity.
Qed.

Lemma unfold_snoc_inductive_case : forall (h n : nat) (t : natlist),
  snoc (h :: t) n = h :: (snoc t n).
Proof.
  intros h n l.
  unfold snoc.
  fold snoc.
  reflexivity.
Qed.

Lemma unfold_rev_inductive_case : forall (h : nat) (t : natlist),
  rev (h :: t) = snoc (rev t) h.
Proof.
  intros h t.
  unfold rev.
  fold rev.
  reflexivity.
Qed.

Lemma rev_snoc : forall (n : nat) (l : natlist),
  rev (snoc l n) = n :: (rev l).
Proof.
  intros n l.
  induction l as [ | n' l' ].
  unfold rev.
  unfold snoc.
  reflexivity.

  unfold snoc.
  fold snoc.
  unfold rev.
  fold rev.
  rewrite -> IHl'.
  unfold snoc.
  fold snoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall (l : natlist),
  rev (rev l) = l.
Proof.
  intro l.
  induction l as [ | n l' ].

  Case "l = nil".
  unfold rev.
  reflexivity.

  Case "l = cons n l'".
  rewrite -> unfold_rev_inductive_case.
  rewrite -> rev_snoc.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem snoc_append : forall (n : nat) (l : natlist),
  snoc l n = l ++ [n].
Proof.
  intros n l.
  induction l as [ | n' l' ].

  Case "l = nil".
  unfold app.
  unfold snoc.
  reflexivity.

  Case "l = cons n' l'".
  rewrite -> unfold_snoc_inductive_case.
  rewrite -> unfold_app_inductive_case.
  rewrite -> IHl'.
  reflexivity.
Qed.

Theorem distr_rev : forall (l1 l2 : natlist),
  rev (l1 ++ l2) = (rev l2) ++ (rev l1).
Proof.
  intros l1 l2.
  induction l1 as [ | n l' ].

  Case "l1 = nil".
  unfold rev.
  fold rev.
  rewrite -> app_nil_end.
  unfold app.
  reflexivity.

  Case "l2 = cons n l'".
  rewrite -> unfold_app_inductive_case.
  rewrite -> unfold_rev_inductive_case.
  rewrite -> snoc_append.
  rewrite -> IHl'.
  rewrite -> unfold_rev_inductive_case.
  rewrite -> snoc_append.
  rewrite -> app_ass.
  reflexivity.
Qed.

Theorem app_ass4 : forall (l1 l2 l3 l4 : natlist),
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
  intros l1 l2 l3 l4.
  rewrite -> app_ass.
  rewrite -> app_ass.
  reflexivity.
Qed.

Lemma nonzeros_length : forall (l1 l2 : natlist),
  nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1 as [ | n l1'].

  Case "l1 = nil".
  unfold app at 1.
  unfold nonzeros at 2.
  unfold app at 1.
  reflexivity.

  Case "l1 = cons n l1'".
  rewrite -> unfold_app_inductive_case.
  unfold nonzeros.
  fold nonzeros.
  rewrite -> IHl1'.
  case n.

  SCase "n = O".
  reflexivity.

  SCase "n = S n'".
  intros n'.
  reflexivity.
Qed.

(* List Exercises, Part 2 *)

(* Exercise: 2 stars, recommended (list_design) *)

Theorem cons_snoc : forall (h n : nat) (t : natlist),
  (cons h t) ++ [n] = [h] ++ (snoc t n).
Proof.
  intros h n t.
  rewrite -> unfold_app_inductive_case.
  rewrite -> unfold_app_inductive_case.
  rewrite -> snoc_append.
  unfold app at 2.
  reflexivity.
Qed.

(* Exercise: 2 stars, optional (bag_proofs) *)

Theorem count_member_nonzero : forall (s : bag),
  ble_nat 1 (count 1 (1 :: s)) = true.
Proof.
  intro s.
  induction s as [ | n s' ].

  Case "s = nil".
  unfold count.
  unfold beq_nat.
  unfold ble_nat.
  reflexivity.

  Case "s = cons n s'".
  unfold count.
  fold count.
  unfold beq_nat.
  fold beq_nat.
  case (beq_nat n 1).

  SCase "(beq_nat n 1) = true".
  unfold ble_nat.
  reflexivity.

  SCase "(beq_nat n 1) = false".
  unfold ble_nat.
  reflexivity.
Qed.

Theorem ble_nat_refl : forall n,
  ble_nat n n = true.
Proof.
  intro n.
  induction n as [ | n' ].

  Case "n = O".
  unfold ble_nat.
  reflexivity.

  Case "n = S n'".
  unfold ble_nat.
  fold ble_nat.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem ble_n_Sn : forall n,
  ble_nat n (S n) = true.
Proof.
  intros n.
  induction n as [ | n' ].

  Case "n = O".
  unfold ble_nat.
  reflexivity.

  Case "n = S n'".
  unfold ble_nat.
  fold ble_nat.
  rewrite -> IHn'.
  reflexivity.
Qed.

Theorem remove_decreases_count : forall (s : bag),
  ble_nat (count O (remove_one O s)) (count O s) = true.
Proof.
  intro s.
  induction s as [ | n s' ].

  Case "s = nil".
  unfold remove_one.
  unfold count.
  unfold ble_nat.
  reflexivity.

  Case "s = cons n s'".
  unfold remove_one.
  fold remove_one.
  case (beq_nat 0 n).

  SCase "(beq_nat 0 n) = true".
  unfold count.
  fold count.
  case (beq_nat n 0).

  SSCase "(beq_nat n 0) = true".
  rewrite -> ble_n_Sn.
  reflexivity.

  SSCase "(beq_nat n 0) = false".
  rewrite -> ble_nat_refl.
  reflexivity.

  SCase "(beq_nat 0 n) = false".
  unfold count.
  fold count.
  case (beq_nat n 0).

  SSCase "(beq_nat n 0) = true".
  unfold count.
  fold count.
  unfold ble_nat.
  fold ble_nat.
  rewrite -> IHs'.
  reflexivity.

  SSCase "(beq_nat n 0) = false".
  rewrite -> IHs'.
  reflexivity.
Qed.
(* Hmm, a bit long, maybe it can be done simpler without all the subcases. *)

(* Exercise: 3 stars, optional (bag_count_sum) *)

Theorem bag_count_sum : forall (n : nat) (s1 s2 : bag),
  (count n s1) + (count n s2) = count n (sum s1 s2).
Proof.
  Admitted. (* TODO *)

(* Exercise: 4 stars, optional (rev_injective) *)

Theorem rev_injective : forall (l1 l2 : natlist), rev l1 = rev l2 -> l1 = l2.
Proof.
  intros l1 l2.
  intro H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite -> rev_involutive.
  reflexivity.
Qed.

(* Options *)

Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

Fixpoint index (n : nat) (l : natlist) : natoption :=
  match l with
    | nil => None
    | a :: l' => match beq_nat n O with
                   | true => Some a
                   | false => index (pred n) l'
                 end
    end.

Example test_index1 : index 0 [4,5,6,7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 3 [4,5,6,7] = Some 7.
Proof. reflexivity. Qed.
Example test_index3 : index 10 [4,5,6,7] = None.
Proof. reflexivity. Qed.

Fixpoint index' (n : nat) (l : natlist) : natoption :=
  match l with
    | nil => None
    | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Definition option_elim (d : nat) (o : natoption) : nat :=
  match o with
    | Some n' => n'
    | None => d
  end.

(* Exercise: 2 stars (hd_opt) *)

Definition hd_opt (l : natlist) : natoption :=
  match l with
    | nil => None
    | h :: t => Some h
  end.

Example test_hd_opt1 : hd_opt [] = None.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [1] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt3 : hd_opt [5,6] = Some 5.
Proof. reflexivity. Qed.

(* Exercise: 2 stars, optional (option_elim_hd) *)

Theorem option_elim_hd : forall (l : natlist) (default : nat),
  hd default l = option_elim default (hd_opt l).
Proof.
  intros l default.
  induction l as [ | n l' ].

  Case "l = nil".
  unfold hd_opt.
  unfold option_elim.
  unfold hd.
  reflexivity.

  Case "l = cons n l'".
  unfold hd_opt.
  unfold option_elim.
  unfold hd.
  reflexivity.
Qed.

(* Exercise: 2 stars, recommended (beq_natlist) *)

Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
  match l1, l2 with
    | nil, nil => true
    | (h1 :: t1), (h2 :: t2) => if beq_nat h1 h2 then (beq_natlist t1 t2) else false
    | _, _ => false
    end.

Example test_beq_natlist1 : (beq_natlist nil nil = true).
Proof. reflexivity. Qed.
Example test_beq_natlist2 : beq_natlist [1,2,3] [1,2,3] = true.
Proof. reflexivity. Qed.
Example test_beq_natlist3 : beq_natlist [1,2,3] [1,2,4] = false.
Proof. reflexivity. Qed.

Theorem beq_natlist_refl : forall (l : natlist),
  true = beq_natlist l l.
Proof.
  intro l.
  induction l as [ | n l' ].

  Case "l = nil".
  unfold beq_natlist.
  reflexivity.

  Case "l = cons n l'".
  unfold beq_natlist.
  fold beq_natlist.
  rewrite <- beq_nat_refl.
  rewrite <- IHl'.
  reflexivity.
Qed.

(* Extended Exercise: Dictionaries *)

Module Dictionary.

Inductive dictionary : Type :=
  | empty : dictionary
  | record : nat -> nat -> dictionary -> dictionary.

Definition insert (key value : nat) (d : dictionary) : dictionary :=
  (record key value d).

Fixpoint find (key : nat) (d : dictionary) : natoption :=
  match d with
    | empty => None
    | record k v d' => if (beq_nat k key) then (Some v) else (find key d')
  end.

(* Exercise: 1 star (dictionary_invariant1) *)

Theorem dictionary_invariant1 : forall (d : dictionary) (k v : nat),
  (find k (insert k v d)) = Some v.
Proof.
  intros d k v.
  induction d as [ | k' v' d' ].

  Case "d = empty".
  unfold insert.
  unfold find.
  rewrite <- beq_nat_refl.
  reflexivity.

  Case "d = (record k' v' d')".
  unfold insert.
  unfold find.
  fold find.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

(* Exercise: 1 star (dictionary_invariant2) *)

(* took the liberity of writing 'beq_nat n m' instead of 'beq_nat m n' so I
   didn't have to prove beq_nat n m = beq_nat m n. *)
Theorem dictionary_invariant2 : forall (d : dictionary) (m n o : nat),
  (beq_nat n m) = false -> (find m d) = (find m (insert n o d)).
Proof.
  intros d m n o.
  intro H.
  induction d as [ | n' o' d' ].

  Case "d = empty".
  unfold insert.
  unfold find.
  rewrite -> H.
  reflexivity.

  Case "d = (record n' o' d')".
  unfold insert.
  unfold find.
  fold find.
  rewrite -> H.
  reflexivity.
Qed.

End Dictionary.

End NatList.

(* end-of-Lists.v *)
