Require Export Induction.
Module NatList.

Inductive natprod : Type :=
| pair : nat -> nat -> natprod.

Check (pair 3 5).

Notation "( x , y )" := (pair x y).

Definition fst (p : natprod) : nat :=
  match p with
   | (x,y) => x
  end.

Example fst_eq_3: fst (pair 3 5) = 3.

Definition snd (p : natprod) : nat :=
  match p with
   | (x,y) => y
  end.

Example snd_eq_5: fst (pair 3 5) = 5.

Compute (fst (pair 3 5)).

Definition swap_pair (p : natprod) : natprod :=
  match p with
    | (x,y) => (y,x)
  end.

Example swap_pair_test: swap_pair (3, 2) = (2, 3).

Theorem surjective_pairing' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  simpl. reflexivity.
Qed.

Theorem surjective_pairing: forall p : natprod,
  p = (fst p, snd p).
Proof.
  intros p. destruct p. simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap: forall p : natprod,
  (snd p, fst p) = swap_pair p.
Proof.
  intros p. destruct p as [x y]. simpl. reflexivity.
Qed. 

Theorem fst_swap_is_snd : forall (p : natprod),
  fst (swap_pair p) = snd p.
Proof.
 intros p. destruct p as [x y]. simpl. reflexivity.
Qed.

Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

Definition mylist := cons 1 (cons 2 (cons 3 nil)).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].

Fixpoint repeat (n count : nat) : natlist :=
  match count with
   | 0 => []
   | S count' => n :: (repeat n count')
  end.

Example repeat_42_3: repeat 42 3 = [42; 42; 42].

Fixpoint length (l:natlist) : nat :=
  match l with
   | [] => 0
   | _ :: xs  => 1 + (length xs)
  end.

Example length_3: length [1; 2; 3] = 3.

Fixpoint app (l1 l2 : natlist) : natlist :=
 match l1 with
  | [] => l2
  | h :: xs => h :: (app xs l2)
 end.

Example append_ex1: app [1; 2] [3; 4; 5] = [1; 2; 3; 4; 5]. 

Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.
Example test_app2: nil ++ [4;5] = [4;5].
Proof. reflexivity. Qed.
Example test_app3: [1;2;3] ++ nil = [1;2;3].
Proof. reflexivity. Qed.

Definition hd (default:nat) (l:natlist) : nat :=
  match l with
  | [] => default
  | h :: _ => h
  end.

Definition tl (l:natlist) : natlist :=
  match l with
  | [] => []
  | _ :: xs => xs
  end.

Example test_hd1: hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.
Example test_hd2: hd 0 [] = 0.
Proof. reflexivity. Qed.
Example test_tl: tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l:natlist) : natlist :=
  match l with
  | [] => []
  | 0 :: xs => nonzeros xs
  | h :: xs => h :: nonzeros xs
  end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].

Inductive natlistprod : Type :=
  pairl : natlist -> natlist -> natlistprod.

Notation "( x , y )" := (pairl x y).

Fixpoint alternate (l1 l2 : natlist) : natlist :=
  match (l1, l2) with
    | (nil, _) => l2
    | (_, nil) => l1
    | (h1 :: t1, h2 :: t2) => h1 :: h2 :: alternate t1 t2
  end.

Example test_alternate1:
  alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.

Example test_alternate2:
  alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.

Example test_alternate3:
  alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.

Example test_alternate4:
  alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.

Definition bag := natlist.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
   | [] => 0
   | x :: xs => match beq_nat x v with
                | true =>  1 + (count v xs) 
                | false => count v xs
                end
  end.

Example test_count1: count 1 [1;2;3;1;4;1] = 3.
   Proof. reflexivity. Qed.

Example test_count2: count 6 [1;2;3;1;4;1] = 0.
    Proof. reflexivity. Qed.

Definition sum : bag -> bag -> bag := app.

Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
 v :: s.
  
  
Example test_add1: count 1 (add 1 [1;4;1]) = 3.
 Proof. reflexivity. Qed.
Example test_add2: count 5 (add 1 [1;4;1]) = 0.
 Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  match count v s with
   | 0 => false
   | _ => true
  end.

Example test_member1: member 1 [1;4;1] = true.
 Proof. reflexivity. Qed.

Example test_member2: member 2 [1;4;1] = false.
 Proof. reflexivity. Qed.

Fixpoint remove_one (v:nat) (s:bag) : bag :=
  (* When remove_one is applied to a bag without the number to remove,
     it should return the same bag unchanged. *)
  match s with
    | nil => nil
    | h :: tl => match (beq_nat h v) with
                   | true => tl
                   | false => h :: remove_one v tl
                 end
  end.

Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity. Qed.

Fixpoint remove_all (v:nat) (s:bag) : bag :=
  match s with
    | nil => nil
    | h :: t => match (beq_nat h v) with
                   | true => remove_all v t
                   | false => h :: remove_all v t
                 end
  end.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity. Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity. Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity. Qed.

Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
   | [] => true
   | x :: xs => andb  (member x s2) (subset xs (remove_one x s2)) 
  end.

Example test_subset1:              (subset [1;2] [2;1;4;1]) = true.
Proof. reflexivity. Qed.
Example test_subset2:              subset [1;2;2] [2;1;4;1] = false.
Proof. reflexivity. Qed.

Theorem nil_app : forall l:natlist,
  [] ++ l = l.
Proof. reflexivity. Qed.

Theorem tl_length_pred : forall l:natlist,
  pred (length l) = length (tl l).
Proof.
  intros l. destruct l as [| n l'].
  - (* l = nil *)
    reflexivity.
  - (* l = cons n l' *)
    reflexivity. Qed.

Theorem app_assoc : forall l1 l2 l3 : natlist,
  (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
 intros l1 l2 l3. induction l1 as [|n1' l1' IHl1'].
 simpl. reflexivity.
 simpl. rewrite -> IHl1'. reflexivity.
Qed.

Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

Example test_rev1: rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.
Example test_rev2: rev nil = nil.
Proof. reflexivity. Qed.

Lemma app_length : forall l1 l2 : natlist,
  length (l1 ++ l2) = (length l1) + (length l2).
Proof.
 intros l1 l2. induction l1 as [| n' l1' Hl1'].
 simpl. reflexivity.
 simpl. rewrite -> Hl1'. reflexivity.
Qed.

Theorem rev_length_firsttry : forall l : natlist,
  length (rev l) = length l.
Proof.
 intros l. induction l as [| n' l' IHl'].
  reflexivity.
 simpl. rewrite -> app_length. 
 rewrite -> IHl'. simpl. rewrite -> plus_comm. reflexivity.
Qed.

Theorem app_nil_r : forall l : natlist,
  l ++ [] = l.
Proof.
  intros l. induction l as [| n' l' IHl'].
  reflexivity.
  simpl. rewrite -> IHl'.  reflexivity.
Qed.

Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2. induction l1.
  rewrite -> nil_app.
  assert (H1: rev [] = []). { reflexivity. }
  rewrite -> H1. 
  rewrite -> app_nil_r.
  reflexivity.
  simpl.
  rewrite -> IHl1.
  rewrite -> app_assoc. reflexivity.
Qed.

Theorem rev_involutive : forall l : natlist,
  rev (rev l) = l.
Proof.
  intros l. induction l.
  simpl. reflexivity.
  simpl. rewrite -> rev_app_distr.
  rewrite -> IHl.
  simpl. reflexivity.
Qed.

Theorem app_assoc4 : forall l1 l2 l3 l4 : natlist,
  l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
Proof.
 intros l1 l2 l3 l4.
 rewrite -> app_assoc.
 rewrite <- app_assoc.
 reflexivity.
Qed.

Lemma nonzeros_app : forall l1 l2 : natlist,
nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
Proof.
  intros l1 l2.
  induction l1.
  reflexivity.
  simpl.
  destruct n.
  rewrite -> IHl1. reflexivity.
  simpl. rewrite -> IHl1. reflexivity.
Qed.

