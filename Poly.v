Module Poly.

Inductive list (X : Type) : Type :=
  | nil : list X
  | cons : X -> list X -> list X.

Arguments nil {X}.
Arguments cons {X} _ _.

Fixpoint repeat {X : Type} (x : X) (n : nat) : (list X) :=
  match n with
  | 0 => nil
  | S n' => cons x (repeat x n')
  end.

Check repeat.
Example repeat_1 : repeat 3 3 = cons 3 ( cons 3 ( cons 3 (nil) )).
Proof. reflexivity. Qed.

Example test_repeat2 :
  repeat false 1 = cons false (nil).
Proof. reflexivity. Qed.

Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
    | nil => l2
    | cons h xs => cons h (app xs l2)
  end.

Example app_1 : app (cons 1 (cons 2 ( cons 3 nil))) (cons 4 (cons 5 nil)) = (cons 1 (cons 2 (cons 3 ( cons 4 ( cons 5 nil))))).
Proof. reflexivity. Qed.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil => nil
  | cons h t => app (rev t) (cons h nil)
  end.
Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.
Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.
Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

Definition mynil : list nat := nil.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Definition list123''' := [1; 2; 3].

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros l.
  induction l0.
  reflexivity.
  simpl.
  rewrite -> IHl0.
  reflexivity.
Qed.

Theorem app_nil_l : forall (X:Type), forall l: list X,
  [] ++ l = l.
Proof. reflexivity. Qed.


Theorem app_assoc : forall (A : Type) (l m n : list A),
 l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n.
  induction l.
  simpl.
  reflexivity.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.

Lemma app_length : forall (A : Type) (l1 l2 : list A),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros A l1 l2.    
  (* length (l1 ++ l2) = length l1 + length l2 *)
  induction l1. 
  (* length ([ ] ++ l2) = length [ ] + length l2 *)
  simpl. 
  (* length l2 = length l2 *)
  reflexivity.
  (* length ((x :: l1) ++ l2) = length (x :: l1) + length l2 *)
  simpl.
  (* S (length (l1 ++ l2)) = S (length l1 + length l2) *) 
  (* IHl1 : length (l1 ++ l2) = length l1 + length l2 *)
  rewrite <- IHl1.
  (* S (length (l1 ++ l2)) = S (length (l1 ++ l2)) *)
  reflexivity.
Qed.

Theorem rev_app_distr : forall (X : Type) (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2.
  induction l1.
  (* rev ([ ] ++ l2) = rev [ ] ++ rev l2 *)
  simpl.
  rewrite -> app_nil_r.
  reflexivity.
  (* rev ((x :: l1) ++ l2) = rev (x :: l1) ++ rev l2 *)
  simpl.
  rewrite -> IHl1.
  rewrite <- app_assoc.
  reflexivity.
Qed.

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l.
  induction l.
  reflexivity.
  simpl.
  rewrite -> rev_app_distr. 
  rewrite -> IHl.
  reflexivity.
Qed.