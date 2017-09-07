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
  simpl.
  induction l.
Qed.
