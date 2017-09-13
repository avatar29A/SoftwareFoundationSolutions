Require Export Basics.
Require Export List.

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

Fixpoint snoc {X:Type} (l:list X) (v:X) : (list X) :=
  match l with
  | nil      => cons v (nil)
  | cons h t => cons h (snoc t v)
  end.

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

(* ###################################################### *)
(** ** Polymorphic Pairs *)

(** Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_ (or _products_): *)

(* ###################################################### *)
(** ** Polymorphic Pairs *)

(** Following the same pattern, the type definition we gave in
    the last chapter for pairs of numbers can be generalized to
    _polymorphic pairs_ (or _products_): *)

Inductive prod (X Y : Type) : Type :=
  | pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.

Notation "( x , y )" := (pair x y).
Notation " X * Y " := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, _) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (_, y) => y
  end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match lx, ly with
    | [], _ => []
    | _, [] => []
    |   x :: xs, y :: ys => (x, y) :: (combine xs ys)
  end.

Compute combine [1; 2] [3; 4].
Compute combine [1; 2] [3; 4; 5].

Check @combine.

Compute (combine [1;2] [false;false;true;true]).

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y) :=
  match l with
  | [] => (nil, nil)
  | (x, y) :: xs => (x :: fst (split xs), y :: snd (split xs))
  end.



Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof. reflexivity. Qed.

(* ###################################################### *)
(** ** Polymorphic Options *)

(** One last polymorphic type for now: _polymorphic options_.
    The type declaration generalizes the one for [natoption] in the
    previous chapter: *)

Inductive option (X:Type) : Type :=
  | Some : X -> option X
  | None : option X.

Arguments Some {X} _.
Arguments None {X}.

(** *** *)
(** We can now rewrite the [index] function so that it works
    with any type of lists. *)

Fixpoint beq_nat (n m : nat) : bool := 
  match n, m with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S n1, S m1 => beq_nat n1 m1
  end.


Fixpoint index {X : Type} (n : nat)
               (l : list X) : option X :=
  match l with
  | [] => None
  | a :: l' => if beq_nat n O then Some a else index (pred n) l'
  end.

Example test_index1 :    index 0 [4;5;6;7]  = Some 4.
Proof. reflexivity.  Qed.
Example test_index2 :    index  1 [[1];[2]]  = Some [2].
Proof. reflexivity.  Qed.
Example test_index3 :    index  2 [true]  = None.
Proof. reflexivity.  Qed.

Definition hd_error {X : Type} (l : list X) : option X :=
  match l with
    | [] => None
    | x :: _ => Some x
  end.

Check @hd_error.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.

Example test_hd_error2 : hd_error [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Example test_hd_error3 : hd_error mynil = None.
Proof. reflexivity. Qed.


(* ###################################################### *)
(** ** High order function *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

Check @doit3times.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

 Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | [] => []
  | h :: t => if test h then h :: (filter test t)
                        else filter test t
  end. 

Example test_filter1: filter (fun l => beq_nat l 2) [1;2;3;4] = [2].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

Definition partition {X : Type} (t: X -> bool) (l : list X) : list X * list X :=
  (filter t l, filter (fun x => negb (t x)) l).

Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

(* ###################################################### *)
(** ** Map *)

(** Another handy higher-order function is called [map]. *)

Fixpoint map {X Y:Type} (f:X->Y) (l:list X)
             : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** *** *)
(** It takes a function [f] and a list [ l = [n1, n2, n3, ...] ]
    and returns the list [ [f n1, f n2, f n3,...] ], where [f] has
    been applied to each element of [l] in turn.  For example: *)

Example test_map1: map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity.  Qed.

Arguments snoc {X} l v.

Theorem map_snoc : forall (X Y : Type) (f : X -> Y) (x : X) (l : list X),
  map f (snoc l x) = snoc (map f l) (f x).
Proof.
  intros X Y f x l.
  induction l.
  reflexivity.
  simpl. rewrite -> IHl. reflexivity.
Qed.

Lemma map_distr : forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1.
  reflexivity.
  simpl. rewrite -> IHl1.
  reflexivity.
Qed.

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l.
  induction l.
  reflexivity.
  simpl.
  rewrite <- IHl.
  rewrite -> map_distr.
  simpl.
  reflexivity.
Qed.

Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : (list Y) :=
  match l with
  | [] => []
  | x :: xs => (f x) ++ (flat_map f xs)
  end.

 Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
 Proof. reflexivity. Qed.

(** ** Fold *)

(** An even more powerful higher-order function is called
    [fold].  This function is the inspiration for the "[reduce]"
    operation that lies at the heart of Google's map/reduce
    distributed programming framework. *)

 Fixpoint fold {X Y : Type} (f : X -> Y -> Y) ( l : list X) (b : Y) : Y :=
   match l with
   | nil => b
   | h :: t => f h ( fold f t b)
   end.

 Compute fold plus [1;2;3;4] 0.

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
  intros X l.
  induction l.
  reflexivity.
  simpl.
  rewrite <- IHl.
  reflexivity.
Qed.


(** **** Exercise: 3 stars (fold_map)  *)
(** We can also define [map] in terms of [fold].  Finish [fold_map]
    below. *)

Definition fold_map {X Y:Type} (f : X -> Y) (l : list X) : list Y :=
  fold (fun x y => f x :: y) l [].

Theorem fold_map_correct : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f l = fold_map f l.
Proof.
  intros X Y f l.
  induction l.
  reflexivity.
  simpl. 
  rewrite -> IHl.
  reflexivity.
Qed.

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

Check @prod_curry.

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z :=
  f (fst p) (snd p).
                     
Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

Check @prod_uncurry.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  destruct p.
  reflexivity.
Qed.

Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if beq_nat n O then Some a else nth_error l' (pred n)
     end.

(** **** Exercise: 4 stars, advanced (church_numerals)  *)

Module Church.

(** In this exercise, we will explore an alternative way of defining
    natural numbers, using the so-called _Church numerals_, named
    after mathematician Alonzo Church. We can represent a natural
    number [n] as a function that takes a function [f] as a parameter
    and returns [f] iterated [n] times. More formally, *)

Definition nat := forall X : Type, (X -> X) -> X -> X.