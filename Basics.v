Fixpoint plus (n:nat) (m:nat) :=
  match n with
  | O => m
  | S n1 => S (plus n1 m)
  end.

Example test_plus_1: (plus (S O) (S O)) = (S (S O)).
Proof. simpl. reflexivity. Qed.
Example test_plus_2: (plus O O) = O.
Proof. simpl. reflexivity. Qed.

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n1 => plus m (mult n1 m) 
  end.

Example test_mult_0: (mult O O) = O.
Proof. simpl. reflexivity. Qed.
Example test_mult_1: (mult (S (S O)) (S (S O))) = (S (S (S (S O)))).
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n,m with
  | O, _ => O
  | n1, O => n1
  | S n1, S m1 => minus n1 m1
  end.

Example test_minus_0: (minus O O) = O.
Proof. simpl. reflexivity. Qed.

Example test_minus_1: (minus (S O) O) = S O.
Proof. simpl. reflexivity. Qed.

Example test_minus_2: (minus (S (S O)) (S O)) = (S O).
Proof. simpl. reflexivity. Qed.

Example test_minus_3: (minus O (S O)) = O.
Proof. simpl. reflexivity. Qed.

Example test_minus_4: (minus (S (S O)) (S (S (S O)))) = O.
Proof. simpl. reflexivity. Qed.


Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S power' => mult base (exp base power')
  end.

Example test_exp_1: (exp (S O) O) = S O.
Proof. simpl. reflexivity. Qed.

Example test_exp_2: (exp (S (S O)) (S (S O))) = (S (S (S (S O)))).
Proof. simpl. reflexivity. Qed.

Infix "*" := mult.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => S O
  | S n1 => n * fact n1
  end.

Example test_fact_1: (fact O) = (S O).
Proof. simpl. reflexivity. Qed.

Example test_fact_2: (fact (S (S (S O)))) = (S (S (S (S (S (S O)))))).
Proof. simpl. reflexivity. Qed.

Example test_fact_3: (fact (S O)) = (S O).
Proof. simpl. reflexivity. Qed.

Example test_factorial1: (fact 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_fact4: (fact 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.


Fixpoint beq_nat (n m : nat) : bool := 
  match n, m with
  | O, O => true
  | S _, O => false
  | O, S _ => false
  | S n1, S m1 => beq_nat n1 m1
  end.

Example test_beq_nat1: (beq_nat 4 3) = false.
Proof. simpl. reflexivity. Qed.

Example test_beq_nat2: (beq_nat 3 3) = true.
Proof. simpl. reflexivity. Qed.

Example test_beq_nat3: (beq_nat 2 3) = false.
Proof. simpl. reflexivity. Qed.

Fixpoint leq_nat (n m : nat) : bool :=
  match n, m with
  | O, O => true
  | S _, O => false
  | O, S _ => true
  | S n1, S m1 => leq_nat n1 m1
  end.


Example test_leq_nat1: (leq_nat 4 3) = false.
Proof. simpl. reflexivity. Qed.

Example test_leq_nat2: (leq_nat 3 3) = true.
Proof. simpl. reflexivity. Qed.

Example test_leq_nat3: (leq_nat 2 3) = true.
Proof. simpl. reflexivity. Qed.

Definition blt_nat (n m : nat) : bool :=
  match (beq_nat n m) with
  | true => false
  | false => leq_nat n m
  end.

Example test_blt_nat1: (blt_nat 4 3) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat2: (blt_nat 3 3) = false.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat3: (blt_nat 2 3) = true.
Proof. simpl. reflexivity. Qed.

Example test_blt_nat4: (blt_nat 2 2) = false.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat5: (blt_nat 2 4) = true.
Proof. simpl. reflexivity. Qed.
Example test_blt_nat6: (blt_nat 4 2) = false.
Proof. simpl. reflexivity. Qed.

Definition admit {T: Type} : T.  Admitted.


Theorem plus_O_n : forall n : nat, (0 + n) = n.
Proof.
  intros n. 
  reflexivity.  
Qed.


Theorem plus_id_n_m : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  (* move n and m into the context *)
  intros n m.
  (* move the hypotesis into the context *)
  intros H.
  (* rewrite the goal using the hypothesis: *)
  rewrite <- H.
  reflexivity.
Qed.



Theorem plus_id_exercise : forall n m o : nat,
  n = m -> 
  m = o -> 
  n + m = m + o.
Proof.
  intros n m o.
  intros H1.
  intros H2.

  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
 Qed.

Theorem mult_0_plus: forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

Theorem plus_S_n : forall n : nat,
  (1 + n) = S n.
Proof.
  intros n.
  reflexivity.
Qed.

Theorem mult_S_1: forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H1.
  rewrite -> plus_S_n.
  rewrite -> H1.
  simpl.
  reflexivity.
Qed.

Theorem plus_1_neq_0_firsttry : forall n : nat,
  beq_nat (n + 1) 0 = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative'' :
  forall b c, andb b c = andb c b.
Proof.
  intros [] [].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Theorem andb_commutative' : forall b c, andb b c = andb c b.
Proof.
  intros b c. destruct b.
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
  { destruct c.
    { reflexivity. }
    { reflexivity. } }
Qed.

Theorem andb_two_equals : forall b c : bool,
  b = true ->
  c = true ->
  andb b c = true.
Proof.
  intros b c.
  intros H1.
  intros H2.
  rewrite -> H1.
  rewrite -> H2.
  reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
  andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct c.
  reflexivity.
  rewrite <- H.
  destruct b.
  reflexivity.
  reflexivity.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
  beq_nat 0 (n + 1) = false.
Proof.
  intros [|n].
  - reflexivity.
  - reflexivity.
Qed.

Theorem identity_fn_applied_twice: 
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
 intros f x b.
 destruct b.
 rewrite -> x.
 rewrite -> x.
 reflexivity.
 rewrite -> x.
 rewrite -> x.
 reflexivity.
Qed.

Theorem negation_fn_applied_twice:
  forall (f : bool -> bool),
  (forall (x : bool), f x = negb x) ->
  forall (b : bool), f (f b) = b.
Proof.
  intros f x b.
  destruct b.
  rewrite -> x.
  rewrite -> x.
  reflexivity.
  rewrite -> x.
  rewrite -> x.
  reflexivity.
Qed.
  
Theorem identity_fn_applied_twice': 
  forall (f : bool -> bool),
  (forall (x : bool), f x = x) ->
  forall (b : bool), f (f b) = b.
Proof.
 intros f H b.
 rewrite -> H.
 rewrite -> H.
 reflexivity.
 
Qed.

Theorem identity_fn_applied_twice'' : 
  forall (f : bool -> bool),
    (forall (x : bool), f x = x) -> forall (b : bool), f (f b) = b.
Proof.
  intros f H b. (* Introduce our parameters *)
  rewrite -> H.
  apply H.
Qed.

Theorem andb_eq_orb :
  forall (b c : bool),
  (andb b c = orb b c) ->
  b = c.
Proof.
  intros b c;
  destruct b,c;
  intro H;
  inversion H.
  inversion H.
  reflexivity.
  reflexivity.
Qed.

Inductive bin : Type :=
  | T : bin
  | O : bin -> bin
  | S : bin -> bin.

Example construct: (S (S (S (S (O (S (S (O (S T))))))))) = (S (S (S (S (O (S (S (O (S T))))))))).
Proof. simpl. reflexivity. Qed.

Fixpoint incr (b : bin) : bin :=
  match b with
  | T => T
  | S T => S (O T)
  | O T => (S T)
  | S n => S (incr n)
  | O n => O (incr n)
  end. 

Example zero_inc: incr (O T) = (S T).
Proof. reflexivity. Qed.

Example one_inc: incr (S T) = (S (O T)).
Proof. reflexivity. Qed.

Example two_inc: incr (S (O T)) = (S (S T)).
Proof. simpl. reflexivity. Qed.

Example ten_inc: incr (S (O (S (O T)))) = (S (O (S (S T)))).
Proof. simpl. reflexivity. Qed.

Fixpoint bin_length (b : bin) : nat :=
  match b with
   | T => 0
   | O n => 1 + (bin_length n)
   | S n => 1 + (bin_length n)
  end.

Example bin_length_0: bin_length T = 0.
Proof. simpl. reflexivity. Qed.

Example bin_length_1: bin_length (S T) = 1.
Proof. simpl. reflexivity. Qed.

Example bin_length_3: bin_length (S (O (S T))) = 3.
Proof. simpl. reflexivity. Qed.

Fixpoint bin_to_nat (b : bin) : nat :=
  match b with
   | T => 0
   | S n => 1 * (exp 2 (bin_length n)) + (bin_to_nat n)
   | O n => 0 + (bin_to_nat n)
  end.

Example bin_to_nat_110: bin_to_nat (S (S (O T))) = 6.
Proof. simpl. reflexivity. Qed.

Example bin_to_nat_11: bin_to_nat (S (S T)) = 3.
Proof. simpl. reflexivity. Qed.

Example bin_to_nat_incr: bin_to_nat (incr (S (S (O T)))) = 6+1.
Proof. simpl. reflexivity. Qed.

Inductive bin' : Type :=
  | Z : bin'
  | D : bin' -> bin'
  | F : bin' -> bin'.

Fixpoint incr' (b: bin') : bin' :=
  match b with
    | Z => F Z
    | D b' => F b'
    | F b' => D (incr' b')
  end.

Fixpoint bin_to_nat' (b: bin') : nat :=
  match b with
    | Z => 0
    | D b' => 2 * (bin_to_nat' b')
    | F b' => 1 + 2 * (bin_to_nat' b')
  end.
