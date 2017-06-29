Require Export Basics.


Theorem plus_n_O : forall n:nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *) reflexivity.
  - (* n = S n' *) simpl. rewrite <- IHn'. reflexivity. Qed.

Theorem minus_diag : forall n,
  minus n n = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n. induction n as [| n' IHn'].
  - (* n = 0 *)
    simpl. reflexivity.
  - (* n = S n' *)
    simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem mult_0_r : forall n:nat,
  n * 0 = 0.
Proof.
  intros n. induction n as [|n' IHn'].
  reflexivity.
  simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n' IHn'].
  simpl. reflexivity.
  simpl. rewrite <- IHn'. reflexivity. Qed.


Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' IHn'].
  simpl. rewrite <- plus_n_O. reflexivity.
  simpl. rewrite -> IHn'. rewrite -> plus_n_Sm. reflexivity. Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n' IHn'].
  simpl. reflexivity.
  simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
   intros n. induction n as [|n' IHn'].
   reflexivity.
   simpl.
   rewrite -> IHn'.
   rewrite <- plus_n_Sm.  
   reflexivity.
Qed.

(* Proofs Within Proofs *)

Theorem mult_0_plus' : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: 0 + n = n). { reflexivity. }
  rewrite -> H.
  reflexivity. 
Qed.

Theorem plus_rearrange_firsttry : forall n m p q : nat,
  (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: (n + m) = (m + n)). { rewrite <- plus_comm. reflexivity. }
  rewrite <- H.
  reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
  n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  assert (H1: n + (m + p) = (n + m) + p). { rewrite <- plus_assoc. reflexivity. }
  rewrite -> H1.
  assert (H2: m + (n + p) = (m + n) + p). { rewrite <- plus_assoc. reflexivity. }
  rewrite -> H2.
  assert (H3: m + n = n + m). { rewrite <- plus_comm. reflexivity. }
  rewrite <- H3. reflexivity.
Qed.

