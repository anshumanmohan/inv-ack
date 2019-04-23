Require Import Omega.
Require Import Setoid.


(*
=============================================================================
****************** SECTION 1: PRELIMINARIES *********************************
=============================================================================
 *)

(* This file contains recurrently useful results and definitions
   that are used throughout the subsequent files *)


(* ****** USEFUL LEMMAS ABOUT NAT ********************** *)

Lemma le_S_n_m : forall n m : nat, n <= m <-> S n <= S m.
  intros. omega. Qed.

Lemma not_lt: forall n m : nat, n <= m <-> ~ m < n.
  intros. omega. Qed.

Lemma not_le: forall n m : nat, ~ n <= m <-> m < n.
  intros. omega. Qed.

Lemma le_lt_S: forall n m : nat, S n <= m <-> n < m.
  intros. omega. Qed.

Lemma lt_S_le: forall n m : nat, n <= m <-> n < S m.
  intros. omega. Qed.


(* ****** REPEATED APPLICATION ************ *)

Fixpoint repeat (f: nat -> nat) (rep n : nat) : nat :=
  match rep with
  | 0 => n
  | S rep' => f (repeat f rep' n)
  end.

Theorem repeat_S_comm :
  forall f k n, repeat f (S k) n = repeat f k (f n).
Proof.
  induction k; trivial. 
  intro. simpl in *. rewrite IHk. trivial.
Qed.

Theorem repeat_plus :
  forall f k l n, repeat f (k + l) n = repeat f k (repeat f l n).
Proof. induction k; trivial. simpl; intros; rewrite IHk; trivial. Qed.