Require Import Omega.
Require Import Setoid.


(*
=============================================================================
****************** SECTION 0: PRELIMINARIES *********************************
=============================================================================
 *)

(* This file contains everything not put in the paper but will be useful
   for the Coq proofs later on *)


(* ****** 0.1. USEFUL LEMMAS ABOUT NAT ********************** *)

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


(* ****** 0.2. CONTRACTIONS *************** *)

(* Definition of general contractions *)
Definition contracting (f : nat -> nat) : Prop := forall n, f n <= n.

(* Basically: a contraction is strict from "a" iff "f n < n" for all "n > a" *)
Definition contract_strict_from (a : nat) (f : nat -> nat) : Prop :=
  forall n, a <= n -> S (f n) <= n.


(* ****** 0.3. REPEATED APPLICATION AND CONTRACTION ************ *)

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



(* 
 * Cleaning up to replace "S a <= b" with "a < b".
 * The exact same proof works. 
 *)
Lemma repeat_contract_strict' :
  forall a f n k,
    contracting f ->
    contract_strict_from (S a) f ->
    a < repeat f k n ->
    k + repeat f (S k) n < n.
Proof. apply repeat_contract_strict. Qed.
(* 
 * I wonder if maybe we can replace it like this everywhere,
 * provided it doens't affect the computation.
 *)

(* Basically the existence of the countdown value for strict contractions
   It asserts there is a minimum "l" for which repeating "f" "l" times from "n"
   will give a result less than or equal to "a"
   This is important for the proof of correctness in "countdown_compute.v" *)
Lemma repeat_contract_strict_threshold :
  forall a f n,
    contracting f -> contract_strict_from (S a) f -> S a <= n ->
    exists l, (S l) <= n /\ repeat f (S l) n <= a < repeat f l n.
Proof.
  intros a f n Hf Haf Han.
  remember (n - a) as m.
  destruct m; [omega|].
  assert (forall b, (a <= b) -> f (S b) <= b) as Ha.
  { intros b Hab. rewrite le_S_n_m. apply Haf. omega. }
  generalize dependent a.
  induction m.
  - intros. exists 0.
    simpl. split; [|split];
             [|replace n with (S a) by omega; apply Ha|]; omega.
  - intros. destruct (IHm (S a)); try omega.
    + intros p Hp. apply Haf. omega.
    + intros b Hab. apply Ha. omega.
    + destruct H as [H0 H1]. destruct H1 as [Hl Hr]. inversion Hl.
      2: exists x; split; [apply H0 | omega].
      exists (S x). simpl. rewrite H1. split.
      2: split; [apply Ha|]; omega.
      apply (Nat.le_trans _ (S x + (repeat f (S x) n)) _);
                  [simpl; rewrite H1; omega|].
      apply (repeat_contract_strict a f n x); auto. omega.
Qed.