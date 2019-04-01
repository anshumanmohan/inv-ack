Require Import Omega.
Require Import prelims.

(* ****** REPEATER ********************************* *)

(* Can be easily defined and computed, so we define it directly *)
Fixpoint repeater_from (a : nat) (f : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => a
  | S n' => f (repeater_from a f n')
  end. 

(* Repeater is a functional way to look at repeat *)
Theorem repeater_from_repeat :
  forall a f n, repeater_from a f n = repeat f n a.
Proof.
  intros a f n. induction n; trivial. simpl. rewrite IHn. trivial.
Qed.


(* ****** HYPEROPS ********************************* *)

Fixpoint hyperop_original (n a b : nat) : nat :=
  match n with
  | 0    => S b
  | S n' =>
    let fix hyperop_n (b0 : nat) :=
        match b0 with
        | 0 => match n' with 0 => a | 1 => 0 | _ => 1 end
        | S b0' => hyperop_original n' a (hyperop_n b0') end
    in hyperop_n b
  end.

Fixpoint hyperop (n a b : nat) : nat :=
  match n with
  | 0 => S b
  | S n' => repeater_from match n' with 0 => a | 1 => 0 | _ => 1 end (hyperop n' a) b
  end.

Theorem hyperop_correct :
  forall n a b, hyperop n a b = hyperop_original n a b.
Proof.
  intros n a. induction n; trivial.
  induction b; trivial.
  simpl in *. rewrite IHb. trivial.
Qed.

Theorem hyperop_recursion :
  forall n a b,
    hyperop (S n) a (S b) = hyperop n a (hyperop (S n) a b).
Proof. trivial. Qed.

Lemma hyperop_1 : forall a b, hyperop 1 a b = b + a.
Proof. intro a. induction b; [|rewrite hyperop_recursion, IHb]; trivial. Qed.

Lemma hyperop_2 : forall a b, hyperop 2 a b = b * a.
Proof.
  intros a b. induction b; trivial.
  rewrite hyperop_recursion, IHb, hyperop_1. simpl; omega.
Qed.

Lemma hyperop_3 : forall a b, hyperop 3 a b = a ^ b.
Proof.
  intros a b. induction b; trivial.
  rewrite hyperop_recursion, IHb, hyperop_2.
  simpl. apply Nat.mul_comm.
Qed.

Theorem hyperop_n_1 : forall n a, 2 <= n -> hyperop n a 1 = a.
Proof.
  intros n a Hn. do 2 (destruct n; [omega|]).
  clear Hn. induction n; trivial.
Qed.

(* ****** ACKERMANN FUNCS ********************************* *)

Fixpoint ackermann_original (m n : nat) : nat :=
  match m with
   | 0 => 1 + n
   | S m' => let fix ackermann' (n : nat) : nat :=
             match n with
              | 0 => ackermann_original m' 1
              | S n' => ackermann_original m' (ackermann' n')
             end
             in ackermann' n
  end.

Fixpoint ackermann m n :=
  match m with
  | 0 => S n
  | S m' => repeater_from (ackermann m' 1) (ackermann m') n
  end.

Theorem ackermann_correct :
  forall n b, ackermann n b = ackermann_original n b.
Proof.
  intros n. induction n; trivial.
  induction b. apply IHn.
  simpl in *. rewrite IHb. trivial.
Qed.

Theorem ackermann_initial :
  forall m, ackermann (S m) 0 = ackermann m 1.
Proof. trivial. Qed.

Theorem ackermann_recursion :
  forall m n, ackermann (S m) (S n) = ackermann m (ackermann (S m) n).
Proof. trivial. Qed.

Theorem ack_hyperop : forall m n,
    3 + ackermann m n = hyperop m 2 (3 + n).
Proof.
  induction m; trivial.
  induction n.
  - replace (3 + 0) with 3 by omega.
    rewrite hyperop_recursion, ackermann_initial, IHm.
    replace (3 + 1) with 4 by trivial.
    f_equal. clear IHm.
    induction m; trivial.
    rewrite hyperop_recursion, hyperop_n_1; [trivial | omega].
  - rewrite ackermann_recursion, IHm.
    replace (3 + S n) with (S (3 + n)) by trivial.
    rewrite hyperop_recursion, IHn; trivial.
Qed.