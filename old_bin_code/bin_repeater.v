Require Import BinNat.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.
Require Import micromega.Lia.
Require Import Nnat.
Require Import Omega.
Require Import bin_prelims.
Require repeater.

Open Scope N_scope.

(*
=============================================================================
******* SECTION 2: HYPEROPS, ACKERMANN AND REPEATER *************************
=============================================================================
 *)

(* We introduce "repeater" and how to use it to redefine the hyperoperations
   and Ackermann function.
   We also prove several results about the value of hypeopererations at small
   numbers and levels, which are treated as known in the paper but need to be
   rigourously proven here to be used in the proofs of theorems in the paper.
   Several similar results for the Ackermann function are also provided.
   Note that some results here may not be related to results in the paper, but
   appear purely for aesthetics reasons. *)

(* ****** REPEATER ********************************* *)

Definition repeater (f : N -> N) (a : N) (n : N) : N :=
  match n with
  | 0      => a
  | Npos p => let fix repeater_pos (g : N -> N) (p : positive) (a' : N) : N :=
               match p with
               | xH    => g a'
               | xO p' => let g' := repeater_pos g p' in g' (g' a')
               | xI p' => let g' := repeater_pos g p' in g (g' (g' a'))
               end in repeater_pos f p a
  end.

(* Repeater is a functional way to look at repeat
   See "repeat" in "prelims.v" *)
Theorem repeater_repeat :
    forall a f n, repeater f a n = repeat f (N.to_nat n) a.
Proof.
  intros a f n. destruct n; trivial. simpl.
  generalize dependent a.
  induction p; intro a; [ | |trivial];
  [replace (Pos.to_nat p~1) with (S (Pos.to_nat p + Pos.to_nat p))%nat by lia|
  replace (Pos.to_nat p~0) with (Pos.to_nat p + Pos.to_nat p)%nat by lia];
    simpl; f_equal; rewrite repeat_plus; repeat rewrite IHp; trivial.
Qed.

(*
(* Repeater on N is consistent with its counterpart on nat *)
Theorem repeater_Nnat : 
    forall a f, repeater f a =
    to_N_func (repeater.repeater_from (to_nat_func f) (N.to_nat a)).
Proof.
  intros a f. apply functional_extensionality; intro n.
  unfold to_N_func. rewrite repeater_repeat.
  rewrite repeater.repeater_from_repeat.
  remember (N.to_nat n) as m. clear Heqm. unfold to_nat_func.
  induction m; simpl; [ |rewrite <- IHm]; rewrite N2Nat.id; trivial.
Qed.
*)

(* Repeater on N is consistent with its counterpart on nat *)
Theorem repeater_Nnat : 
    forall a f n, repeater f a n =
    N.of_nat (repeater.repeater_from (to_nat_func f) (N.to_nat a) (N.to_nat n)).
Proof.
  intros a f n. rewrite repeater_repeat.
  rewrite repeater.repeater_from_repeat.
  remember (N.to_nat n) as m. clear Heqm. unfold to_nat_func.
  induction m; simpl; [ |rewrite <- IHm]; rewrite N2Nat.id; trivial.
Qed.


(* ****** HYPEROPS ********************************* *)

(* A function to summarize the initial values of the hyperoperations *)
Definition hyperop_init (a : N) (n : nat) : N :=
  match n with 0%nat => a | 1%nat => 0 | _ => 1 end.

(* Our definition for hyperops using repeater *)
Fixpoint hyperop (a : N) (n : nat) (b : N) : N :=
  match n with
  | 0%nat => 1 + b
  | S n'  => repeater (hyperop a n') (hyperop_init a n') b
  end.

(* A handy theorem to transform goals involving hyperops *)
Lemma hyperop_recursion :
  forall (n : nat) (a : N),
    hyperop a (S n) = repeater (hyperop a n) (hyperop_init a n).
Proof. intros. apply functional_extensionality. intro b. trivial. Qed.

(* Proof that the two hyperops are the same *)
Theorem hyperop_correct :
  forall n a b, hyperop a n b = N.of_nat (repeater.hyperop (N.to_nat a) n (N.to_nat b)).
Proof.
  intros n a. induction n; intro b.
  - unfold hyperop. unfold repeater.hyperop. lia.
  - rewrite hyperop_recursion.
    replace (repeater.hyperop (N.to_nat a) (S n) (N.to_nat b)) with
    (repeater.repeater_from (repeater.hyperop (N.to_nat a) n)
                          (repeater.hyperop_init (N.to_nat a) n)
                          (N.to_nat b)) by trivial.
    replace (repeater.hyperop_init (N.to_nat a) n) with
    (N.to_nat (hyperop_init a n)) by repeat (destruct n; trivial).
    rewrite repeater_Nnat. repeat f_equal.
    apply functional_extensionality; intro c.
    unfold to_nat_func. rewrite IHn. repeat rewrite Nat2N.id. trivial.
Qed.

(* The first few functions in the hyperops. Useful for pointing out
   their inverse specifically *)

Lemma hyperop_1 : forall a b, hyperop a 1 b = b + a.
Proof.
  intros. rewrite hyperop_correct. rewrite repeater.hyperop_1. lia.
Qed.

Lemma hyperop_2 : forall a b, hyperop a 2 b = b * a.
Proof.
  intros. rewrite hyperop_correct. rewrite repeater.hyperop_2. lia.
Qed.

Lemma hyperop_3 : forall a b, hyperop a 3 b = a ^ b.
Proof.
  intros. rewrite hyperop_correct. rewrite repeater.hyperop_3.
  remember (N.to_nat a) as a0. replace a with (N.of_nat a0) by lia. clear Heqa0.
  remember (N.to_nat b) as b0. replace b with (N.of_nat b0) by lia. clear Heqb0.
  induction b0; trivial. replace (N.of_nat (S b0)) with (1 + N.of_nat b0) by lia.
  rewrite N.pow_add_r. rewrite N.pow_1_r. simpl. rewrite <- IHb0. lia.
Qed.

(* A beautiful result about hypeops value at b = 1.
   Used in the proof of the theorem "ack_hyperop",
   which is also just for aesthetics *)
Lemma hyperop_n_1 : forall n a, (2 <= n)%nat -> hyperop a n 1 = a.
Proof.
  intros n a Hn. do 2 (destruct n; [omega|]).
  clear Hn. induction n; trivial.
Qed.

(* ****** ACKERMANN FUNCTION ********************************* *)

(* Our definition using repeater *)
Definition ackermann (n m : N) : N :=
  let fix ack_nat (n0 : nat) (m0 : N) : N :=
   match n0 with
   | 0%nat => 1 + m0
   | S n1  => repeater (ack_nat n1) (ack_nat n1 1) m0
   end in ack_nat (N.to_nat n) m.

(* Proof that the above are the same *)
Theorem ackermann_correct : forall n m,
  ackermann n m = N.of_nat (repeater.ackermann (N.to_nat n) (N.to_nat m)).
Proof.
  intros n m. unfold ackermann. unfold repeater.ackermann.
  generalize dependent m. induction (N.to_nat n); intro m; [lia| ].
  rewrite repeater_Nnat. repeat f_equal;
  [unfold to_nat_func; apply functional_extensionality; intro p| ];
  rewrite IHn0; repeat rewrite Nat2N.id; trivial.
Qed.