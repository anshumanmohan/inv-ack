Require Import Omega.
Require Import prelims.
Require Import countdown_repeater.
Require Import inverse.
Require Import countdown_compute.

(*
=============================================================================
**************** SECTION 5: DIV, LOG AND HIGHER LEVELS **********************
=============================================================================
*)

(* This section contains applications of countdown and repeater.
   Obviously we will use repeater to implement Hyperoperations, Knuth's Up Arrows,
   and Ackermann function.
   We use countdown to implement their inverses. We will introduce an inverse tower
   for the Hyperoperation and Knuth's Up Arrow (which is just the truncation of the 
   Hyperoperations).
   Interestingly, the 2nd, 3rd and 4th levels of this tower corresponds to division,
   log base b and log* base b, which are not defined in the Coq standard library. Our
   approach to them using countdown is offers enough versatility and flexibility to
   substantiate easy and direct proof for a vast range of facts about these functions.
   Lastly, we slightly modify this tower to get the inverse tower for the Peter-Ackermann
   function, which is used to compute the Inverse Ackermann function, which is not
   only an interesting application of countdown, but also an important one since it
   computes the inverse Ackermann function in linear time. *)

(* ****** 5.2. HYPEROPS ********************************* *)

Fixpoint hyperop_original (n a b : nat) : nat :=
match n with
| 0    => S b
| S n' => let fix hyperop_n (b0 : nat) :=
          match b0 with
          | 0     => match n' with
                     | 0 => a
                     | 1 => 0
                     | _ => 1 end
          | S b0' => hyperop_original n' a (hyperop_n b0') end
          in hyperop_n b
end.

Fixpoint hyperop (n a b : nat) : nat :=
match n with
| 0 => S b
| S n' => repeater_from
           match n' with
           | 0 => a
           | 1 => 0
           | _ => 1 end (hyperop n' a) b
end.

Theorem hyperop_correct :
forall n a b, hyperop n a b = hyperop_original n a b.
Proof.
intros n a.
induction n.
{ trivial. }
induction b.
- trivial.
- simpl. simpl in IHb.
  rewrite IHb. trivial.
Qed.

Theorem hyperop_recursion :
forall n a b, hyperop (S n) a (S b) = hyperop n a (hyperop (S n) a b).
Proof.
trivial.
Qed.

Theorem hyperop_1 : forall a b, hyperop 1 a b = b + a.
Proof.
intro a. induction b.
{ trivial. }
rewrite hyperop_recursion.
rewrite IHb. trivial.
Qed.

Theorem hyperop_2 : forall a b, hyperop 2 a b = b * a.
Proof.
intros a b.
induction b.
{ trivial. }
rewrite hyperop_recursion.
rewrite IHb.
rewrite hyperop_1.
simpl. omega.
Qed.

Theorem hyperop_3 : forall a b, hyperop 3 a b = a ^ b.
Proof.
intros a b.
induction b.
{ trivial. }
rewrite hyperop_recursion.
rewrite IHb.
rewrite hyperop_2.
simpl. apply Nat.mul_comm.
Qed.

Theorem hyperop_n_1 : forall n a, 2 <= n -> hyperop n a 1 = a.
Proof.
intros n a Hn.
destruct n. { omega. }
destruct n. { omega. }
clear Hn. induction n.
- trivial.
- rewrite hyperop_recursion.
  replace (hyperop (S (S (S n))) a 0) with 1 by trivial.
  apply IHn.
Qed.

(* ****** 5.2. KNUTH ARROWS ********************************* *)

Fixpoint knuth_arrow n a b :=
match n with
| 0 => b * a
| S n' => let fix knuth_arrow_n b0 :=
          match b0 with
          | 0 => 1
          | S b0' => knuth_arrow n' a (knuth_arrow_n b0')
          end in knuth_arrow_n b
end.

Theorem knuth_arrow_recursion : forall n a b,
knuth_arrow (S n) a (S b) = knuth_arrow n a (knuth_arrow (S n) a b).
Proof.
trivial.
Qed.

Theorem knuth_arrow_hyperop : forall n a b,
knuth_arrow n a b = hyperop (S(S n)) a b.
Proof.
intros n a.
induction n.
{ intro b. rewrite hyperop_2. trivial. }
induction b.
- trivial.
- rewrite knuth_arrow_recursion.
  rewrite hyperop_recursion.
  rewrite IHb.
  apply IHn.
Qed.

(* ****** 5.3. ACKERMANN FUNCS ********************************* *)

Fixpoint ackermann m n :=
match m with
| 0    => S n
| S m' => repeater_from (ackermann m' 1) (ackermann m') n
end.

Theorem ackermann_initial :
forall m, ackermann (S m) 0 = ackermann m 1.
Proof.
trivial.
Qed.

Theorem ackermann_recursion :
forall m n, ackermann (S m) (S n) = ackermann m (ackermann (S m) n).
Proof.
trivial.
Qed.

Theorem ack_hyperop : forall m n,
3 + ackermann m n = hyperop m 2 (3 + n).
Proof.
induction m.
{ trivial. }
induction n.
- replace (3 + 0) with 3 by omega.
  rewrite hyperop_recursion.
  rewrite ackermann_initial.
  rewrite IHm. replace (3 + 1) with 4 by trivial.
  apply f_equal. clear IHm.
  induction m.
  + trivial.
  + rewrite hyperop_recursion.
    rewrite hyperop_n_1. trivial. omega.
- rewrite ackermann_recursion.
  rewrite IHm.
  replace (3 + S n) with (S (3 + n)) by trivial.
  rewrite hyperop_recursion.
  rewrite IHn. trivial.
Qed.

(* ****** 5.4. INVERSE-HYPEROP TOWER ********************************* *)

Fixpoint inv_hyperop n a b :=
match n with
| 0    => b - 1
| S n' => countdown_to
           match n' with
           | 0 => a
           | 1 => 0
           | _ => 1 end (inv_hyperop n' a) b
end.

Theorem inv_hyperop_0_countdownable :
forall a, countdownable_to a (inv_hyperop 0 a).
Proof.
intro a. split; intro n; simpl; omega.
Qed.

Theorem inv_hyperop_1 :
forall a b, inv_hyperop 1 a b = b - a.
Proof.
intros a b.
assert (countdown_to_recurse_rel a (inv_hyperop 0 a) (inv_hyperop 1 a)).
{ remember (inv_hyperop 0 a) as f.
  replace (inv_hyperop 1 a) with (countdown_to a f) by (rewrite Heqf; trivial).
  rewrite <- countdown_to_rel_recursion
  by (rewrite Heqf; apply inv_hyperop_0_countdownable).
  apply countdown_to_repeat.
  rewrite Heqf. apply inv_hyperop_0_countdownable. }
unfold countdown_to_recurse_rel in H.
remember (b - a) as m.
generalize dependent b. induction m.
- intros b Hb. apply H. omega.
- intros b Hb. remember (m + a) as n.
  rewrite <- (IHm n) by omega.
  replace n with (inv_hyperop 0 a b) by (simpl; omega).
  apply H. omega.
Qed.


Theorem inv_hyperop_countdownable :
forall n a, (1 <= a) -> countdownable_to
           (match n with | 0 => a | 1 => 0 | _ => 1 end) (inv_hyperop n a).
Proof.
destruct n.
{ intros a Ha. split; intro n; simpl; omega. }
destruct n.
{ intros a Ha. split; intro n; rewrite inv_hyperop_1; omega. }
induction n.
Admitted.

Theorem inv_hyperop_correct :
forall n a, upp_inv_rel (inv_hyperop n a) (hyperop n a).
Proof.
intros n a.
induction n.
- intros bi bh. simpl. omega.
- remember (match n with | 0 => a | 1 => 0 | _ => 1 end) as x0.
  replace (inv_hyperop (S n) a) with
  (countdown_to x0 (inv_hyperop n a)) by (rewrite Heqx0; trivial).
  replace (hyperop (S n) a) with
  (repeater_from x0 (hyperop n a)) by (rewrite Heqx0; trivial).
  apply (countdown_repeater_upp_inverse x0 (inv_hyperop n a) _ _).
  + apply countdown_to_repeat.
Admitted.