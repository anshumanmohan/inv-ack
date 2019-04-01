Require Import Omega.
Require Import prelims.
Require Import repeater.
Require Import countdown.
Require Import inverse.


(* We use countdown to implement an inverse tower for the Hyperoperation.
   Interestingly, the 2nd, 3rd and 4th levels of this tower corresponds to division,
   log base b and log* base b, which are not defined in the Coq standard library. Our
   approach to them using countdown offers enough versatility and flexibility to
   substantiate easy and direct proof for a vast range of facts about these functions.
   Lastly, we slightly modify this tower to get the inverse tower for the Peter-Ackermann
   function, which is used to compute the Inverse Ackermann function, which is not
   only an interesting application of countdown, but also an important one since it
   computes the inverse Ackermann function in linear time. *)

(* ****** INVERSE-HYPEROP TOWER ********************************* *)

Fixpoint inv_hyperop n a b :=
  match n with
  | 0 => b - 1
  | S n' =>
    countdown_to match n' with 0 => a | 1 => 0 | _ => 1 end (inv_hyperop n' a) b
  end.

Theorem inv_hyperop_recursion :
  forall n a,
    inv_hyperop (S n) a =
    countdown_to (match n with | 0 => a | 1 => 0 | _ => 1 end)
                 (inv_hyperop n a).
Proof. trivial. Qed.

Theorem inv_hyperop_0_contract_strict :
  forall a k, contract_strict_above k (inv_hyperop 0 a).
Proof.
  intro a. split; intro n; simpl; omega.
Qed.

Theorem inv_hyperop_1 :
  forall a b, inv_hyperop 1 a b = b - a.
Proof.
  intros a b.
  rewrite inv_hyperop_recursion.
  remember (b - a) as m.
  generalize dependent b. induction m.
  - intros b Hb.
    apply countdown_recursion.
    apply inv_hyperop_0_contract_strict. omega.
  - intros b Hb. remember (m + a) as n.
    rewrite <- (IHm n) by omega.
    replace n with (inv_hyperop 0 a b) by (simpl; omega).
    apply countdown_recursion.
    apply inv_hyperop_0_contract_strict. omega.
Qed.

Corollary inv_hyperop_1_repeat :
  forall a k m, repeat (inv_hyperop 1 a) k m = m - k * a.
Proof.
  intros a k m. induction k; [simpl; omega|].
  remember (inv_hyperop 1 a) as f. simpl.
  rewrite IHk, Heqf, inv_hyperop_1; omega.
Qed.

Theorem inv_hyperop_correct :
  forall a n,
    2 <= a ->
    contract_strict_above (match n with | 0 => a | 1 => 0 | _ => 1 end) (inv_hyperop n a) /\
    upp_inv_rel (inv_hyperop n a) (hyperop n a).
Proof.
  intros a n Ha.
  induction n.
  1: split; [apply inv_hyperop_0_contract_strict | intros n N; simpl; omega].
  destruct n.
  { split.
    - split; intro n; rewrite inv_hyperop_1; omega.
    - intros n N. rewrite inv_hyperop_1, hyperop_1. omega.
  }
  rewrite inv_hyperop_recursion.
  replace (hyperop (S (S n)) a) with
      (repeater_from (match n with | 0 => 0 | S _ => 1 end) (hyperop (S n) a))
    by trivial.
  destruct IHn as [IHn0 IHn1].
  split; [|apply countdown_repeater_upp_inverse; trivial].
  destruct n; [|apply countdown_contract_strict; trivial; apply IHn0].
  split.
  - intro n. rewrite countdown_repeat by apply IHn0.
    rewrite inv_hyperop_1_repeat. assert (1 <= a) by omega.
    apply (mult_le_compat_l 1 a n) in H. omega.
  - intros n Hn.
    destruct n; [omega|]. destruct n; [omega|]. 
    rewrite <- le_S_n_m.
    rewrite countdown_repeat by apply IHn0.
    rewrite inv_hyperop_1_repeat. apply (Nat.le_sub_le_add_l).
    apply (Nat.le_trans _ ((S n) * 2) _); [omega|].
    apply (mult_le_compat_l 2 a (S n)) in Ha. omega.
Qed.

Corollary inv_hyperop_upp_inverse :
  forall a n, (2 <= a) -> upp_inv_rel (inv_hyperop n a) (hyperop n a).
Proof. apply inv_hyperop_correct. Qed.


(* ****** DIVISION AND LOGARITHM ********************************* *)

(* Computes ceiling of b / a *)
Definition div a b := inv_hyperop 2 a b.

Theorem div_correct : forall a b m,
    1 <= a -> div a b <= m <-> b <= m * a.
Proof.
  intros a b m Ha.
  destruct a ; [omega|]. 
  unfold div.
  rewrite inv_hyperop_recursion.
  rewrite countdown_repeat by (split; intro n; rewrite inv_hyperop_1; omega).
  rewrite inv_hyperop_1_repeat. omega.
Qed.

(* Computes ceiling of log_a(b) *)
Definition log a b := inv_hyperop 3 a b.

Theorem log_correct : forall a b m,
    2 <= a -> log a b <= m <-> b <= a ^ m.
Proof.
  intros a b m Ha.
  unfold log. rewrite <- hyperop_3.
  apply inv_hyperop_upp_inverse; trivial.
Qed.
