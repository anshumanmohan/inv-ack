Require Import Omega.
Require Import prelims.
Require Import countdown_repeater.
Require Import inverse.

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
   approach to them using countdown offers enough versatility and flexibility to
   substantiate easy and direct proof for a vast range of facts about these functions.
   Lastly, we slightly modify this tower to get the inverse tower for the Peter-Ackermann
   function, which is used to compute the Inverse Ackermann function, which is not
   only an interesting application of countdown, but also an important one since it
   computes the inverse Ackermann function in linear time. *)

(* ****** 5.2. HYPEROPS ********************************* *)

Definition hyperop_init (a n : nat) : nat :=
  match n with 0 => a | 1 => 0 | _ => 1 end.

Fixpoint hyperop_original (a n b : nat) : nat :=
  match n with
  | 0    => 1 + b
  | S n' => let fix hyperop' (b : nat) :=
            match b with
            | 0 => hyperop_init a n'
            | S b' => hyperop_original a n' (hyperop' b') 
            end
            in hyperop' b
  end.

Fixpoint hyperop (a n b : nat) : nat :=
  match n with
  | 0 => 1 + b
  | S n' => repeater_from (hyperop_init a n') (hyperop a n') b
  end.

Theorem hyperop_correct :
  forall n a b, hyperop n a b = hyperop_original n a b.
Proof.
  intros a n. induction n; trivial.
  induction b; trivial.
  simpl in *. rewrite IHb. trivial.
Qed.

Theorem hyperop_recursion :
  forall n a b,
    hyperop a (S n) (S b) = hyperop a n (hyperop a (S n) b).
Proof. trivial. Qed.

Theorem hyperop_1 : forall a b, hyperop a 1 b = b + a.
Proof. intro a. induction b; [|rewrite hyperop_recursion, IHb]; trivial. Qed.

Theorem hyperop_2 : forall a b, hyperop a 2 b = b * a.
Proof.
  intros a b. induction b; trivial.
  rewrite hyperop_recursion, IHb, hyperop_1. simpl; omega.
Qed.

Theorem hyperop_3 : forall a b, hyperop a 3 b = a ^ b.
Proof.
  intros a b. induction b; trivial.
  rewrite hyperop_recursion, IHb, hyperop_2.
  simpl. apply Nat.mul_comm.
Qed.

Theorem hyperop_n_1 : forall n a, 2 <= n -> hyperop a n 1 = a.
Proof.
  intros n a Hn. do 2 (destruct n; [omega|]).
  clear Hn. induction n; trivial.
Qed.

(* ****** 5.2. KNUTH ARROWS ********************************* *)

Fixpoint knuth_arrow n a b :=
  match n with
  | 0 => b * a
  | S n' =>
    let fix knuth_arrow_n b0 :=
        match b0 with
        | 0 => 1
        | S b0' => knuth_arrow n' a (knuth_arrow_n b0')
        end in knuth_arrow_n b
  end.

Theorem knuth_arrow_recursion : forall n a b,
    knuth_arrow (S n) a (S b) = knuth_arrow n a (knuth_arrow (S n) a b).
Proof. trivial. Qed.

Theorem knuth_arrow_hyperop : forall n a b,
    knuth_arrow n a b = hyperop a (S(S n)) b.
Proof.
  intros n a.
  induction n.
  1: intro b; rewrite hyperop_2; trivial. 
  induction b; trivial.
  rewrite knuth_arrow_recursion, hyperop_recursion, IHb.
  apply IHn.
Qed.

(* ****** 5.3. ACKERMANN FUNCS ********************************* *)

Fixpoint ackermann_original (n m : nat) : nat :=
  match n with
  | 0    => 1 + m
  | S n' => let fix ackermann' (m : nat) : nat :=
              match m with
              | 0 => ackermann_original n' 1
              | S m' => ackermann_original n' (ackermann' m')
              end
            in ackermann' m
  end.

Fixpoint ackermann n m :=
  match n with
  | 0 => S m
  | S n' => repeater_from (ackermann n' 1) (ackermann n') m
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
    3 + ackermann m n = hyperop 2 m (3 + n).
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

(* ****** 5.4. INVERSE-HYPEROP TOWER ********************************* *)

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

Theorem inv_hyperop_0_countdownable :
  forall a k, countdownable_to k (inv_hyperop 0 a).
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
    apply countdown_to_recursion.
    apply inv_hyperop_0_countdownable. omega.
  - intros b Hb. remember (m + a) as n.
    rewrite <- (IHm n) by omega.
    replace n with (inv_hyperop 0 a b) by (simpl; omega).
    apply countdown_to_recursion.
    apply inv_hyperop_0_countdownable. omega.
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
    countdownable_to (match n with | 0 => a | 1 => 0 | _ => 1 end) (inv_hyperop n a) /\
    upp_inv_rel (inv_hyperop n a) (hyperop a n).
Proof.
  intros a n Ha.
  induction n.
  1: split; [apply inv_hyperop_0_countdownable | intros n N; simpl; omega].
  destruct n.
  { split.
    - split; intro n; rewrite inv_hyperop_1; omega.
    - intros n N. rewrite inv_hyperop_1, hyperop_1. omega.
  }
  rewrite inv_hyperop_recursion.
  replace (hyperop a (S (S n))) with
      (repeater_from (match n with | 0 => 0 | S _ => 1 end) (hyperop a (S n)))
    by trivial.
  destruct IHn as [IHn0 IHn1].
  split; [|apply countdown_repeater_upp_inverse; trivial].
  destruct n; [|apply countdown_countdownable; trivial; apply IHn0].
  split.
  - intro n. rewrite countdown_to_repeat by apply IHn0.
    rewrite inv_hyperop_1_repeat. assert (1 <= a) by omega.
    apply (mult_le_compat_l 1 a n) in H. omega.
  - intros n Hn.
    destruct n; [omega|]. destruct n; [omega|]. 
    rewrite <- le_S_n_m.
    rewrite countdown_to_repeat by apply IHn0.
    rewrite inv_hyperop_1_repeat. apply (Nat.le_sub_le_add_l).
    apply (Nat.le_trans _ ((S n) * 2) _); [omega|].
    apply (mult_le_compat_l 2 a (S n)) in Ha. omega.
Qed.

Corollary inv_hyperop_upp_inverse :
  forall a n, (2 <= a) -> upp_inv_rel (inv_hyperop a n) (hyperop a n).
Proof. apply inv_hyperop_correct. Qed.


(* ****** 5.5. DIVISION AND LOGARITHM ********************************* *)

(* Computes ceiling of b / a *)
Definition div a b := inv_hyperop 2 a b.

Theorem div_correct : forall a b m,
    1 <= a -> div a b <= m <-> b <= m * a.
Proof.
  intros a b m Ha.
  destruct a ; [omega|]. 
  unfold div.
  rewrite inv_hyperop_recursion.
  rewrite countdown_to_repeat by (split; intro n; rewrite inv_hyperop_1; omega).
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
