Require Import Omega.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.
Require Import inverse.
Require Import countdown.
Require Import applications.

(*
==========================================================================
************** SECTION 4.2 THE INVERSE ACKERMANN FUNCTION ****************
==========================================================================
 *)

(* This section contains the most important application of countdown,
   the Inverse Ackermann function.
   We first define an inverse tower for the Ackermann hierarchy, then
   write a theorem proving its correctness
   Then we define a structurally terminating definition for the inverse
   Ackermann function, and prove its correctness using the above theorem
   We state and prove the correctness of the improvement, which runs in linear time
   At the end, we also sketch a naive approach to the inverse Ackermann function,
   which uses brute force search, and a massive improvement over it, but still slower
   than our main method for inv_ack, although we do not prove it at the moment
*)

(* *********** INVERSE ACKERMANN HIERARCHY ******************* *)

(* Definition *)
Fixpoint alpha m x :=
  match m with
  | 0 => x - 1
  | S m' => countdown_to 1 (alpha m') (alpha m' x)
  end.

(* Definition *)
Theorem alpha_correct :
  forall m, contract_strict_above 1 (alpha m) /\
            upp_inv_rel (alpha m) (ackermann m).
Proof.
  induction m.
  { split.
    - split; intro x; simpl; omega.
    - intros n x. simpl. omega. }
  destruct IHm as [IHm0 IHm1]. split.
  - simpl. split; intro n;
             rewrite countdown_antirecursion by apply IHm0;
             apply (countdown_contract_strict 1 _ 1) in IHm0;
             destruct IHm0 as [IHm00 IHm01]; trivial.
    + specialize (IHm00 n). omega.
    + specialize (IHm01 n). omega.
  - intros n x. simpl. rewrite repeater_from_repeat.
    rewrite <- repeat_S_comm.
    apply (upp_inv_repeat (S n) _ _) in IHm1.
    rewrite <- (IHm1 1 x), repeat_S_comm.
    apply countdown_repeat. apply IHm0.
Qed.


(* *********** INVERTABILITY OF ACKERMANN FUNCTION ************ *)

(* Repeatability *)
Lemma ack_repeatable : forall i, repeatable_from 0 (ackermann i).
Proof.
  induction i; split; try split;
  intro n; try intro m; simpl; try omega;
  apply (repeatable_monotone 0 1 _) in IHi; try omega;
  repeat rewrite repeater_from_repeat;
  repeat rewrite <- repeat_S_comm;
  repeat rewrite <- repeater_from_repeat;
  apply (repeater_repeatable _ 0 _) in IHi; try omega;
  destruct IHi as [IHi0 IHi1];
  [intro; apply IHi0; omega | |];
  apply (Nat.le_trans _ (S (S n)) _); try apply IHi1; omega.
Qed.

(* Ackermann at level 1. It is useful for 2 purposes:
   (1) Compute alpha 1 below, which is used in hard-coding the second level
   for linear runtime.
   (2) Serves to prove base case for "ack_incr_by_lvl"  *)
Lemma ack_1 : forall n, ackermann 1 n = (S (S n)).
Proof.
  induction n; [|rewrite ackermann_recursion; rewrite IHn]; trivial.
Qed.

(* Alpha at level 1. Used in hard-coding the second level for linear runtime *)
Lemma alpha_1 : alpha 1 = (fun n => n - 2).
Proof.
  assert (upp_inv_rel (alpha 1) (ackermann 1)) as H by apply alpha_correct.
  assert (upp_inv_rel (fun n => n - 2) (ackermann 1)) as H'.
  { intros n m. rewrite ack_1. omega. }
  rewrite upp_inv_unique in H by
   (intros n m; repeat rewrite ack_1; omega).
  rewrite upp_inv_unique in H' by
   (intros n m; repeat rewrite ack_1; omega).
  rewrite H'. apply H.
Qed.

(* Below two results asserts that the diagonal Ackermann function is increasing,
   hence has a proper upper inverse. We need them because we need to compute the inverse
   value for the inv_ack correctness proof later *)

(* Strict Increasing With Level *)
Lemma ack_incr_by_lvl :
    forall n, increasing (fun i => ackermann i n).
Proof.
  intro n. rewrite incr_S. intro i. generalize dependent n.
  induction i; intro n.
  - rewrite ack_1. simpl. omega.
  - remember (S i) as p. destruct n.
    + simpl. apply ack_repeatable. omega.
    + rewrite ackermann_recursion. apply ack_repeatable.
      assert (Hi := IHi).
      rewrite Heqp in IHi. specialize (IHi (S n)).
      rewrite ackermann_recursion in IHi.
      rewrite <- incr_twoways in IHi by apply ack_repeatable.
      apply (Nat.lt_trans _ (ackermann (S i) n) _); trivial.
      clear IHi. induction n.
      * simpl. apply Hi.
      * repeat rewrite ackermann_recursion.
        apply (Nat.lt_trans _ (ackermann i (ackermann (S p) n)) _).
        apply ack_repeatable; assumption.
        apply Hi.
Qed.

(* Diagonal Strict Increasing *)
Lemma diag_ack_incr : increasing (fun n => ackermann n n).
Proof.
  intros n m Hnm. apply (Nat.lt_trans _ (ackermann n m) _);
  [apply ack_repeatable| apply ack_incr_by_lvl]; assumption.
Qed.


(* *********** INVERSE ACKERMANN FUNCTION ******************** *)

Fixpoint inv_ack_worker (f : nat -> nat) (n k bud : nat) : nat :=
  match bud with
  | 0      => 0
  | S bud' =>
    match (n - k) with
    | 0   => k
    | S _ =>
      let g := (countdown_to 1 f) in
      inv_ack_worker (compose g f) (g n) (S k) bud'
    end
  end.

(* Original defintion, runtime O(n^2) *)
Definition inv_ack n :=
  match (alpha 0) with f => inv_ack_worker f (f n) 0 n end.

(* Intermediate lemma about inv_ack_worker *)
Lemma inv_ack_worker_intermediate :
    forall i n b, (i < alpha i n) -> (i < b) ->
        (inv_ack_worker (alpha 0) (alpha 0 n) 0 b
         = inv_ack_worker (alpha (S i)) (alpha (S i) n) (S i) (b - (S i))).
    induction i.
    - simpl. intros n b Hn Hb. unfold inv_ack_worker.
      destruct b; try omega.
      remember ((n - 1) - 0) as m. destruct m; try omega.
      replace (S b - 1) with b by omega. trivial.
    - intros n b Hn Hb. rewrite IHi.
      + remember (S i) as p.
        replace (alpha (S p)) with
        (compose (countdown_to 1 (alpha p)) (alpha p)) by trivial.
        unfold inv_ack_worker.
        remember (alpha p n - p) as m. destruct m; try omega.
        remember (b - p) as c. destruct c; try omega.
        replace (b - S p) with c by omega.
        rewrite <- Heqm. trivial.
      + rewrite <- not_le. destruct (alpha_correct i) as [_ Halphai].
        rewrite (Halphai i n). intro.
        assert (n <= ackermann (S i) (S i)).
        { apply (Nat.le_trans _ (ackermann i i) _); trivial.
          apply Nat.lt_le_incl. apply diag_ack_incr. omega. }
        destruct (alpha_correct (S i)) as [_ HalphaSi].
        rewrite <- (HalphaSi (S i) n) in H0. omega.
      + omega.
Qed.

(* Proof that inv_ack is correct *)
Theorem inv_ack_correct :
  upp_inv_rel inv_ack (fun k => ackermann k k).
Proof.
  rewrite upp_inv_unique by apply diag_ack_incr.
  assert (forall n N : nat,
            upp_inv (fun k : nat => ackermann k k) N <= n
            <-> alpha n N <= n) as H.
  { intros n N.
    rewrite (upp_inv_correct (fun k : nat => ackermann k k)
           diag_ack_incr n N). destruct (alpha_correct n) as [_ Hm].
    symmetry. apply Hm. }
  apply functional_extensionality. intro n.
  remember (upp_inv (fun k : nat => ackermann k k) n) as m.
  unfold inv_ack. assert (H0 := H). destruct m.
  - specialize (H 0 n). rewrite <- Heqm in H.
    assert (n <= 1) as Hn. { simpl in H. omega. }
    destruct n; simpl; trivial; destruct n; simpl; trivial; omega.
  - specialize (H m n). rewrite <- Heqm in H.
    assert (m < alpha m n) as Hn by omega.
    assert (S m < n) as Hmn.
    { destruct (alpha_correct m) as [_ Hm]. rewrite <- not_le in Hn.
      rewrite (Hm m n) in Hn. rewrite <- not_le. intro.
      assert (ackermann m m <= m) by omega.
      destruct (ack_repeatable m) as [_ Hackm].
      destruct Hackm as [_ Hackm]. specialize (Hackm m).
      omega. }
    rewrite (inv_ack_worker_intermediate m n n).
    assert (alpha (S m) n - (S m) = 0).
    { specialize (H0 (S m) n). rewrite <- Heqm in H0. omega. }
    unfold inv_ack_worker.
    remember (n - S m) as p. destruct p; try omega.
    + rewrite H1. trivial.
    + assumption.
    + omega.
Qed.

(* ****** INVERSE ACKERMANN BY HARD-CODING SECOND LEVEL ************* *)

(* Definition by hard-coding the second alpha level, runtime O(n) *)
Definition inv_ack' n :=
  match n with
  | 0 | 1 => 0
  | _     => match (fun x => x - 2) with f
             => inv_ack_worker f (f n) 1 (n - 1) end
  end.

(* Correctness proof *)
Theorem inv_ack'_correct : inv_ack' = inv_ack.
Proof.
  apply functional_extensionality. intro n.
  unfold inv_ack. unfold inv_ack'.
  destruct n; try destruct n; trivial.
  rewrite (inv_ack_worker_intermediate 0 _ _) by (simpl; omega).
  rewrite alpha_1. trivial.
Qed.


(* *********** NAIVE INVERSE ACKERMANN FUNCTION ******************** *)

Fixpoint inv_ack_naive (n : nat) (ans : nat) (bud : nat) : nat :=
  match bud with
  | 0 => 0
  | S bud' =>
    match n - (ackermann ans ans) with
    | 0 => ans
    | _ => inv_ack_naive n (S ans) bud'
    end
  end.

Definition inv_ack_naive_outer n := inv_ack_naive n 0 n.

(* Compute inv_ack_naive_outer 62. *)
(* Obviously this gets busy calculating A(4). *)

(* So let's try to do better: 
   Stop calculating A(4) the moment the "rolling answer" blows past n.
   This works out well because Ackermann grows monotonically even _within_ the calculation of a single term.
 *)

(* 
 * Here we have a tail-recursive variant of repeater_from, 
 * with an added feature: 
 * If we cross the "target", we stop and return 
 * our working answer 
*)
Fixpoint repeater_from_tail_target ans f n target : nat :=
  match target - ans with
  | 0 => ans
  | _ =>
    match n with
    | 0 => ans
    | S n' => repeater_from_tail_target (f ans) f n' target
    end
  end.

Fixpoint ackermann_target target m n :=
  match m with
  | 0 => S n
  | S m' => repeater_from_tail_target (ackermann_target target m' 1) (ackermann_target target m') n target
  end.

(* Compute ackermann_target 70 4 4. *)
(* --> returns 70 immediately. Because it is not
   concerned with actually calculating A(4,4). *)

Fixpoint inv_ack_target (n : nat) (ans : nat) (bud : nat) : nat :=
  match bud with
  | 0 => 0
  | S bud' =>
    match (n - (ackermann_target n ans ans)) with
    | 0 => ans
    | _ => inv_ack_target n (ans + 1) (bud')
    end
  end.

Definition inv_ack_target_outer n := inv_ack_target n 0 n.