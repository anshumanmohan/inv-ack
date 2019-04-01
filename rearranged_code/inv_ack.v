Require Import Omega.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.
Require Import inverse.
Require Import countdown.
Require Import applications.


(* This section contains the most important application of countdown,
   the Inverse Ackermann function.
   We first define an inverse tower for the Ackermann hierarchy, then
   write a theorem proving its correctness
   Then we define a structurally terminating definition for the inverse
   Ackermann function, and prove its correctness using the above theorem *)

(* *********** INVERSE ACKERMANN HIERARCHY ******************* *)

Fixpoint alpha m x :=
  match m with
  | 0 => x - 1
  | S m' => countdown_to 1 (alpha m') (alpha m' x)
  end.

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
  apply repeater_repeatable in IHi; try omega;
  destruct IHi as [IHi0 IHi1];
  [intro; apply IHi0; omega | |];
  apply (Nat.le_trans _ (S (S n)) _); try apply IHi1; omega.
Qed.

(* Ackermann at level 1 *)
Lemma ack_1 : forall n, ackermann 1 n = (S (S n)).
Proof.
  induction n; [|rewrite ackermann_recursion; rewrite IHn]; trivial.
Qed.

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


(* Compute inv_ack 7. *)
(* Compute ackermann 2 2. *)
(* Time Compute inv_ack 62. *)
(* Time Compute inv_ack_naive_outer 65. *) (* too slow *)
(* Time Compute inv_ack_target_outer 65. *)
(* Time Compute inv_ack 1000. *)
(* Time Compute inv_ack_target_outer 1000. *)

(* *********** 6.3. TIME ANALYSIS ********************
   TODO: Think whether I want to keep this section or not.
   TODO: If yes, complete it WITHIN 1 WEEK after deadline *)

(*
Definition next_lvl f := compose (countdown_to 1 f) f.

Fixpoint alpha i : nat -> nat :=
match i with
| 0 => (fun b => b - 2)
| S i' => next_lvl (alpha i')
end.

Fixpoint compose_sum (t : nat -> nat) (f : nat -> nat) k n : nat :=
match k with
| 0 => t n
| S k' => t n + compose_sum t f k' (f n)
end.

Fixpoint rtime i n : nat :=
match i with
| 0 => 1
| S i' => compose_sum (rtime i') (alpha i') (countdown_to 1 (alpha i') n) n + (alpha i n)
end.
*)

(* Compute rtime 2 13. *)
