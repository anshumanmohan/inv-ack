Require Import Omega.
Require Import Program.Basics.
Require Import prelims.
Require Import countdown_repeater.
Require Import inverse.
Require Import applications.


(*
=============================================================================
**************** SECTION 6: INVERSE ACKERMANN FUNCTION **********************
=============================================================================
 *)

(* This section contains the most important application of countdown,
   the Inverse Ackermann function.
   We first define an inverse tower for the Ackermann hierarchy, then
   write a theorem proving its correctness
   Then we define a structurally terminating definition for the inverse
   Ackermann function, and prove its correctness using the above theorem *)

(* *********** 6.1. INVERSE ACKERMANN HIERARCHY ******************* *)

Fixpoint inv_ack_hier m x :=
  match m with
  | 0 => x - 1
  | S m' => countdown_to 1 (inv_ack_hier m') (inv_ack_hier m' x)
  end.

Theorem inv_ack_hier_correct :
  forall m, countdownable_to 1 (inv_ack_hier m) /\
            upp_inv_rel (inv_ack_hier m) (ackermann m).
Proof.
  induction m.
  { split.
    - split; intro x; simpl; omega.
    - intros n x. simpl. omega. }
  destruct IHm as [IHm0 IHm1]. split.
  - simpl. split; intro n;
             rewrite countdown_to_antirecursion by apply IHm0;
             apply (countdown_countdownable 1 _ 1) in IHm0;
             destruct IHm0 as [IHm00 IHm01]; trivial.
    + specialize (IHm00 n). omega.
    + specialize (IHm01 n). omega.
  - intros n x. simpl. rewrite repeater_from_repeat.
    rewrite <- repeat_S_comm.
    apply (upp_inv_repeat (S n) _ _) in IHm1.
    rewrite <- (IHm1 1 x), repeat_S_comm.
    apply countdown_to_repeat. apply IHm0.
Qed.


(* *********** 6.2. INVERSE ACKERMANN FUNCTION ******************** *)

Fixpoint inv_ack_worker (f : nat -> nat) (n thr bud : nat) : nat :=
  match bud with
  | 0 => 0
  | S bud' =>
    match (n - thr) with
    | 0 => 0
    | S _ =>
      match (countdown_to 1 f) with
        g => S (inv_ack_worker (compose g f) (g n) (S thr) bud') end
    end
  end.

Definition inv_ack n :=
  match (inv_ack_hier 0) with f => inv_ack_worker f (f n) 0 n end.

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

(* *********** 6.3. TIME ANALYSIS ********************* *)

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

(* Compute rtime 2 13. *)
