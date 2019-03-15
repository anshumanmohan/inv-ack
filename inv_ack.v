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


(* Compute inv_ack 7. *)
(* Compute ackermann 2 2. *)