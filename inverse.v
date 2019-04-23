Require Import Omega.
Require Import Program.Basics.
Require Import Logic.FunctionalExtensionality.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.

(*
===================================================================================
**** SECTION 3.1 INCREASING FUNCTIONS, UPPER INVERSE AND EXPANSIONS (2)************
===================================================================================
 *)

(* In Section 3.1, we introduce the notion of "upper inverse" (upp_inv),
   increasing functions and why we prefer to consider inverse of
   increasing functions only.
   We prove several use results about upper inverse and increasing functions
   We introduce "expansions" and how they are connected to increasing functions
   through repeater.
   Increasing functions that are strict expansions serve as the target for us
   to compute the upper inverse with "countdown" later on. *)

(* In this PART 2 file, we deal with upper inverse of increasing functions *)


(* ****** UPPER INVERSE ****************** *)

(* f is the upper inverse of F: f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : nat -> nat) : Prop :=
    forall n N, f N <= n <-> N <= F n.

(* An increasing F has a recursively definable upper inverse
   Under assumption F is increasing, the below definition will compute its upper inverse
   Do not use it for not always increasing functions
   This is sort of why we are only interested in inverses of increasing functions
   Inverses of other functions on naturals are hard to define neatly and do not
   behave nicely.
   This computation implies the upper inverse exists, which is useful for
   proofs about worker functions later on *)
Fixpoint upp_inv (F : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => let m := upp_inv F n' in
            if F m =? n' then S m else m
  end.

(* Proof that the above upper inverse definition is correct *)
Theorem upp_inv_correct :
    forall F, increasing F -> upp_inv_rel (upp_inv F) F.
Proof.
  intros F HF n N. generalize dependent n.
  induction N; intro n.
  - simpl. omega.
  - assert (N <= F (upp_inv F N)) as HN by (apply IHN; omega).
    simpl. remember (upp_inv F N) as m. remember (F m =? N) as b.
    symmetry in Heqb. destruct b.
    + rewrite Nat.eqb_eq in Heqb. rewrite <- Heqb.
      apply incr_twoways. apply HF.
    + rewrite Nat.eqb_neq in Heqb.
      assert (N < F m) as HNm by omega.
      split; rewrite IHN;
      [rewrite <- IHN; rewrite not_lt; rewrite incr_twoways by apply HF | ];
      omega.
Qed.

(* Proof that upper inverse is unique *)
Theorem upp_inv_unique :
    forall f F, increasing F -> (upp_inv_rel f F <-> f = upp_inv F).
Proof.
  intros f F HF.
  assert (upp_inv_rel (upp_inv F) F) as H by (apply upp_inv_correct; apply HF).
  split; intro.
  - apply functional_extensionality. intro N.
    assert (f N <= upp_inv F N).
    { rewrite (H0 _ N). rewrite <- (H _ N). trivial. }
    assert (upp_inv F N <= f N).
    { rewrite (H _ N). rewrite <- (H0 _ N). trivial. }
    omega.
  - rewrite H0. trivial.
Qed.

(* Composing F's inverse and F gives identity *)
Theorem upp_inv_compose :
    forall f F, increasing F -> upp_inv_rel f F -> compose f F = id.
Proof.
  intros f F HF HfF. apply functional_extensionality. intro n.
  unfold id. unfold compose.
  assert (f (F n) <= n) as H0.
  { rewrite (HfF n (F n)). trivial. }
  assert (n <= f (F n)) as H1.
  { rewrite not_lt. rewrite (incr_twoways F (f (F n)) n HF).
    rewrite <- not_lt. rewrite <- (HfF (f (F n)) (F n)). trivial. }
  omega.
Qed.

(* Repeat preserves upper inverse relation *)
Lemma upp_inv_repeat : forall k f F,
    upp_inv_rel f F -> upp_inv_rel (repeat f k) (repeat F k).
Proof.
  unfold upp_inv_rel. intros k f F HfF. induction k.
  1: intros n N; simpl; reflexivity.
  intros n N. rewrite repeat_S_comm. split.
  - intro. rewrite IHk in H. simpl. apply HfF. apply H.
  - simpl; rewrite <- HfF; rewrite IHk; trivial.
Qed.