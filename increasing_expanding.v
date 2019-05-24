Require Import Omega.
Require Import prelims.
Require Import repeater.

(*
===================================================================================
**** SECTION 3.1 INCREASING FUNCTIONS, UPPER INVERSE AND EXPANSIONS (1)************
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

(* In this PART 1 file, we deal with increasing functions and expansions *)

(* ****** INCREASING FUNCTIONS ****************** *)

(* Usual definition of increasing functions *)
Definition increasing (f : nat -> nat) : Prop :=
  forall n m, n < m -> f n < f m.

(* Usual definition of nondecreasing functions *)
Definition nondecreasing (f : nat -> nat) : Prop :=
  forall n m, n <= m -> f n <= f m.

(* A shortened equivalence of the notion of increasing *)
Lemma incr_S : forall f,
    increasing f <-> forall n, f n < f (S n).
Proof.
  intro f. split; [intros; apply H; omega|].
  unfold increasing. intros.
  generalize dependent n.
  induction m; [intros; inversion H0; omega|]. 
  intros. specialize (H m). inversion H0; trivial.
  apply IHm in H2. omega.
Qed.

(* A shortened equivalence of the notion of nondecreasing *)
Lemma nondecr_S : forall f,
    nondecreasing f <-> forall n, f n <= f (S n).
Proof.
  intro f. split; [intros; apply H; omega|].
  unfold nondecreasing. intros.
  generalize dependent n.
  induction m; [intros; inversion H0; omega|]. 
  intros. inversion H0; [omega|].
  apply IHm in H2. apply (Nat.le_trans _ (f m) _).
  trivial. apply H.
Qed.

(* A stronger but equivalent definition of increasing *)
Lemma incr_twoways : forall f n m,
    increasing f -> (n < m <-> f n < f m).
Proof.
  intros f n m Hf. split.
  - apply Hf.
  - intro Hfnm. rewrite <- not_le. intro. destruct H;
    [ | assert (m < S m0) as H2 by omega; apply Hf in H2]; omega.
Qed.

(* Repeat preserves nondecreasing-ness *)
Lemma repeat_incr : forall k f,
    nondecreasing f -> nondecreasing (repeat f k).
Proof.
  unfold nondecreasing. intros k f Hf.
  induction k; trivial.
  intros; apply Hf; apply IHk; trivial.
Qed.

(* ****** EXPANSIONS ****************** *)

(* Definition of non-strict expansions *)
Definition expanding (f : nat -> nat) : Prop :=
  forall n, n <= f n.

(* Definition of strict expansion *)
Definition expand_strict_from (a : nat) (f : nat -> nat) : Prop :=
  expanding f /\ (forall n, a <= n -> n < f n).

(* Increasing functions are expansions *)
Lemma increasing_expanding :
forall f, increasing f -> expanding f.
Proof.
  intros f Hf n. induction n;
  [ | specialize (Hf n (S n)); apply (Nat.le_trans _ (S (f n)) _)];
  omega.
Qed.

(* Increasing functions that expands strictly at a also expands strictly from a *)
Lemma increasing_expanding_strict :
forall f a, increasing f -> (a < f a) -> expand_strict_from a f.
Proof.
  intros f a Hf Haf. split.
  - apply increasing_expanding. apply Hf.
  - induction n.
    + intro. replace a with 0 in Haf by omega. omega.
    + specialize (Hf n (S n)). intro Han. inversion Han;
      [rewrite <- H | apply IHn in H0; apply (Nat.le_trans _ (S (f n)) _)];
      omega.
Qed.

(* ****** REPEATABLE FUNCTIONS ****************** *)

Definition repeatable_from (a : nat) (f : nat -> nat) : Prop :=
  increasing f /\ expand_strict_from a f.

(* Simplified repeatable conditions *)
Lemma repeatable_simpl :
    forall a f, repeatable_from a f <-> (increasing f /\ a < f a).
Proof.
  intros a f. unfold repeatable_from.
  split; intro; destruct H as [H0 H1]; split; try assumption.
  - apply H1. trivial.
  - apply (increasing_expanding_strict f a H0 H1).
Qed.

(* Repeatability is monotonic *)
Lemma repeatable_monotone :
    forall a b f, (a <= b) -> repeatable_from a f -> repeatable_from b f.
Proof.
  intros a b f Hab Haf. rewrite repeatable_simpl.
  split; apply Haf. omega.
Qed.

(* Important theorem, used to prove the repeatability of the hyperoperations when a >= 2.
   It justifies the need for strict expansions. Since the identity function is
   strictly increasing but non a strict expansions, its repeater is constant.
   Repeatability combines increasing-ness and expansive-ness, which are all preserved
   through repeater, as proved below *)
Lemma repeater_repeatable :
    forall a b f, (0 < a) -> repeatable_from a f -> repeatable_from b (repeater_from f a).
Proof.
  intros a b f Ha. intro.
  apply (repeatable_monotone 0 _ _). omega.
  generalize H. clear H.
  repeat rewrite repeatable_simpl.
  simpl. split; try omega.
  destruct H as [Hf Haf].
  rewrite incr_S. induction n;
  [|simpl; rewrite <- (incr_twoways f _ _ Hf)]; assumption.
Qed.