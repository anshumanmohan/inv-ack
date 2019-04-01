Require Import Omega.
Require Import prelims.

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
  expanding f /\ (forall n, a <= n -> S n <= f n).

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