Require Import BinNat.
Require Import Nnat.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Omega.
Require Import prelims.

Require increasing_expanding.

Open Scope N_scope.


(*
=============================================================================
****************** SECTION 1: PRELIMINARIES *********************************
=============================================================================
 *)

(* This file contains recurrently useful results and definitions
   that are used throughout the subsequent files *)

Lemma le_antisym: forall m n : N, (m <= n) -> (n <= m) -> (m = n).
Proof. intros. lia. Qed.

(* ****** N TO nat COMPARISON CONVERSION ******** *)

Lemma le_N_nat : forall m n : N, (m <= n) <-> (N.to_nat m <= N.to_nat n)%nat.
Proof.
  intros m n. rewrite <- N.compare_le_iff.
  rewrite N2Nat.inj_compare. apply Nat.compare_le_iff.
Qed.

Lemma le_nat_N : forall m n : nat, (m <= n)%nat <-> (N.of_nat m <= N.of_nat n).
Proof.
  intros m n. rewrite <- Nat.compare_le_iff.
  rewrite Nat2N.inj_compare. apply N.compare_le_iff.
Qed.

Lemma lt_N_nat : forall m n : N, (m < n) <-> (N.to_nat m < N.to_nat n)%nat.
Proof.
  intros m n. rewrite <- N.compare_lt_iff.
  rewrite N2Nat.inj_compare. apply Nat.compare_lt_iff.
Qed.

Lemma lt_nat_N : forall m n : nat, (m < n)%nat <-> (N.of_nat m < N.of_nat n).
Proof.
  intros m n. rewrite <- Nat.compare_lt_iff.
  rewrite Nat2N.inj_compare. apply N.compare_lt_iff.
Qed.


(* ****** REPEATED APPLICATION ************ *)

Fixpoint repeat (f: N -> N) (rep : nat) (n : N) : N :=
  match rep with
  | O => n
  | S rep' => f (repeat f rep' n)
  end.

Theorem repeat_S_comm :
    forall f k n, repeat f (S k) n = repeat f k (f n).
Proof.
  induction k; trivial. intro. simpl in *. rewrite IHk. trivial.
Qed.

Theorem repeat_plus :
    forall f k l n, repeat f (k + l) n = repeat f k (repeat f l n).
Proof. induction k; trivial. simpl; intros; rewrite IHk; trivial. Qed.

(* ****** INCREASING FUNCTIONS ****** *)
Definition increasing (f : N -> N) : Prop :=
  forall n m, n < m -> f n < f m.


(* ****** NAT_SIZE ************ *)

(* Length of the binary representation *)
Definition nat_size (n : N) : nat :=
  match n with
  | 0 => 0%nat
  | Npos p => let fix nat_pos_size (x : positive) : nat :=
                  match x with
                  | xH => 1%nat
                  | xI y | xO y => S (nat_pos_size y) end
                  in nat_pos_size p
  end.

(* nat_size is increasing *)
Lemma nat_size_incr :
    forall m n, m <= n -> (nat_size m <= nat_size n)%nat.
Proof.
  intros m n Hmn.
  destruct m as [|pm]. simpl. omega.
  destruct n as [|pn]. lia.
  generalize dependent pm.
  induction pn;
  intros; [ | |replace (Npos pm) with 1 by lia; trivial];
  destruct pm; simpl; try omega; apply le_n_S; apply IHpn; lia.
Qed.


(* Binary contraction contracts size *)
Lemma div2_nat_size :
    forall m n, 0 < n -> m <= N.div2 n -> (1 + nat_size m <= nat_size n)%nat.
Proof.
  intros m n Hn Hmn. apply (Nat.le_trans _ (1 + nat_size (N.div2 n)) _).
  - apply le_n_S. apply nat_size_incr. apply Hmn.
  - destruct n; try lia.
    destruct p; trivial.
Qed.

Lemma div2_contr :
    forall m n, 0 < n -> m <= N.div2 n -> m < n.
Proof.
  intros m n Hn Hmn. apply (div2_nat_size m n Hn) in Hmn.
  rewrite N.lt_nge. intro. apply nat_size_incr in H. omega.
Qed.

Lemma nat_size_contract : forall n, (nat_size n <= N.to_nat n)%nat.
Proof. destruct n; trivial. simpl. induction p; simpl; lia. Qed.


(* ****** NAT TO N CONVERSION ************ *)

Definition to_N_func (f : nat -> nat) (n : N) : N := N.of_nat (f (N.to_nat n)).

Definition to_nat_func (f : N -> N) (n : nat) : nat := N.to_nat (f (N.of_nat n)).

Theorem N_nat_func_id : forall (f : N -> N), f = to_N_func (to_nat_func f).
Proof.
  intro f. apply functional_extensionality. intro n.
  unfold to_N_func. unfold to_nat_func. repeat rewrite N2Nat.id. trivial.
Qed.

Theorem nat_N_func_id : forall (f : nat -> nat), f = to_nat_func (to_N_func f).
Proof.
  intro f. apply functional_extensionality. intro n.
  unfold to_N_func. unfold to_nat_func. repeat rewrite Nat2N.id. trivial.
Qed.

Lemma to_N_func_repeat : forall f k,
    repeat f k = to_N_func (prelims.repeat (to_nat_func f) k).
Proof.
  intros f k. induction k; apply functional_extensionality;
  intro n; simpl; unfold to_N_func; [symmetry; apply N2Nat.id|repeat f_equal].
  rewrite IHk. unfold to_nat_func. rewrite N2Nat.id. unfold to_N_func. trivial.
Qed.

Lemma to_nat_func_repeat : forall f k,
    prelims.repeat f k = to_nat_func (repeat (to_N_func f) k).
Proof.
  intros f k. induction k; apply functional_extensionality;
  intro n; simpl; unfold to_nat_func; [symmetry; apply Nat2N.id|repeat f_equal].
  rewrite IHk. unfold to_N_func. rewrite Nat2N.id. unfold to_nat_func. trivial.
Qed.

Lemma to_nat_func_incr : forall f,
    increasing f <-> increasing_expanding.increasing (to_nat_func f).
Proof.
  split; unfold to_nat_func; intros Hf m n.
  - rewrite lt_nat_N. rewrite <- lt_N_nat. apply Hf.
  - repeat rewrite lt_N_nat. intro. apply Hf in H.
    repeat rewrite N2Nat.id in H. apply H.
Qed.