Require Import Omega.
Require Import prelims.
Require Import countdown_repeater.

(*
=============================================================================
****************** SECTION 2: UPPER AND LOWER INVERSE RELATION **************
=============================================================================
 *)

(* This section is for upper (and lower, not yet complete) inverse relations
   The upper inverse is much less painful to define and used in proofs
   The lower inverse is hadrder because it does not always exists, thus
   requires more attention to edge cases, which results in complicated proofs.
   Also: (n - 2) is the upper inverse of (n + 2) but NOT the lower inverse *)

(* ****** 2.1. UPPER AND LOWER INVERSES ***************** *)

(* f is the upper inverse of F: f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : nat -> nat) : Prop :=
  forall n N, f N <= n <-> N <= F n.

Lemma upp_inv_rel_fact: forall f F, upp_inv_rel f F ->
  forall n, f (F n) = n.
Proof.
  intros.
  assert (f (F n) <= n) by (now rewrite (H _ _)).
  assert (F n <= F (f (F n))). {
    rewrite <- (H _ _). trivial. }
  assert (n <= f (F n) \/ n > f (F n)) by omega.
  destruct H2. omega.
  Admitted.

(* f is the lower inverse of F: f N is the largest n such that F n <= N *)
Definition low_inv_rel_from_a (a : nat) (f F : nat -> nat) : Prop :=
  forall n N, n <= f N <-> F n <= max a N.


(* ****** 2.2. PROPERTIES PRESERVED BY INVERSES **************** *)

(* Actually this section contains some redundant properties that I
  haven't used in any proof *)

(* Expansions, the counterpart of contractions *)
Definition expanding (F : nat -> nat) : Prop :=
  forall n, n <= F n.

Definition expand_strict_from (a : nat) (F : nat -> nat) : Prop :=
  forall n, a <= n -> S n <= F n.

(* If the upper inverse of "F" is a contraction, then "F" is an expansion *) 
Lemma contract_upp_inv_expand :
  forall a f F,
    contract_strict_from (S a) f -> upp_inv_rel f F ->
    expand_strict_from a F.
Proof.
  intros a f F Hf HfF n Han.
  rewrite <- (HfF n _). rewrite le_S_n_m.
  apply (Hf (S n)). rewrite <- le_S_n_m. apply Han.
Qed.

(* Basically, since "F" is an expansion, "F n >= 1 + n > 0" *)
Lemma contract_upp_inv_positive :
  forall n f F, contract_strict_from 1 f -> upp_inv_rel f F -> 0 < F n.
Proof.
  intros n f F Hf HfF.
  apply (Nat.le_trans _ (S n) _); [omega|]. 
  apply (contract_upp_inv_expand 0 f F); trivial. omega.
Qed.

(* If the upper inverse of "F" is increasing, so is "F" *)
Lemma contract_incr_upp_inv_incr :
  forall f F,
    contract_strict_from 1 f -> increasing f ->
    upp_inv_rel f F -> increasing F.
Proof.
  intros f F Hf_sh Hf_in HfF. rewrite incr_S. intro.
  rewrite <- (HfF (S n) _). apply (Nat.le_trans _ n _); [|omega].
  rewrite (HfF n _). trivial.
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

(*
Lemma contract_low_inv_positive :
forall n f F, contract_strict_from 1 f -> low_inv_rel_from_a 1 f F
-> (1 <= n) -> (0 < F n).
Proof.
intros n f F Hf HfF.
apply (Nat.le_trans _ (S n) _). { omega. }
apply (contract_low_inv_expand 1 f F); trivial.
omega.
Qed.

Lemma contract_low_inv_expand :
forall a f F, contract_strict_from a f -> low_inv_rel_from_a a f F -> expand_strict_from a F.
Proof.
intros a f F Hf HfF n Han.
rewrite le_lt_S.
rewrite <- not_le.
assert (max a n = n) as Hman by (apply Nat.max_r_iff; trivial).
rewrite <- Hman.
rewrite <- (HfF _ n).
rewrite Hman.
apply (Hf n) in Han.
omega.
Qed.

Lemma contract_incr_low_inv_incr :
forall f F, contracting f -> increasing f -> low_inv_rel f F -> increasing F.
Proof.
intros f F Hf_sh Hf_in HfF. rewrite incr_S. intro.
rewrite <- (HfF n _). apply (Nat.le_trans _ (S n) _).
- omega.
- rewrite (HfF (S n) _). trivial.
Qed.
 *)

(* ****** 2.3. COUNTDOWN - REPEATER - INVERSE PRESERVATION **************** *)

(* This theorem is important. It says that the countdown and repeater will
   preserve the upper inverse relation on their respective results
   This is needed to prove that the tower (n - 2), ceil(n/2), ceil(log_2(n)), ...
   is the upper inverse of the tower (n + 2), 2n, 2^n, ...
   However I haven't cleaned that part in the old code yet *)

Theorem countdown_repeater_upp_inverse : forall a f F,
    countdownable_to a f -> upp_inv_rel f F ->
    upp_inv_rel (countdown_to a f) (repeater_from a F).
Proof.
  intros a f F Haf HfF n N.
  rewrite repeater_from_repeat.
  apply (upp_inv_repeat n _ _) in HfF.
  rewrite <- (HfF a N). apply countdown_to_repeat. apply Haf.
Qed.