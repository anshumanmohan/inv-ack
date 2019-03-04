Require Import Omega.
Require Import prelims.


(*
=============================================================================
****************** SECTION 1: COUNTDOWN AND REPEATER ************************
=============================================================================
*)

(* Countdown is non-trivial to define, our approach is to provide a sort of interface
   for it by separating the core property and the actual definition. We provide the
   relation "countdown_to_repeat_rel" to state the condition for "cf" to be the countdown
   to "a" of "f". All facts about countdown can be proven just using this condition
   without touching the real definition, which will be provided later *)

(* ****** 1.1. COUNTDOWN ******************************* *)


(* ****** 1.1.1. DEFINITIONS ********************)

(* Basically says that "cf n" is the minimum number of times we need to
   repeat "f" to get a result less than or equal to "a" *)
Definition countdown_to_repeat_rel (a : nat) (f cf : nat -> nat) : Prop
:= forall n k : nat, cf n <= k <-> repeat f k n <= a.


(* Usual recursive property of countdown : "cf n = 1 + cf (f n)" *)
Definition countdown_to_recurse_rel (a : nat) (f cf : nat -> nat) : Prop
:= forall n, ((n <= a) -> cf n = 0) /\ ((S a <= n) -> cf n = S (cf (f n))).


(* General formula derived from the recursive property above *)
Lemma countdown_to_recurse_formula :
forall a f cf n k, contracting f
-> countdown_to_recurse_rel a f cf
-> S a <= repeat f k n
-> cf n = (S k) + cf (repeat f (S k) n).
Proof.
intros a f cf n k Hf Hfcf Han.
induction k.
{ simpl. simpl in Han. destruct (Hfcf n) as [_ Hfcfn].
  apply Hfcfn. apply Han. }
simpl in Han. rewrite IHk.
- simpl. destruct (Hfcf (f (repeat f k n))) as [_ Hfcfn].
  apply Hfcfn in Han. omega.
- apply (Nat.le_trans _ (f (repeat f k n)) _).
  + apply Han.
  + apply Hf.
Qed.


(* Proof that the two above conditions are equivalent *)
Theorem countdown_to_rel_recursion :
forall a f cf, contracting f
-> contract_strict_from (S a) f
-> (countdown_to_repeat_rel a f cf <-> countdown_to_recurse_rel a f cf).
Proof.
intros a f cf Hf Haf.
unfold countdown_to_repeat_rel.
unfold countdown_to_recurse_rel.
split.
- intros Hfcf n. split.
  + rewrite <- (Hfcf n 0). omega.
  + intro Han. remember (cf (f n)) as k.
    assert (cf n <= S k).
    { rewrite Hfcf. rewrite repeat_S_comm.
      rewrite <- Hfcf. omega. }
    assert (~ cf n <= k).
    { rewrite Hfcf. destruct k. { simpl. omega. }
      rewrite repeat_S_comm. rewrite <- Hfcf.
      omega. }
    omega.
- intros Hfcf n k. split.
  + intro Hkn. rewrite not_lt. intro.
    rewrite (countdown_to_recurse_formula a f cf n k) in Hkn.
    * omega.
    * apply Hf.
    * unfold countdown_to_recurse_rel. apply Hfcf.
    * apply H.
  + remember (n - a) as m.
    destruct m.
    { intro. destruct (Hfcf n) as [Hfcfn _].
      rewrite Hfcfn. omega. omega. }
    assert (S a <= n) as Han by omega.
    destruct (repeat_contract_strict_threshold a f n) as [x Hx].
    * apply Hf.
    * apply Haf.
    * apply Han.
    * intro. destruct Hx as [Hxn Hxna].
      destruct Hxna as [Hxnal Hxnar].
      assert (cf n = S x).
      { rewrite (countdown_to_recurse_formula a f cf n x).
        - destruct (Hfcf (repeat f (S x) n)) as [Hfcfxn _].
          apply Hfcfxn in Hxnal. omega.
        - apply Hf.
        - unfold countdown_to_recurse_rel. apply Hfcf.
        - apply Hxnar. }
      rewrite H0. apply not_le. intro.
      apply (repeat_contract f n k x) in Hf.
      omega. apply H1.
Qed.


(* ****** 1.1.1. PROPERTIES ********************)


(* Countdown preserves increasing-ness of contractions *)
Theorem countdown_to_incr : forall a f cf,
contracting f -> increasing f
-> countdown_to_repeat_rel a f cf -> increasing cf.
Proof.
intros a f cf Hf0 Hf1 Hfcf n m Hnm.
unfold countdown_to_repeat_rel in Hfcf.
rewrite Hfcf.
apply (Nat.le_trans _ (repeat f (cf m) m) _).
- apply (repeat_incr (cf m) f) in Hf1. apply Hf1. apply Hnm.
- rewrite <- Hfcf. trivial.
Qed.


(* Countdown preserves contracting-ness of contractions *)
Theorem countdown_to_contract : forall a f cf,
(1 <= a) -> contracting f
-> contract_strict_from (S a) f
-> countdown_to_repeat_rel a f cf
-> contracting cf /\ contract_strict_from 1 cf.
Proof.
intros a f cf Ha Hf Haf Hfcf.
split.
- intro. rewrite (Hfcf n n).
  rewrite not_lt. intro.
  apply repeat_contract_strict in H.
  + omega.
  + apply Hf.
  + apply Haf.
- intros n Hn. destruct n. { omega. }
  rewrite <- le_S_n_m. rewrite (Hfcf _ n).
  destruct n. { trivial. }
  remember (repeat f n (S (S n)) - a) as m.
  destruct m.
  { apply (Nat.le_trans _ (repeat f n (S (S n))) _).
    apply Hf. omega. }
  assert (S n + repeat f (S n) (S (S n)) <= (S n) + a).
  { apply (Nat.le_trans _ (S (S n)) _).
    apply (repeat_contract_strict a _ _).
    - apply Hf.
    - apply Haf.
    - omega.
    - omega. }
  omega.
Qed.

(* Basically: "f" has a countdown to "a" if
   it is a contraction that is strict from "a" *)
Definition countdownable_to (a : nat) (f : nat -> nat) : Prop
:= contracting f /\ contract_strict_from (S a) f.


(* Just the combination of the two preservation theorems above *)
Theorem countdown_countdownable : forall a f cf,
(1 <= a) -> countdownable_to a f
-> (countdown_to_repeat_rel a f cf)
-> countdownable_to a cf.
Proof.
intros a f cf Ha Haf Hafcf.
destruct Haf as [Haf0 Haf1].
apply (countdown_to_contract a f cf) in Haf0.
- destruct Haf0 as [Hcf0 Hcf1].
  split.
  + apply Hcf0.
  + intros n Han. apply Hcf1. omega.
- apply Ha.
- apply Haf1.
- apply Hafcf.
Qed.


(* ****** 1.2. REPEATER ******************************** *)

(* Can be easily defined and computed, so we define it directly *)
Fixpoint repeater_from (a : nat) (f : nat -> nat) (n : nat) : nat
:= match n with
   | 0 => a
   | S n' => f (repeater_from a f n')
end. 

(* It actually is just "repeat" from "prelims" in disguise *)
Theorem repeater_from_repeat :
forall a f n, repeater_from a f n = repeat f n a.
Proof.
intros a f n.
induction n. { trivial. }
simpl. rewrite IHn. trivial.
Qed.
