Require Import Omega.
Require Import prelims.


(*
=============================================================================
****************** SECTION 2: COUNTDOWN AND REPEATER ************************
=============================================================================
*)

(* This section contains the actual definition of countdown, as we previously
   only work with its properties (i.e. what countdown should be, rather than
   what it actually is.
   I choose a different approach than my previous approach here, which is
   actually simpler (very straighforward), but will require a longer proof of
   correctness
   What happened to the previous approach? I am trying to clean its code to
   get rid of edge cases (e.g. check if (f n) is below 1 or not), not done yet
   Also, this new approach is both simpler and faster. It takes o(n) time instead
   of O(n) !
   We also introduce the repeater and its relation to countdown *)


(* ****** 2.1. DEFINITION *************************************)

(* Basically, repeats "f" "k" times or until we go below "a".
   Output "min(k, min{l : repeat f l n <= a})" *)
Fixpoint countdown_to_worker (a : nat) (f : nat -> nat) (n k : nat)
: nat :=
match k with
| 0    => 0
| S k' => match (n - a) with
          | 0   => 0
          | S _ => S (countdown_to_worker a f (f n) k') end
end.

(* Actual defintion. We give the worker a budget of "n" steps, which
   guarantees it reach below "a" before terminating *)
Definition countdown_to a f n := countdown_to_worker a f n n.

(* Basically: "f" has a proper countdown to "a" if
   it is a contraction that is strict from "a" *)
Definition countdownable_to (a : nat) (f : nat -> nat) : Prop
:= contracting f /\ contract_strict_from (S a) f.



(* Can be easily defined and computed, so we define it directly *)
Fixpoint repeater_from (a : nat) (f : nat -> nat) (n : nat) : nat
:= match n with
   | 0 => a
   | S n' => f (repeater_from a f n')
end. 


(* ****** 1.2. THEOREMS ************************************* *)


(* *** REPEATER iS REPEAT **** *)
Theorem repeater_from_repeat :
forall a f n, repeater_from a f n = repeat f n a.
Proof.
intros a f n.
induction n. { trivial. }
simpl. rewrite IHn. trivial.
Qed.


(* *** COUNTDOWN CORRECTNESS THEOREMS *** *)

(* INITIAL VALUE THEOREM
   Basically countdown returns 0 if "n" is already below "a" *)
Theorem countdown_to_init : forall a f n k,
(n <= a) -> (countdown_to_worker a f n k = 0).
Proof.
intros a f n k Hna.
unfold countdown_to_worker.
destruct k. { trivial. }
replace (n - a) with 0 by omega.
trivial.
Qed.


(* INTERMEDIATE STATE LEMMA
   Similar to the general recursion formula for "countdown_to_recurse_rel" *)
Theorem countdown_to_intermediate : forall a f n k i,
contracting f
-> S i <= k
-> S a <= repeat f i n
-> countdown_to_worker a f n k
   = (S i) + countdown_to_worker a f (repeat f (S i) n) (k - (S i)).
Proof.
assert (forall a f n k, contracting f -> 1 <= k -> S a <= n
        -> countdown_to_worker a f n k
        = 1 + countdown_to_worker a f (f n) (k - 1)
        ) as case_0.
{ simpl. intros a f n k Hf Hk Ha.
  destruct k. { omega. }
  replace (S k - 1) with k by omega.
  unfold countdown_to_worker.
  replace (n-a) with (S(n - S a)) by omega.
  trivial.
}
intros a f n k i Hf Hik Hai.
induction i.
{ simpl. apply case_0; trivial. }
rewrite IHi.
- simpl. remember (f (repeat f i n)) as m.
  remember (k - S i) as l.
  replace (k - S(S i)) with (l - 1) by omega.
  rewrite case_0.
  + omega.
  + trivial.
  + omega.
  + simpl in Hai. rewrite Heqm. trivial.
- omega.
- apply (Nat.le_trans _ (repeat f (S i) n) _).
  + trivial.
  + apply Hf.
Qed.

(* COUNTDOWN VS REPEAT THEOREM
   This is the correctness theorem for this countdown defintion 
   It asserts that this countdown function obeys the conditions
   set up for countdown in "countdown_repeater.v" *)

Theorem countdown_to_repeat : forall a f n k,
countdownable_to a f -> countdown_to a f n <= k <-> repeat f k n <= a.
Proof.
intros a f n k Haf.
destruct Haf as [Hf Haf].
unfold countdown_to.
split.
- intro. rewrite not_lt. intro.
  rewrite (countdown_to_intermediate a f n n k) in H.
  + omega.
  + apply Hf.
  + apply (Nat.le_trans _ (S k + (repeat f (S k) n)) _).
    * omega.
    * apply (repeat_contract_strict a f n k). apply Hf. apply Haf. apply H0.
  + apply H0.
- intro. destruct k.
  { simpl in H. rewrite (countdown_to_init a f n).
    omega. apply H. }
  remember (n - a) as m.
  destruct m. { rewrite countdown_to_init; omega. }
  destruct (repeat_contract_strict_threshold a f n).
  + apply Hf.
  + apply Haf.
  + omega.
  + destruct H0 as [Hx0 Hx1]. destruct Hx1 as [Hxl Hxr].
    assert (countdown_to_worker a f n n = S x) as Hx.
    { rewrite (countdown_to_intermediate a f n n x).
      - rewrite countdown_to_init. omega. apply Hxl.
      - apply Hf.
      - apply Hx0.
      - apply Hxr. }
    rewrite Hx. apply not_le. intro.
    apply (repeat_contract f n (S k) x) in H0.
    omega. apply Hf.
Qed.

(* RECURSION FOR CONTRACTORS THEOREM *)
Theorem countdown_to_recursion : forall a f n,
countdownable_to a f
-> (n <= a -> countdown_to a f n = 0)
    /\ (S a <= n -> countdown_to a f n = S(countdown_to a f (f n))).
Proof.
intros a f n Hf.
split.
- intro Han. unfold countdown_to.
  apply countdown_to_init. apply Han.
- intro Han.
  assert (countdown_to a f n <= S (countdown_to a f (f n))) as G1.
  { rewrite countdown_to_repeat by apply Hf.
    rewrite repeat_S_comm.
    rewrite <- countdown_to_repeat by apply Hf.
    trivial. }
  assert (1 <= countdown_to a f n) as G0.
  { rewrite le_lt_S. rewrite <- not_le.
    rewrite countdown_to_repeat by apply Hf.
    simpl. omega. }
  assert (countdown_to a f (f n) <= countdown_to a f n - 1).
  { rewrite countdown_to_repeat by apply Hf.
    rewrite <- repeat_S_comm.
    replace (S (countdown_to a f n - 1)) with (countdown_to a f n) by omega.
    rewrite <- countdown_to_repeat by apply Hf.
    trivial. }
  omega.
Qed.

Corollary countdown_to_antirecursion : forall a f n,
countdownable_to a f
-> countdown_to a f (f n) = countdown_to a f n - 1.
Proof.
intros a f n Haf.
assert (H := Haf).
destruct (Nat.lt_ge_cases a n) as [Han | Han];
apply (countdown_to_recursion a f n) in H.
- apply H in Han. omega.
- assert (f n <= a) as Hafn.
  { apply (Nat.le_trans _ n _).
    - apply Haf.
    - apply Han. }
  apply (countdown_to_recursion a f (f n)) in Haf.
  apply Haf in Hafn.
  apply H in Han. omega.
Qed.


(* COUNTDOWNABILITY PRESERVATION THEOREM *)
Theorem countdown_countdownable : forall a f t,
(1 <= a) -> countdownable_to a f
-> countdownable_to t (countdown_to a f).
Proof.
intros a f t Ha Haf.
split.
- intro n. rewrite countdown_to_repeat by apply Haf.
  rewrite not_lt. intro.
  apply repeat_contract_strict in H.
  + omega.
  + apply Haf.
  + apply Haf.
- intros n Hn. destruct n. { omega. }
  rewrite <- le_S_n_m.
  rewrite countdown_to_repeat by apply Haf.
  destruct n. { trivial. }
  remember (repeat f n (S (S n)) - a) as m.
  destruct m.
  { apply (Nat.le_trans _ (repeat f n (S (S n))) _).
    apply Haf. omega. }
  assert (S n + repeat f (S n) (S (S n)) <= (S n) + a).
  { apply (Nat.le_trans _ (S (S n)) _).
    apply (repeat_contract_strict a _ _).
    - apply Haf.
    - apply Haf.
    - omega.
    - omega. }
  omega.
Qed.