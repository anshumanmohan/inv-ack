Require Import Omega.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.
Require Import inverse.


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


(* ****** DEFINITION *************************************)

(* Basically, repeats "f" "k" times or until we go below "a".
   Output "min(k, min{l : repeat f l n <= a})" *)
Fixpoint countdown_worker (a : nat) (f : nat -> nat) (n k : nat) : nat :=
  match k with
  | 0    => 0
  | S k' => match (n - a) with
            | 0 => 0
            | _ => S (countdown_worker a f (f n) k') end
  end.

(* Actual defintion. We give the worker a budget of "n" steps, which
   guarantees it reach below "a" before terminating *)
Definition countdown_to a f n := countdown_worker a f n n.


(* *** COUNTDOWN CORRECTNESS THEOREMS *** *)

(* INITIAL VALUE THEOREM
   Basically countdown returns 0 if "n" is already below "a" *)
Theorem countdown_init : forall a f n k,
    n <= a -> countdown_worker a f n k = 0.
Proof.
  intros a f n k Hna.
  unfold countdown_worker.
  destruct k; trivial.
  replace (n - a) with 0 by omega; trivial.
Qed.


(* EXISTENCE OF COUNTDOWN VALUE LEMMA *)
(* Basically the existence of the countdown value for strict contractions
   It asserts there is a minimum "l" for which repeating "f" "l" times from "n"
   will give a result less than or equal to "a" *)
Lemma repeat_contract_strict_threshold :
  forall a f n,
    contract_strict_above a f -> S a <= n ->
    exists l, (S l) <= n /\ repeat f (S l) n <= a < repeat f l n.
Proof.
  intros a f n Hf Han. destruct Hf as [Hf Haf].
  remember (n - a) as m.
  destruct m; [omega|].
  assert (forall b, (a <= b) -> f (S b) <= b) as Ha.
  { intros b Hab. rewrite le_S_n_m. apply Haf. omega. }
  generalize dependent a.
  induction m.
  - intros. exists 0.
    simpl. split; [|split];
             [|replace n with (S a) by omega; apply Ha|]; omega.
  - intros. destruct (IHm (S a)); try omega.
    + intros p Hp. apply Haf. omega.
    + intros b Hab. apply Ha. omega.
    + destruct H as [H0 H1]. destruct H1 as [Hl Hr]. inversion Hl.
      2: exists x; split; [apply H0 | omega].
      exists (S x). simpl. rewrite H1. split.
      2: split; [apply Ha|]; omega.
      apply (Nat.le_trans _ (S x + (repeat f (S x) n)) _);
                  [simpl; rewrite H1; omega|].
      apply (repeat_contract_strict a f n x). split; assumption. omega.
Qed.


(* INTERMEDIATE STATE LEMMA
   Similar to the general recursion formula for "countdown_recurse_rel" *)
Theorem countdown_intermediate : forall a f n k i,
    contracting f -> S i <= k ->
    S a <= repeat f i n ->
    countdown_worker a f n k =
    (S i) + countdown_worker a f (repeat f (S i) n) (k - (S i)).
Proof.
  assert (forall a f n k,
             contracting f -> 1 <= k -> S a <= n ->
             countdown_worker a f n k =
             1 + countdown_worker a f (f n) (k - 1) ) as case_0.
  { simpl. intros a f n k Hf Hk Ha.
    destruct k; [omega|]. 
    replace (S k - 1) with k by omega.
    unfold countdown_worker.
    replace (n - a) with (S (n - S a)) by omega. trivial.
  }
  intros a f n k i Hf Hik Hai.
  induction i; [simpl; apply case_0; trivial|]. rewrite IHi; [|omega|].
  - simpl. remember (f (repeat f i n)) as m.
    remember (k - S i) as l.
    replace (k - S(S i)) with (l - 1) by omega.
    rewrite case_0; [omega | trivial | omega|].
    simpl in Hai. rewrite Heqm. trivial.
  - apply (Nat.le_trans _ (repeat f (S i) n) _); [trivial | apply Hf].
Qed.

(* COUNTDOWN VS REPEAT THEOREM
   This is the correctness theorem for this countdown defintion 
   It asserts that this countdown function obeys the conditions
   set up for countdown in "countdown_repeater.v" *)

Theorem countdown_repeat : forall a f n k,
    contract_strict_above a f -> countdown_to a f n <= k <-> repeat f k n <= a.
Proof.
  intros a f n k Haf. inversion Haf as [Hf _].
  unfold countdown_to; split.
  - intro. rewrite not_lt. intro.
    rewrite (countdown_intermediate a f n n k Hf) in H; [omega | trivial..].
    apply (Nat.le_trans _ (S k + (repeat f (S k) n)) _); [omega|].
    apply (repeat_contract_strict a f n k Haf H0). 
  - intro. destruct k.
    1: simpl in H; rewrite (countdown_init a f n); omega; apply H. 
    remember (n - a) as m.
    destruct m; [rewrite countdown_init; omega|]. 
    destruct (repeat_contract_strict_threshold a f n Haf); [omega|].
    destruct H0 as [Hx0 [Hxl Hxr]].
    assert (countdown_worker a f n n = S x) as Hx.
    { rewrite (countdown_intermediate a f n n x);
        [|apply Hf | apply Hx0| apply Hxr].
      rewrite countdown_init. omega. apply Hxl.
    }
    rewrite Hx. apply not_le. intro.
    apply (repeat_contract f n (S k) x) in H0.
    omega. apply Hf.
Qed.

(* RECURSION FOR CONTRACTORS THEOREM *)
Theorem countdown_recursion : forall a f n,
    contract_strict_above a f ->
    (n <= a -> countdown_to a f n = 0) /\
    (S a <= n -> countdown_to a f n = S (countdown_to a f (f n))).
Proof.
  intros a f n Hf. split.
  1: intro Han; unfold countdown_to; apply countdown_init; apply Han.
  intro Han.
  assert (countdown_to a f n <= S (countdown_to a f (f n))) as G1.
  { rewrite countdown_repeat by apply Hf.
    rewrite repeat_S_comm.
    rewrite <- countdown_repeat by apply Hf.
    trivial. }
  assert (1 <= countdown_to a f n) as G0.
  { rewrite le_lt_S. rewrite <- not_le.
    rewrite countdown_repeat by apply Hf.
    simpl. omega. }
  assert (countdown_to a f (f n) <= countdown_to a f n - 1).
  { rewrite countdown_repeat by apply Hf.
    rewrite <- repeat_S_comm.
    replace (S (countdown_to a f n - 1)) with (countdown_to a f n) by omega.
    rewrite <- countdown_repeat by apply Hf. trivial. }
  omega.
Qed.

Corollary countdown_antirecursion : forall a f n,
    contract_strict_above a f -> countdown_to a f (f n) = countdown_to a f n - 1.
Proof.
  intros a f n Haf.
  assert (H := Haf).
  destruct (Nat.lt_ge_cases a n) as [Han | Han];
    apply (countdown_recursion a f n) in H.
  1: apply H in Han; omega.
  assert (f n <= a) as Hafn.
  { apply (Nat.le_trans _ n _); [apply Haf | apply Han]. }
    apply (countdown_recursion a f (f n)) in Haf.
    apply Haf in Hafn. apply H in Han. omega.
Qed.


(* STRICT CONTRACTIVENESS PRESERVATION THEOREM *)
Theorem countdown_contract_strict : forall a f t,
    1 <= a -> contract_strict_above a f ->
    contract_strict_above t (countdown_to a f).
Proof.
  intros a f t Ha Haf. split.
  - intro n. rewrite countdown_repeat by apply Haf.
    rewrite not_lt. intro.
    apply repeat_contract_strict in H; [omega | apply Haf..].
  - intros n Hn. destruct n; [omega|].
    rewrite <- le_S_n_m.
    rewrite countdown_repeat by apply Haf.
    destruct n;  trivial.
    remember (repeat f n (S (S n)) - a) as m. destruct m.
    1: apply (Nat.le_trans _ (repeat f n (S (S n))) _); [apply Haf | omega]. 
    assert (S n + repeat f (S n) (S (S n)) <= (S n) + a).
    { apply (Nat.le_trans _ (S (S n)) _);
      [apply (repeat_contract_strict a _ _ _ Haf)|]; omega.
    }
    omega.
Qed.

(* ****** COUNTDOWN - REPEATER - INVERSE PRESERVATION **************** *)

(* This theorem is important. It says that the countdown and repeater will
   preserve the upper inverse relation on their respective results
   This is needed to prove that the tower (n - 2), ceil(n/2), ceil(log_2(n)), ...
   is the upper inverse of the tower (n + 2), 2n, 2^n, ...
   However I haven't cleaned that part in the old code yet *)

(*
Theorem countdown_repeater_upp_inverse : forall a f F,
    expand_strict_from a F -> upp_inv_rel f F ->
    upp_inv_rel (countdown_to a f) (repeater_from a F).
Proof.
  intros a f F Haf HfF n N.
  apply (upp_inv_expand_contract_strict a f F) in Haf.
  2: apply HfF.
  rewrite repeater_from_repeat.
  apply (upp_inv_repeat n _ _) in HfF.
  rewrite <- (HfF a N). apply countdown_repeat. apply Haf.
Qed.
*)

(* TODO: Change it to using expand_strict_from as premise *)
Theorem countdown_repeater_upp_inverse : forall a f F,
    contract_strict_above a f -> upp_inv_rel f F ->
    upp_inv_rel (countdown_to a f) (repeater_from a F).
Proof.
  intros a f F Haf HfF n N.
  rewrite repeater_from_repeat.
  apply (upp_inv_repeat n _ _) in HfF.
  rewrite <- (HfF a N). apply countdown_repeat. apply Haf.
Qed.