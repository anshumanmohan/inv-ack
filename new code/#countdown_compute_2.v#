Require Import Omega.
Require Import prelims.
Require Import countdown_repeater.


(*
=============================================================================
**************** SECTION 4: COUNTDOWN COMPUTATIONS **************************
=============================================================================
*)

(* This contains the original approach to countdown, which is still under
   cleaning. *)

(* ****** 1.1. DEFINITION *************************************)


Fixpoint countdown_to_worker (a : nat) (f : nat -> nat) (n cd : nat)
: nat :=
match n with
| 0    => 0
| S n' => match cd with
          | 0     => S (countdown_to_worker a f n' (n' - f (a + n') - 1))
          | S cd' => countdown_to_worker a f n' cd'
          end
end.

Definition countdown_to a f n := countdown_to_worker a f (n - a) (n - f n - 1).


(* ****** 1.2. THEOREMS ************************************* *)

(*
(* INITIAL VALUE THEOREM *)
Theorem countdown_to_init : forall a f n k,
(n <= a) -> (countdown_to_worker a f n k = 0).
Proof.
intros a f n k Hna.
unfold countdown_to_worker.
destruct k. { trivial. }
replace (n - a) with 0 by omega.
trivial.
Qed.
*)

(* INTERMEDIATE STATE LEMMA*)
Theorem countdown_to_intermediate : forall a f n cd i,
(i <= cd) -> countdown_to_worker a f n cd = countdown_to_worker a f (n - i) (cd - i).
Proof.
intros a f n cd i Hicd.
induction i.
{ replace (n - 0) with n by omega.
  replace (cd - 0) with cd by omega.
  trivial. }
rewrite IHi.
- remember (n - i) as n1.
  destruct n1. { replace (n - S i) with 0 by omega. trivial. }
  replace (n - S i) with n1 by omega.
  replace (cd - i) with (S (cd - S i)) by omega.
  trivial.
- omega.
Qed.

(* RECURSION LEMMA *)
Theorem countdown_to_recursion : forall a f n,
(S a <= n) -> countdown_to a f n = S (countdown_to a f (f n)).
Proof.
intros a f n Han.
unfold countdown_to.
rewrite (countdown_to_intermediate a f (n - a) (n - f n - 1) (n - f n - 1)).
rewrite Nat.sub_diag.
remember (f n + 1 - a) as m.
destruct m.
{ replace (n - a - (n - f n - 1)) with 0 by omega.
  replace (f n - a) with 0 by omega.
  simpl.
replace (n - a) with (S (n - S a)) by omega.



(* COUNTDOWN VS REPEAT LEMMA *)
Theorem countdown_to_repeat : forall a f,
contracting f
-> contract_strict_from (S a) f
-> countdown_to_repeat_rel a f (countdown_to a f).
Proof.
intros a f Hf Haf n k.
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
Theorem countdown_to_contractor : forall a f n,
contracting f
-> contract_strict_from (S a) f
-> S a <= n
-> countdown_to a f n = S(countdown_to a f (f n)).
Proof.
intros a f n Hf Haf Han.
assert (H0 := Hf).
apply (countdown_to_repeat a f) in H0.
- rewrite countdown_to_rel_recursion in H0.
  destruct (H0 n) as [Hfn0 Hfn1].
  tauto. apply Hf. apply Haf.
- apply Haf.
Qed.