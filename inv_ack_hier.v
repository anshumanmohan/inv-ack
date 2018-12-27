Require Import Omega.
Require Import Setoid.

(* ================================================
========= DEFINITIONS ============================ *)


Fixpoint div_worker (b n cd b1 : nat) : nat
:=
match n with
| 0    => 1
| 1    => 1
| S n' => match cd with
          | 0     => S(div_worker b n' b1 b1)
          | S cd' => div_worker b n' cd' b1
          end
end.

Definition div (b n : nat)
:= match (b-1) with | b1 => div_worker b n b1 b1 end.


Fixpoint next_level_worker (f : nat -> nat) (n n1 cd n2 : nat) : nat
:=
match n with
| 0    => 0
| 1    => 0
| S n' => match cd with
          | 0     => S(next_level_worker f n' n2 (n1 - n2 - 1) (f n2))
          | S cd' => next_level_worker f n' n1 cd' n2
          end
end.

Definition next_level f n
:= match (f n) with
   | n1 => match (f n1) with
           | n2 => next_level_worker f n n1 (n - n1 - 1) n2
           end
end.

Fixpoint inv_ack_hier i b n
:= match i with
   | 0 => n
   | 1 => div b n
   | S i' => next_level (inv_ack_hier i' b) n
end.


Definition next_level_fast f n
:= match n with
   | 1 => 0
   | _ => match (f n) with
          | n1 => S(next_level f n1) end
end.

Fixpoint inv_ack_hier_fast i b n
:= match i with
   | 0 => n
   | 1 => div b n
   | S i' => next_level_fast (inv_ack_hier i' b) n
end.


(* ================================================
============= THEOREMS ============================ *)


(* USEFUL LEMMAS ABOUT NAT *)
Lemma le_add_le_sub_r : forall n m p : nat, n + p <= m -> n <= m - p.
apply Nat.le_add_le_sub_r. Qed.

Lemma le_add_le_sub_l : forall n m p : nat, n + p <= m -> p <= m - n.
apply Nat.le_add_le_sub_l. Qed.

Lemma lt_add_lt_sub_r : forall n m p : nat, n + p < m <-> n < m - p.
apply Nat.lt_add_lt_sub_r. Qed.

Lemma lt_add_lt_sub_l : forall n m p : nat, n + p < m <-> p < m - n.
apply Nat.lt_add_lt_sub_l. Qed.

Lemma lt_le_S : forall n m : nat, n < m -> S n <= m.
apply lt_le_S. Qed.

Lemma minus_n_0 : forall n, n - 0 = n.
intros. rewrite minus_n_O. trivial. Qed.

Lemma sub_add_distr: forall n m p : nat, n - (m + p) = n - m - p.
intros. apply Nat.sub_add_distr. Qed.

Lemma sub_sub_comm: forall n m p: nat, n - m - p = n - p - m.
intros. rewrite <- sub_add_distr. rewrite <- sub_add_distr.
rewrite plus_comm. trivial. Qed.

Lemma add_sub_eq_l: forall n m p : nat, m + p = n -> n - m = p.
apply Nat.add_sub_eq_l. Qed.

Lemma add_sub_eq_r: forall n m p : nat, m + p = n -> n - p = m.
apply Nat.add_sub_eq_r. Qed.

Lemma le_plus_minus: forall n m : nat, n <= m -> m = n + (m - n).
apply le_plus_minus. Qed.

Lemma sub_compl: forall n m : nat, m <= n -> n - (n - m) = m.
intros. apply add_sub_eq_r. symmetry. apply le_plus_minus. trivial. Qed.

Lemma sub_lt: forall n m : nat, m <= n -> 0 < m -> n - m < n.
apply Nat.sub_lt. Qed.

Lemma le_sub_l: forall n m : nat, n - m <= n.
apply Nat.le_sub_l. Qed.

Lemma le_succ_l: forall n m : nat, S n <= m <-> n < m.
apply Nat.le_succ_l. Qed.

Lemma lt_succ_r: forall n m : nat, n < S m <-> n <= m.
apply Nat.lt_succ_r. Qed.

Lemma lt_lt_0: forall n m : nat, n < m -> 0 < m.
apply Nat.lt_lt_0. Qed.

Lemma le_cases: forall n m : nat, n <= m -> (n <= m-1 \/ (n = m /\ m <> 0)).
intros. destruct H.
- destruct n. simpl. left. omega. right. omega.
- simpl. rewrite minus_n_0. left. trivial.
Qed.

Lemma nat_compare: forall n m : nat, S n <= m \/ n = m \/ S m <= n.
intros. assert (H := le_lt_dec m n). destruct H as [H1 | H2].
- right. inversion H1. omega. right. omega.
- left. omega.
Qed.

Lemma le_antisymm: forall n m : nat, n <= m -> m <= n -> n = m.
apply le_antisym. Qed.

(* LEMMAS ABOUT DECREASING FUNCTIONS *)

Fixpoint repeat (f: nat -> nat) (rep n : nat) : nat
:= match rep with
   | 0      => n
   | S rep' => f (repeat f rep' n)
end.

Definition decreasing (f : nat -> nat) := forall m, f m <= m - 1.

Theorem repeat_decreasing : forall f k l n,
(decreasing f) -> (k < l) -> (repeat f l n <= repeat f k n - 1).
Proof.
intros f k l n Hf. unfold decreasing in Hf.
generalize dependent l. induction k.
- simpl. intros. destruct l. inversion H. clear H. induction l. simpl. apply Hf.
  apply (Nat.le_trans _ (repeat f (S l) n) _). simpl.
  apply (Nat.le_trans _ (f(repeat f l n) - 1) _). apply Hf. apply Nat.le_sub_l.
  apply IHl.
- induction l. intro. inversion H.
  intro. inversion H. rewrite H1. simpl. apply Hf.
  apply (Nat.le_trans _ (repeat f l n) _).
  + simpl. apply (Nat.le_trans _ (repeat f l n - 1) _). apply Hf. apply Nat.le_sub_l.
  + apply IHl. apply H1.
Qed.

Theorem dec_threshold : forall f n t,
(decreasing f) ->
(n > t) ->
(exists k, (repeat f (S k) n <= t) /\ (t < repeat f k n)).
Proof.
intros f n t Hf Hn.
assert (n = (n-t) + t).
{ rewrite plus_comm. apply (le_plus_minus t _).
  unfold gt in Hn. apply Nat.lt_le_incl. trivial. }
remember (n-t) as l.
assert (t = n - l).
{ rewrite Heql. rewrite sub_compl. trivial. apply Nat.lt_le_incl. trivial. }
rewrite H0.
clear Heql. clear H.
assert (l <> 0).
{ intro. rewrite H in H0. rewrite minus_n_0 in H0. rewrite H0 in Hn.
  apply Nat.lt_irrefl in Hn. trivial. }
clear H0.
destruct l. exfalso. apply H. trivial. clear H.
induction l.
- exists 0. split.
  replace (n - 1) with (repeat f 0 n - 1). apply Hf. trivial.
  simpl. apply sub_lt. rewrite le_succ_l. apply (lt_lt_0 t n). trivial. omega.
- assert (n - S(S l) = n - S l - 1).
  { rewrite <- sub_add_distr. rewrite plus_comm. trivial. }
  rewrite H. remember (n - S l) as s.
  destruct IHl as [h Hs]. destruct Hs as [Hs1 Hs2].
  apply le_cases in Hs1. destruct Hs1 as [Hs1 | Hs1].
  + exists h. split. trivial. rewrite <- le_succ_l in Hs2. rewrite <- le_succ_l.
    apply (Nat.le_trans _ (S s) _). apply Peano.le_n_S. apply le_sub_l. trivial.
  + destruct Hs1 as [Hs0 Hs1]. exists (S h). simpl. split.
    * rewrite <- Hs0. apply Hf.
    * simpl in Hs0. rewrite Hs0. destruct s.
      exfalso. apply Hs1. trivial.
      simpl. rewrite minus_n_0. apply Nat.lt_succ_diag_r.
Qed.


Lemma dec_f_0 : forall f, (decreasing f) -> (forall k, repeat f k 0 = 0).
Proof.
induction k. trivial.
simpl. rewrite IHk.
assert (f 0 <= 0). { apply H. } inversion H0. rewrite H2. rewrite H2. trivial.
Qed.


Lemma dec_f_1 : forall f, (decreasing f) -> (forall k, repeat f (S k) 1 = 0).
Proof.
induction k. simpl.
specialize (H 1). inversion H. rewrite H1. trivial.
replace (repeat f (S (S k)) 1) with (f (repeat f (S k) 1)).
rewrite IHk.
specialize (H 0). inversion H. rewrite H1. trivial.
trivial.
Qed.


(* LEMMAS ABOUT PROPER DECREASING FUNCTIONS *)

Definition proper (f: nat -> nat) := forall m, (m > 1) -> (f m > 0).

Definition proper_dec f := proper f /\ decreasing f.


(* LEMMAS ABOUT NEXT_LEVEL_WORKER *)

Lemma next_level_interstate_1 : forall f n n1 cd n2,
next_level_worker f n n1 cd n2 = next_level_worker f (n - cd) n1 0 n2.
Proof.
intros f n n1 cd n2.
destruct n.
simpl. trivial.
generalize dependent n. induction cd.
- simpl. trivial.
- intro.
  replace (next_level_worker f (S n) n1 (S cd) n2) with (next_level_worker f n n1 cd n2).
  replace (S n - S cd) with (n - cd).
  destruct n.
  + simpl. trivial.
  + rewrite IHcd. trivial.
  + trivial.
  + symmetry. simpl. destruct n. trivial. trivial.
Qed.


Lemma next_level_interstate_2 : forall f n n1 cd n2, (1 + cd < n) ->
next_level_worker f n n1 cd n2
= 1 + next_level_worker f (n - cd - 1) n2 (n1 - n2 - 1) (f n2).
Proof.
intros. apply lt_add_lt_sub_r in H. apply lt_le_S in H.
rewrite next_level_interstate_1.
remember (n - cd) as m.
destruct m. inversion H.
simpl. rewrite minus_n_0.
destruct m. inversion H. inversion H1. trivial.
Qed.


Lemma next_level_interstate_3 : forall f n k,
proper_dec f
-> 1 < (repeat f k n)
-> next_level f (repeat f k n) = 1 + next_level f (repeat f (S k) n).
Proof.
intros. destruct H as [H1 H2].
unfold proper in H1. unfold decreasing in H2.
unfold next_level.
rewrite next_level_interstate_2.
simpl.
assert (repeat f k n - (repeat f k n - f (repeat f k n) - 1) - 1 = f (repeat f k n)) as H3.
{
rewrite sub_sub_comm.
rewrite (sub_sub_comm _ (f (repeat f k n)) _).
apply sub_compl. apply H2.
}
rewrite H3. trivial.
replace (repeat f (S k) n) with (f (repeat f k n)).
remember (repeat f k n) as a. rewrite <- le_plus_minus.
- apply sub_lt. apply (Nat.le_trans _ (a - 1) _). apply H2. apply le_sub_l.
  apply H1. apply H0.
- specialize (H2 a). apply lt_le_S. apply lt_add_lt_sub_r. simpl.
  unfold lt. apply le_n_S in H2. apply (Nat.le_trans _ (S(a-1)) _). apply H2.
  replace (S(a-1)) with (1 + (a-1)). rewrite <- (le_plus_minus 1 a).
  apply Nat.le_refl. apply Nat.lt_le_incl. apply H0. omega.
- trivial.
Qed.


Lemma next_level_final_state : forall f n k,
(repeat f k n) <= 1 -> next_level f (repeat f k n) = 0.
Proof.
intros. unfold next_level.
destruct (repeat f k n). trivial.
destruct n0. trivial.
inversion H. inversion H1.
Qed.


Lemma next_level_interstate_ult : forall f n k,
proper_dec f
-> 1 < (repeat f k n)
-> next_level f n = (S k) + next_level f (repeat f (S k) n).
Proof.
intros f n k Hf Hk.
replace (next_level f n) with (next_level f (repeat f 0 n)).
induction k. apply next_level_interstate_3. trivial. trivial.
rewrite IHk. apply next_level_interstate_3 in Hk.
rewrite Hk. omega. trivial.
destruct Hf as [Hf1 Hf2]. unfold decreasing in Hf2. simpl in Hk.
apply lt_le_S in Hk. specialize (Hf2 (repeat f k n)).
unfold lt.
{ apply (Nat.le_trans _ (repeat f k n - 1) _ ).
  apply (Nat.le_trans _ (f (repeat f k n)) _ ). trivial. trivial.
  apply le_sub_l. }
trivial.
Qed.


(* MAIN THEOREMS *)


Theorem next_level_repeat_1 : forall f n k,
(proper_dec f) -> ((repeat f k n <= 1) <-> (next_level f n <= k)).
Proof.
intros. assert (Hf := H). destruct H as [Hf1 Hf2]. destruct n as [| n1].
unfold next_level. rewrite dec_f_0. simpl. omega. trivial.
destruct n1 as [| n2].
- unfold next_level. destruct k.
  simpl. omega.
  rewrite dec_f_1. simpl. omega. trivial.

- assert (1 < S (S n2)) as Hn. { omega. } remember (S (S n2)) as n.
  split.
  + intro Hk. destruct (dec_threshold f n 1) as [l Hl]. trivial. trivial.
    destruct Hl as [HSl Hl].
    apply (next_level_interstate_ult f n l) in Hf.
    apply (next_level_final_state f n (S l)) in HSl.
    rewrite HSl in Hf. rewrite <- plus_n_O in Hf. rewrite Hf.
    assert (Hkl := nat_compare l k). unfold lt in Hl.
    destruct Hkl as [l_lt_k | k_le_l].
    * trivial.
    * exfalso. destruct k_le_l as [k_eq_l | k_lt_l].
      rewrite k_eq_l in Hl. assert (2 <= 1).
      { apply (Nat.le_trans _ (repeat f k n) _). trivial. trivial. }
      omega.
      
      rewrite le_succ_l in k_lt_l. apply (repeat_decreasing f k l n) in k_lt_l.
      apply (Nat.le_trans 2 (repeat f l n) _) in k_lt_l.
      rewrite le_succ_l in k_lt_l. rewrite <- lt_add_lt_sub_r in k_lt_l.
      simpl in k_lt_l. rewrite <- le_succ_l in k_lt_l. assert (3 <= 1).
      { apply (Nat.le_trans _ (repeat f k n) _). trivial. trivial. }
      omega. trivial. trivial.
    * trivial.
  
  + intro Hnk. apply not_lt. intro Hk.
    apply (next_level_interstate_ult f n k) in Hk.
    assert (S k <= k).
    { apply (Nat.le_trans _ (next_level f n) _).
      rewrite Hk. apply Nat.le_add_r. trivial. }
    omega. trivial.
Qed.


Theorem next_level_repeat_2 : forall (f : nat -> nat) (n k : nat),
        (proper_dec f)
        -> ((next_level f n = k)
        <-> (repeat f k n <= 1 /\ (forall p, repeat f p n <= 1 -> k <= p))). 
Proof.
intros f n k Hf. split.
- intro Hk. split.
  + rewrite next_level_repeat_1. omega. trivial.
  + intros p Hp. rewrite <- Hk. rewrite <- next_level_repeat_1. trivial. trivial.
- intro Hk. destruct Hk as [Hk1 Hk2].
  apply le_antisym. rewrite <- next_level_repeat_1. trivial. trivial.
  apply (Hk2 (next_level f n)). rewrite next_level_repeat_1. trivial. trivial.
Qed.