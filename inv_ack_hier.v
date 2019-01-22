Require Import Omega.
Require Import Setoid.


(* USEFUL LEMMAS ABOUT NAT *)
Lemma le_add_le_sub_r : forall n m p : nat, n + p <= m -> n <= m - p.
apply Nat.le_add_le_sub_r. Qed.

Lemma le_add_le_sub_l : forall n m p : nat, n + p <= m -> p <= m - n.
apply Nat.le_add_le_sub_l. Qed.

Lemma lt_add_lt_sub_r : forall n m p : nat, n + p < m <-> n < m - p.
apply Nat.lt_add_lt_sub_r. Qed.

Lemma lt_add_lt_sub_l : forall n m p : nat, n + p < m <-> p < m - n.
apply Nat.lt_add_lt_sub_l. Qed.

Lemma lt_le_S : forall n m : nat, n < m <-> S n <= m.
intros. omega. Qed.

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

Lemma minus_S : forall n m : nat, n - m = S n - S m.
intros. omega. Qed.

Lemma le_S_n_m : forall n m : nat, n <= m <-> S n <= S m.
split. apply Peano.le_n_S. apply Peano.le_S_n. Qed.

Lemma lt_S_n_m : forall n m : nat, n < m <-> S n < S m.
intros. omega. Qed.

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

Lemma not_lt: forall n m : nat, n <= m <-> ~ m < n.
split. omega. omega. Qed.

Lemma not_le: forall n m : nat, ~ n <= m <-> m < n.
split. omega. omega. Qed.

Lemma le_antisymm: forall n m : nat, n <= m -> m <= n -> n = m.
apply le_antisym. Qed.



(* LEMMAS ABOUT DECREASING FUNCTIONS *)

Fixpoint repeat (f: nat -> nat) (rep n : nat) : nat
:= match rep with
   | 0      => n
   | S rep' => f (repeat f rep' n)
end.

Theorem repeat_S_comm : forall f k n, repeat f (S k) n = repeat f k (f n).
Proof.
induction k. { trivial. }
intro. simpl. simpl in IHk. rewrite IHk. trivial.
Qed.

Definition shrinking (f : nat -> nat) := forall m, f m <= m - 1.

Theorem repeat_shrinking : forall f k l n,
(shrinking f) -> (k < l) -> (repeat f l n <= repeat f k n - 1).
Proof.
intros f k l n Hf. unfold shrinking in Hf.
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

Theorem shrink_threshold : forall f n t,
(shrinking f) ->
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


Lemma repeat_shrink : forall f, shrinking f -> (forall n k, repeat f k n <= n - k).
Proof.
intros f Hf n. induction k.
- simpl. omega.
- simpl. apply (Nat.le_trans _ (repeat f k n - 1) _). apply Hf. omega.
Qed.


Lemma shrink_f_0 : forall f, (shrinking f) -> (forall k, repeat f k 0 = 0).
Proof.
induction k. trivial.
simpl. rewrite IHk.
assert (f 0 <= 0). { apply H. } inversion H0. rewrite H2. rewrite H2. trivial.
Qed.


Lemma shrink_f_1 : forall f, (shrinking f) -> (forall k, repeat f (S k) 1 = 0).
Proof.
induction k. simpl.
specialize (H 1). inversion H. rewrite H1. trivial.
replace (repeat f (S (S k)) 1) with (f (repeat f (S k) 1)).
rewrite IHk.
specialize (H 0). inversion H. rewrite H1. trivial.
trivial.
Qed.


(* ================================================
========= DEFINITIONS ============================ *)

Fixpoint next_level_worker (f : nat -> nat) (n n1 cd : nat) : nat
:=
match n with
| 0 => 0
| 1 => 0
| S n' => match n1 with
          | 0 => 1
          | 1 => 1
          | _ =>
          match cd with
          | 0 => match (f n1) with | n2 => S(next_level_worker f n' n2 (n1 - n2 - 1)) end
          | S cd' => next_level_worker f n' n1 cd'
          end
          end
end.

Definition next_level f n
:= match (f n) with | n1 => next_level_worker f n n1 (n - n1 - 1)
end.

Definition next_level_fast f n
:= match n with
   | 0 => 0
   | 1 => 0
   | _ => match (f n) with
          | n1 => S(next_level f n1) end
end.

Definition sub2 (n : nat) : nat := n - 2.

Compute sub2 2.
Compute sub2 1.
Compute sub2 3.

Compute next_level sub2 2.
Compute next_level sub2 3.
Compute next_level sub2 4.

(* ================================================
============= THEOREMS ============================ *)


(* LEMMAS ABOUT NEXT_LEVEL_WORKER *)

Lemma next_level_interstate_1 : forall f n n1 cd k,
(2 <= n1) -> (k <= cd) -> (k <= n)
-> next_level_worker f n n1 cd = next_level_worker f (n - k) n1 (cd - k).
Proof.
intros f n n1 cd k Hn1. generalize dependent cd.
generalize dependent k. induction n. { trivial. }
intros k cd Hk Hkn1. destruct k. { repeat rewrite minus_n_0. trivial. }
destruct cd. { inversion Hk. }
apply le_S_n_m in Hk. repeat rewrite Nat.sub_succ. rewrite <- le_S_n_m in Hkn1.
rewrite <- IHn.
- destruct n. trivial.
  destruct n1. inversion Hn1. destruct n1. inversion Hn1. inversion H0.
  trivial.
- trivial.
- trivial.
Qed.


Lemma next_level_interstate_2 : forall f n,
shrinking f -> 2 <= n -> next_level f n = 1 + next_level f (f n).
Proof.
intros. unfold next_level. destruct n. inversion H0.
destruct n. inversion H0. inversion H2.
remember (f (S (S n))) as n1.
destruct n1. { trivial. } destruct n1. { trivial. }
remember (S (S n) - S (S n1) - 1) as cd.
rewrite (next_level_interstate_1 _ _ _ _ cd). rewrite Nat.sub_diag.
assert (S(S n) - cd = (S (S (S n1)))).
{ rewrite Heqcd. rewrite <- sub_add_distr. rewrite plus_comm. rewrite sub_compl.
  trivial. rewrite <- le_S_n_m. rewrite Heqn1. apply H. }
rewrite H1. trivial. omega. trivial. omega.
Qed.


(* MAIN THEOREMS *)


Theorem next_level_repeat_1 : forall f n k,
shrinking f -> (repeat f k n <= 1 <-> next_level f n <= k).
Proof.
intros. generalize dependent n. induction k.
{ intro n. simpl. destruct n. { unfold next_level. simpl. omega. }
  destruct n. { unfold next_level. simpl. omega. }
  rewrite next_level_interstate_2. omega. trivial. omega. }
intro n.
destruct n. { unfold next_level. rewrite shrink_f_0. simpl. omega. trivial. }
destruct n. { unfold next_level. rewrite shrink_f_1. simpl. omega. trivial. }
rewrite repeat_S_comm. rewrite next_level_interstate_2. rewrite <- le_S_n_m.
apply IHk. trivial. omega.
Qed.


Theorem next_level_repeat_2 : forall (f : nat -> nat) (n k : nat),
        shrinking f
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


(* PROPER SHRINKING PRESERVE THEOREM *)

Theorem next_level_shrink : forall f,
shrinking f -> shrinking (next_level f).
Proof.
intros f Hf. unfold shrinking.
intros. rewrite <- next_level_repeat_1.
assert (forall n k, repeat f k n <= n - k).
{ apply repeat_shrink. trivial. }
specialize (H m (m - 1)). omega. trivial.
Qed.


(* INCREASING FUNCTIONS *)

Definition increasing (f : nat -> nat) : Prop := forall n m, n <= m -> f n <= f m.

Definition increasing_strict (f : nat -> nat) : Prop := forall n m, n < m -> f n < f m.


Lemma incr_S : forall f, increasing f <-> (forall n, f n <= f (S n)).
Proof.
intro. split. { intros. apply H. omega. }
{ unfold increasing. intros. generalize dependent n. induction m.
- intros. inversion H0. omega.
- intros. inversion H0. omega. apply IHm in H2. apply (Nat.le_trans _ (f m) _).
  trivial. apply H. }
Qed.


Lemma incr_strict_S : forall f, increasing_strict f <-> (forall n, f n < f (S n)).
Proof.
intro. split. { intros. apply H. omega. }
{ unfold increasing_strict. intros. generalize dependent n. induction m.
- intros. inversion H0.
- intros. inversion H0. apply H. apply IHm in H2. apply (Nat.lt_trans _ (f m) _).
  trivial. apply H. }
Qed.


Lemma repeat_incr : forall f, increasing f -> (forall k, increasing (repeat f k)).
Proof.
intro f. unfold increasing. intro Hf.
induction k. simpl. intros. trivial.
intros. simpl. apply Hf. apply IHk. trivial.
Qed.


Theorem next_level_incr : forall f,
shrinking f -> increasing f -> increasing (next_level f).
Proof.
intros f Hf0 Hf1 n m Hnm. apply next_level_repeat_1. trivial.
assert (increasing (repeat f (next_level f m))).
{ apply repeat_incr. trivial. }
specialize (H n m). apply H in Hnm.
apply (Nat.le_trans _ (repeat f (next_level f m) m) _).
trivial. apply next_level_repeat_1. trivial. trivial.
Qed.


(* THE ACKERMANN HIERARCHY *)

Definition can_inv_rel (f F : nat -> nat) : Prop
:= forall n N, f N <= n <-> N <= F n.

Fixpoint next_can_level F n : nat :=
match n with
| 0 => 1
| S n' => F (next_can_level F n')
end.


Definition growing (F : nat -> nat) : Prop := forall n, S n <= F n.


Lemma can_inv_growing : forall f F, shrinking f -> can_inv_rel f F -> growing F.
Proof.
intros f F Hf HfF n. rewrite <- (HfF n _).
apply (Nat.le_trans _ (S n - 1) _). apply Hf. omega.
Qed.


Lemma can_inv_positive : forall f F,
shrinking f -> can_inv_rel f F -> (forall n, 0 < F n).
Proof.
intros f F Hf HfF n. apply (Nat.le_trans _ (S n) _). omega.
generalize dependent n. apply (can_inv_growing f F). trivial. trivial.
Qed.


Lemma can_inv_increasing : forall f F,
shrinking f -> increasing f -> can_inv_rel f F -> increasing F.
Proof.
intros f F Hf_sh Hf_in HfF. rewrite incr_S. intro.
rewrite <- (HfF (S n) _). apply (Nat.le_trans _ n _).
rewrite (HfF n _). trivial. omega.
Qed.


Theorem inv_next_level_can : forall f F,
shrinking f -> increasing f -> can_inv_rel f F
-> can_inv_rel (next_level f) (next_can_level F).
Proof.
intros f F Hf1 Hf2 HfF. unfold can_inv_rel.
induction n.
{ simpl. intro. rewrite <- next_level_repeat_1. simpl. omega. trivial. }
intro. simpl.
destruct N. { unfold next_level. simpl. omega. }
destruct N.
{ unfold next_level. simpl. split.
  - intro. apply (can_inv_positive f F). trivial. trivial.
  - intro. omega. }
rewrite next_level_interstate_2. rewrite <- le_S_n_m.
rewrite (IHn (f (S (S N)))). apply HfF. trivial. omega.
Qed.


(* PACKING EVERYTHING *)

Definition inv_ack_like_rel f F : Prop :=
(shrinking f) /\ (increasing f)
/\ (can_inv_rel f F) /\ (growing F) /\ (increasing F).


Theorem next_level_inv_ack_like : forall f F,
inv_ack_like_rel f F -> inv_ack_like_rel (next_level f) (next_can_level F).
Proof.
intros. destruct H. destruct H0. destruct H1. destruct H2.
assert (shrinking (next_level f)). { apply next_level_shrink. trivial. }
assert (can_inv_rel (next_level f) (next_can_level F)).
{ apply inv_next_level_can; trivial. }
split. { trivial. }
split. { apply next_level_incr; trivial. }
split. { apply inv_next_level_can; trivial. }
split. { apply (can_inv_growing (next_level f) _); trivial. }
apply (can_inv_increasing (next_level f) _); trivial. apply next_level_incr; trivial.
Qed.


(* INVERSE ACKERMANN HIERARCHY *)

(* ZEROTH LEVEL : MINUS *)
Definition minus_b b n := n - b.

Definition minus_2 n := match n with | 0 => 0 | 1 => 0 | S(S n') => n' end.

Lemma minus_2_correct: forall n, minus_2 n = n - 2.
Proof.
unfold minus_2. destruct n. trivial. destruct n. trivial. omega.
Qed.

Theorem minus_2_shrink: shrinking minus_2.
Proof.
intro. rewrite minus_2_correct. omega.
Qed.


(* HIGHER LEVELS *)

Fixpoint inv_ack_hier i n
:= match i with
   | 0 => minus_2 n
   | S i' => next_level (inv_ack_hier i') n
end.

Fixpoint ack_hier i n
:= match i with
   | 0 => S(S n)
   | S i' => next_can_level (ack_hier i') n
end.

Fixpoint inv_ack_hier_fast i n
:= match i with
   | 0 => minus_2 n
   | S i' => next_level_fast (inv_ack_hier i') n
end.


Theorem inv_hier_ack_hier :
forall i, inv_ack_like_rel (inv_ack_hier i) (ack_hier i).
Proof.
induction i.
- simpl. unfold inv_ack_like_rel. unfold minus_b. split.
  { unfold shrinking. intro. apply minus_2_shrink. } split.
  { unfold increasing. intros. repeat rewrite minus_2_correct. omega. } split.
  { unfold can_inv_rel. intros. rewrite minus_2_correct. omega.  } split.
  { unfold growing. intros. replace (S n) with (1 + n). omega. trivial. }
  { unfold increasing. intros. omega. }
- apply next_level_inv_ack_like. trivial.
Qed.


Corollary inv_ack_hier_each_incr : forall i, increasing (inv_ack_hier i).
intro. assert (H := (inv_hier_ack_hier i)). unfold inv_ack_like_rel in H.
destruct H as [_ H]. destruct H as [H _]. trivial. Qed.


Corollary inv_ack_hier_each_shrink : forall i, shrinking (inv_ack_hier i).
intro. assert (H := (inv_hier_ack_hier i)). unfold inv_ack_like_rel in H.
destruct H as [H _]. trivial. Qed.


Corollary inv_ack_hier_shrink : forall i n,
(3 <= n) -> (inv_ack_hier (S i) n) <= inv_ack_hier i n.
Proof.
intros. assert (Hi := (inv_ack_hier_each_shrink i)). simpl.
rewrite <- next_level_repeat_1. remember (inv_ack_hier i n) as m.
destruct m.
- simpl. destruct i. { simpl in Heqm. rewrite minus_2_correct in Heqm. omega. }
  symmetry in Heqm. simpl in Heqm. rewrite next_level_repeat_2 in Heqm.
  destruct Heqm as [Heqm _]. simpl in Heqm. trivial. apply inv_ack_hier_each_shrink.
- rewrite repeat_S_comm. apply (Nat.le_trans _ (inv_ack_hier i n - m) _).
  apply repeat_shrink. trivial. omega.
- trivial.
Qed.


Corollary inv_ack_hier_shrink_gen : forall i j n,
(3 <= n) -> (i <= j) -> (inv_ack_hier j n) <= inv_ack_hier i n.
Proof.
intros i j n Hn Hij. generalize dependent i.
induction j. { intros. inversion Hij. trivial. }
intros. inversion Hij.
{ trivial. }
apply (Nat.le_trans _ (inv_ack_hier j n) _).
{ apply inv_ack_hier_shrink. trivial. }
apply IHj. trivial.
Qed.


(* RELATION TO ACKERMANN FUNCTION *)


Fixpoint next_ack_level f n : nat :=
match n with
| 0 => f 1
| S n' => f (next_ack_level f n')
end.


Fixpoint Ack m n : nat :=
match m with
| 0 => S n
| S m' => next_ack_level (Ack m') n
end.


Lemma Ack_1 : forall n, Ack 1 n = n + 2.
Proof.
induction n. trivial. unfold Ack. simpl. unfold Ack in IHn. rewrite IHn. trivial.
Qed.


Lemma ack_hier_1 : forall m, ack_hier m 1 = 3.
Proof.
induction m. trivial. trivial. Qed.


Theorem ack_hier_Ack : forall m n, ack_hier m (n + 2) = Ack (m + 1) n + 2.
Proof.
induction m.
{ intro. rewrite Ack_1. simpl. omega. }
induction n.
{ simpl. rewrite <- (IHm 1). rewrite ack_hier_1. trivial. }
simpl. simpl in IHn. rewrite IHn. rewrite IHm. trivial.
Qed.


Theorem inv_ack_Ack : forall n x y,
n <= Ack (S x) y <-> inv_ack_hier x (n + 2) <= y + 2.
Proof.
intros. assert (inv_ack_like_rel (inv_ack_hier x) (ack_hier x)).
{ apply inv_hier_ack_hier. }
destruct H as [_ H]. destruct H as [_ H]. destruct H as [H _].
rewrite (H (y+2) (n+2)). rewrite ack_hier_Ack.
replace (x+1) with (S x). omega. omega.
Qed.


(* INVERSE ACKERMANN DEFINITION *)

Definition inv_ack_rel n a := forall x, n <= Ack x x <-> a <= x.


(* Find minimum u such that inv_ack_hier u n <= u + 3 *)
Fixpoint inv_ack_worker n f cd1 cd0 :=
match cd0 with
| 0 => 0
| 1 => 1
| S cd0' => match cd1 with
            | 0 => match (next_level f) with
                   | f' => S (inv_ack_worker n f' (n - f' n - 1) cd0') end
            | S cd1' => inv_ack_worker (n - 1) f cd1' cd0' end
end.

Definition inv_ack_helper i n :=
match (inv_ack_hier i), (inv_ack_hier (S i)) with
       | f0, f1 => inv_ack_worker (f0 n) f1 (f0 n - f1 n) (f0 n - (i + 3))
end.

Definition inv_ack n :=
match n with
| 0 => 0
| 1 => 0
| _ => inv_ack_worker (S(S n)) minus_2 2 n
end.


Theorem inv_ack_interstate_1 : forall n f cd1 cd0 k, (k <= cd1) -> (k < cd0)
-> inv_ack_worker n f cd1 cd0 = inv_ack_worker (n - k) f (cd1 - k) (cd0 - k).
Proof.
intros n f cd1 cd0 k. generalize dependent cd0.
generalize dependent cd1. generalize dependent n.
induction k. { intros. repeat rewrite minus_n_0. trivial. }
intros n cd1 cd0 HSk1 HSk0.
destruct cd0. { omega. } destruct cd0. { omega. }
destruct cd1. { omega. }
rewrite <- le_S_n_m in HSk1. rewrite <- lt_S_n_m in HSk0.
apply (IHk (n - 1) cd1 (S cd0)) in HSk1.
repeat rewrite <- minus_S. rewrite <- sub_add_distr in HSk1.
unfold plus in HSk1. rewrite <- HSk1. trivial. trivial.
Qed.


Theorem inv_ack_interstate_2 : forall n f cd1 cd0,
(1 <= cd0) -> inv_ack_worker n f cd1 cd0
= S (inv_ack_worker (n - cd1) (next_level f)
     ((n - cd1) - (next_level f (n - cd1)) - 1) (cd0 - cd1 - 1)).
Proof.
intros n f cd1 cd0 H. remember (cd0 - cd1) as m.
destruct m.
{ rewrite (inv_ack_interstate_1 _ _ _ _ (cd0 - 1)). simpl.
  rewrite sub_compl. trivial. trivial. omega. omega. }
rewrite (inv_ack_interstate_1 _ _ _ _ cd1).
rewrite Nat.sub_diag.
destruct m. { simpl. rewrite <- Heqm. trivial. }
rewrite <- Heqm. rewrite <- minus_S. rewrite minus_n_0. trivial.
trivial. omega.
Qed.


Theorem inv_ack_interstate_3 : forall i n, 
(i + 4 <= inv_ack_hier i n) -> inv_ack_helper i n = 1 + inv_ack_helper (S i) n.
Proof.
intros i n Hin.
unfold inv_ack_helper. remember (inv_ack_hier i) as f0.
remember (inv_ack_hier (S i)) as f1. remember (inv_ack_hier (S(S i))) as f2.
assert (4 <= n) as Hn.
{ assert (H := (inv_ack_hier_each_shrink i n)). rewrite <- Heqf0 in H. omega. }
assert (f1 n <= f0 n).
{ rewrite Heqf1. rewrite Heqf0. apply inv_ack_hier_shrink. omega. }
rewrite inv_ack_interstate_2. simpl.
replace (f0 n - (f0 n - f1 n)) with (f1 n).
assert (f2 = next_level f1) as Hf12. { rewrite Heqf1. rewrite Heqf2. trivial. }
rewrite <- Hf12.
rewrite <- sub_add_distr. replace (f2 (f1 n) + 1) with (f2 n).
replace (f0 n - (i + 3) - (f0 n - f1 n) - 1) with (f1 n - S (i + 3)).
- trivial.
- rewrite <- sub_sub_comm. rewrite <- (sub_add_distr _ (i + 3) _).
  rewrite (plus_comm 1 _). rewrite <- sub_sub_comm. omega.
- rewrite Hf12. rewrite plus_comm.
  rewrite next_level_interstate_2. trivial.
  rewrite Heqf1. apply inv_ack_hier_each_shrink. omega.
- omega.
- omega.
Qed.


Theorem inv_ack_interstate_4 : forall n,
(2 <= n) -> inv_ack n = 1 + inv_ack_helper 0 (S(S n)).
Proof.
intro. unfold inv_ack_helper. simpl.
destruct n. { omega. } destruct n. { omega. }
assert (S(S(S(S n))) - 2 = S(S n)). { omega. }
intro. clear H0. unfold inv_ack. rewrite inv_ack_interstate_2.
rewrite H. rewrite <- sub_add_distr. rewrite <- sub_add_distr.
rewrite plus_comm. rewrite <- minus_2_correct in H.
rewrite <- H. rewrite <- (next_level_interstate_2 minus_2 _). trivial.
apply minus_2_shrink. omega. omega.
Qed.


Theorem inv_ack_helper_thm : forall i k n, (3 <= n) ->
(i + k + 4 <= inv_ack_hier (i + k) n) <-> (S i <= inv_ack_helper k n).
Proof.
intros i k n Hn. generalize dependent k.

assert (forall k, k + 4 <= inv_ack_hier k n <-> 1 <= inv_ack_helper k n) as H0.
{ split. intro. rewrite inv_ack_interstate_3. omega. trivial.
  unfold inv_ack_helper. intro. simpl. rewrite not_lt. rewrite plus_comm.
  simpl. rewrite lt_succ_r. intro. assert (inv_ack_hier k n - (k + 3) = 0).
  { omega. } rewrite H1 in H. simpl in H. inversion H. }

induction i. { apply H0. }
intro. specialize (IHi (S k)). replace (i + S k) with (S i + k) in IHi.
split.
- intro. assert (H1 := H). rewrite IHi in H. rewrite inv_ack_interstate_3. omega.
  apply (Nat.le_trans _ (inv_ack_hier (S i + k) n) _).
  apply (Nat.le_trans _ (S i + k + 4) _). omega. trivial.
  apply inv_ack_hier_shrink_gen. trivial. omega.
- intro. rewrite IHi. rewrite inv_ack_interstate_3 in H. omega.
  rewrite H0. omega.
- omega.
Qed.


Theorem inv_ack_correct : forall x n, (inv_ack n <= x <-> n <= Ack x x).
Proof.
destruct n. { simpl. omega. }
destruct n.
{
simpl. destruct x. simpl. omega.
rewrite inv_ack_Ack. simpl. split.
- intro. apply (Nat.le_trans _ (inv_ack_hier 0 3) _).
  apply inv_ack_hier_shrink_gen. trivial. omega. simpl. omega.
- intro. omega. }
rewrite inv_ack_interstate_4. destruct x. { simpl. omega. }
rewrite <- le_S_n_m. rewrite inv_ack_Ack.
rewrite not_lt. rewrite not_lt.
rewrite <- le_succ_l. rewrite <- le_succ_l.
replace x with (x + 0). replace (S (S (x + 0) + 2)) with (x + 0 + 4).
rewrite (inv_ack_helper_thm x 0 _). rewrite (plus_comm _ 2). simpl.
omega. omega. omega. omega. omega.
Qed.