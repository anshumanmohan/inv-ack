Require Import Omega.
Require Import Setoid.


<<<<<<< HEAD
(*
=============================================================================
****************** SECTION 0: PRELIMINARIES *********************************
=============================================================================
*)


(* ************ 0.1. USEFUL LEMMAS ABOUT NAT ********************** *)

=======
(* USEFUL LEMMAS ABOUT NAT *)
(** Can't these all be dealt with via Omega?
 ** Why are we listing them again, and using them at all? 
 **)
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Lemma le_add_le_sub_r : forall n m p : nat, n + p <= m -> n <= m - p.
Proof. apply Nat.le_add_le_sub_r. Qed.

Lemma le_add_le_sub_l : forall n m p : nat, n + p <= m -> p <= m - n.
Proof. apply Nat.le_add_le_sub_l. Qed.

Lemma lt_add_lt_sub_r : forall n m p : nat, n + p < m <-> n < m - p.
Proof. apply Nat.lt_add_lt_sub_r. Qed.

Lemma lt_add_lt_sub_l : forall n m p : nat, n + p < m <-> p < m - n.
Proof. apply Nat.lt_add_lt_sub_l. Qed.

Lemma lt_le_S : forall n m : nat, n < m <-> S n <= m.
Proof. intros. omega. Qed.

Lemma minus_n_0 : forall n, n - 0 = n.
Proof. intros. rewrite minus_n_O. trivial. Qed.

Lemma sub_add_distr: forall n m p : nat, n - (m + p) = n - m - p.
Proof. intros. apply Nat.sub_add_distr. Qed.

Lemma sub_sub_comm: forall n m p: nat, n - m - p = n - p - m.
Proof.
  intros. rewrite <- sub_add_distr, <- sub_add_distr, plus_comm.
  trivial.
Qed.

Lemma add_sub_eq_l: forall n m p : nat, m + p = n -> n - m = p.
Proof.  apply Nat.add_sub_eq_l. Qed.

Lemma add_sub_eq_r: forall n m p : nat, m + p = n -> n - p = m.
Proof. apply Nat.add_sub_eq_r. Qed.

Lemma le_plus_minus: forall n m : nat, n <= m -> m = n + (m - n).
  apply le_plus_minus. Qed.

Lemma minus_S : forall n m : nat, n - m = S n - S m.
Proof. intros. omega. Qed.

Lemma le_S_n_m : forall n m : nat, n <= m <-> S n <= S m.
Proof. split. apply Peano.le_n_S. apply Peano.le_S_n. Qed.

Lemma lt_S_n_m : forall n m : nat, n < m <-> S n < S m.
Proof. intros. omega. Qed.

Lemma sub_compl: forall n m : nat, m <= n -> n - (n - m) = m.
Proof.
  intros. apply add_sub_eq_r. symmetry.
  apply le_plus_minus. trivial.
Qed.

Lemma sub_lt: forall n m : nat, m <= n -> 0 < m -> n - m < n.
Proof. apply Nat.sub_lt. Qed.

Lemma le_sub_l: forall n m : nat, n - m <= n.
Proof. apply Nat.le_sub_l. Qed.

Lemma le_succ_l: forall n m : nat, S n <= m <-> n < m.
Proof. apply Nat.le_succ_l. Qed.

Lemma lt_succ_r: forall n m : nat, n < S m <-> n <= m.
Proof. apply Nat.lt_succ_r. Qed.

Lemma lt_lt_0: forall n m : nat, n < m -> 0 < m.
Proof. apply Nat.lt_lt_0. Qed.

Lemma le_cases: forall n m : nat, n <= m -> (n <= m-1 \/ (n = m /\ m <> 0)).
Proof. intros. destruct H; omega. Qed.

Lemma nat_compare: forall n m : nat, S n <= m \/ n = m \/ S m <= n.
Proof. intros. omega. Qed.

Lemma not_lt: forall n m : nat, n <= m <-> ~ m < n.
Proof. split. omega. omega. Qed.

Lemma not_le: forall n m : nat, ~ n <= m <-> m < n.
Proof. split. omega. omega. Qed.

Lemma le_antisymm: forall n m : nat, n <= m -> m <= n -> n = m.
Proof. apply le_antisym. Qed.



(* ****** 0.2. CONTRACTING FUNCTIONS *************** *)

Fixpoint repeat (f: nat -> nat) (rep n : nat) : nat :=
  match rep with
  | 0 => n
  | S rep' => f (repeat f rep' n)
  end.

Theorem repeat_S_comm : forall f k n, repeat f (S k) n = repeat f k (f n).
Proof.
  induction k; trivial.
  intro. simpl in *; rewrite IHk; trivial.
Qed.

<<<<<<< HEAD
Definition contracting (f : nat -> nat) := forall m, f m <= m - 1.

Theorem repeat_contracting : forall f k l n,
(contracting f) -> (k < l) -> (repeat f l n <= repeat f k n - 1).
Proof.
intros f k l n Hf. unfold contracting in Hf.
induction l. { omega. }
intro. inversion H.
- apply Hf.
- clear H0 m. apply IHl in H1.
  apply (Nat.le_trans _ (repeat f l n - 1) _). apply Hf. omega.
Qed.


Lemma repeat_contract : forall f, contracting f -> (forall n k, repeat f k n <= n - k).
Proof.
intros f Hf n. induction k. { simpl. omega. }
simpl. apply (Nat.le_trans _ (repeat f k n - 1) _). apply Hf. omega.
Qed.


Lemma contract_f_0 : forall f, (contracting f) -> (forall k, repeat f k 0 = 0).
Proof.
induction k. { trivial. }
simpl. rewrite IHk. assert (f 0 <= 0). { apply H. } omega.
Qed.


Lemma contract_f_1 : forall f, (contracting f) -> (forall k, repeat f (S k) 1 = 0).
Proof.
induction k. { simpl. specialize (H 1). omega. }
replace (repeat f (S (S k)) 1) with (f (repeat f (S k) 1)) by trivial.
rewrite IHk. specialize (H 0). omega.
Qed.



(* *********** 0.3. INCREASING FUNCTIONS ****************** *)

Definition increasing (f : nat -> nat) : Prop := forall n m, n <= m -> f n <= f m.

Definition increasing_strict (f : nat -> nat) : Prop := forall n m, n < m -> f n < f m.


Lemma incr_S : forall f, increasing f <-> (forall n, f n <= f (S n)).
Proof.
intro f.
split.
- intros. apply H. omega.
- unfold increasing. intros.
  generalize dependent n.
  induction m.
  { intros. inversion H0. omega. }
  intros. inversion H0.
  + omega.
  + apply IHm in H2. apply (Nat.le_trans _ (f m) _).
    trivial. apply H.
=======
Definition shrinking (f : nat -> nat) :=
  forall m, f m <= m - 1.

(*
Why not...
Definition shrinking (f : nat -> nat) := forall m, f m < m.
*)

(** A couple examples of the kind of proof cleanup I think we could do **)
Theorem repeat_shrinking : forall f k l n,
    (shrinking f) -> (k < l) -> (repeat f l n <= repeat f k n - 1).
Proof.
  intros. generalize dependent l.
  unfold shrinking in H. induction k.
  - simpl; intros. destruct l; [inversion H0|].
    induction l; [trivial|].
    apply (Nat.le_trans _ (repeat f (S l) n) _); [|apply IHl; omega].
    apply (Nat.le_trans _ (f (repeat f l n) - 1) _); simpl; [apply H | omega].
  - induction l; [inversion 1|].
    intro. inversion H0; [subst; simpl; trivial|].
    apply (Nat.le_trans _ (repeat f l n) _); [simpl | apply IHl; omega].
    apply (Nat.le_trans _ (repeat f l n - 1) _); [apply H | omega].
Qed.

Theorem shrink_threshold : forall f n t,
    shrinking f ->
    n > t ->
    exists k, repeat f (S k) n <= t /\ t < repeat f k n.
Proof.
  intros f n t Hf Hn.
  remember (n - t) as l.
  replace t with (n - l) by omega; destruct l; [omega|].
  clear Heql. induction l.
  - exists 0.
    replace (n - 1) with (repeat f 0 n - 1) by trivial.
    split; [apply Hf | simpl; omega].
  - assert (n - S (S l) = n - S l - 1) by omega.
    rewrite H. remember (n - S l) as s.
    destruct IHl as [h Hs]. destruct Hs as [Hs1 Hs2].
    apply le_cases in Hs1. destruct Hs1 as [Hs1 | Hs1].
    + exists h. split; trivial. omega.
    + destruct Hs1 as [Hs0 Hs1]. exists (S h). simpl. split.
      * rewrite <- Hs0. apply Hf.
      * simpl in Hs0; rewrite Hs0; omega. 
Qed.

Lemma repeat_shrink : forall f, shrinking f -> (forall n k, repeat f k n <= n - k).
Proof.
  intros f Hf n. induction k; simpl; [omega|]. 
  apply (Nat.le_trans _ (repeat f k n - 1) _); [apply Hf | omega].
Qed.

Lemma shrink_f_0 : forall f, (shrinking f) -> (forall k, repeat f k 0 = 0).
Proof.
  induction k; trivial.
  simpl. rewrite IHk.
  assert (f 0 <= 0) by apply H; inversion H0. auto.
Qed.

Lemma shrink_f_1 : forall f, (shrinking f) -> (forall k, repeat f (S k) 1 = 0).
Proof.
  induction k.
  - specialize (H 1); inversion H; rewrite H1; trivial.
  - replace (repeat f (S (S k)) 1) with (f (repeat f (S k) 1)) by trivial.
    rewrite IHk; specialize (H 0); inversion H; rewrite H1; trivial.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.


Lemma incr_strict_S : forall f, increasing_strict f <-> (forall n, f n < f (S n)).
Proof.
intro f.
split.
- intros. apply H. omega.
- unfold increasing_strict. intros.
  generalize dependent n.
  induction m.
  { intros. inversion H0. }
  intros. inversion H0.
  + apply H.
  + apply IHm in H2. apply (Nat.lt_trans _ (f m) _).
    trivial. apply H.
Qed.


Lemma repeat_incr : forall f, increasing f -> (forall k, increasing (repeat f k)).
Proof.
intro f. unfold increasing. intro Hf.
induction k. simpl. intros. trivial.
intros. simpl. apply Hf. apply IHk. trivial.
Qed.



(* ************* 0.4. UPPER AND LOWER INVERSES ***************** *)

(* f is the upper inverse of F: f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : nat -> nat) : Prop
:= forall n N, f N <= n <-> N <= F n.

(* f is the lower inverse of F: f N is the largest n such that F n <= N *)
Definition low_inv_rel (f F : nat -> nat) : Prop
:= forall n N, n <= f N <-> F n <= N.


<<<<<<< HEAD

(* ************ 0.5. PROPERTIES PRESERVED BY INVERSES **************** *)


Definition st_expanding (F : nat -> nat) : Prop := forall n, S n <= F n.

Definition we_expanding (F : nat -> nat) : Prop := forall n, n <= F n - 1.


Lemma contract_upp_inv_st_expand :
forall f F, contracting f -> upp_inv_rel f F -> st_expanding F.
Proof.
intros f F Hf HfF n. rewrite <- (HfF n _).
apply (Nat.le_trans _ (S n - 1) _). apply Hf. omega.
Qed.


Lemma contract_low_inv_we_expand :
forall f F, contracting f -> low_inv_rel f F -> we_expanding F.
Proof.
intros f F Hf HfF n.
destruct n. { omega. }
rewrite le_succ_l. rewrite <- lt_add_lt_sub_l. simpl.
rewrite <- not_le. rewrite <- (HfF _ _).
intro.
assert (S n <= S n - 1).
{ apply (Nat.le_trans _ (f (S n)) _). apply H. apply Hf. }
omega.
Qed.


Lemma contract_upp_inv_positive :
forall f F, contracting f -> upp_inv_rel f F -> (forall n, 0 < F n).
Proof.
intros f F Hf HfF n. apply (Nat.le_trans _ (S n) _). omega.
generalize dependent n. apply (contract_upp_inv_st_expand f F). trivial. trivial.
Qed.


Lemma contract_incr_upp_inv_incr :
forall f F, contracting f -> increasing f -> upp_inv_rel f F -> increasing F.
Proof.
intros f F Hf_sh Hf_in HfF. rewrite incr_S. intro.
rewrite <- (HfF (S n) _). apply (Nat.le_trans _ n _).
- rewrite (HfF n _). trivial.
- omega.
Qed.


Lemma contract_incr_low_inv_incr :
forall f F, contracting f -> increasing f -> low_inv_rel f F -> increasing F.
Proof.
intros f F Hf_sh Hf_in HfF. rewrite incr_S. intro.
rewrite <- (HfF n _). apply (Nat.le_trans _ (S n) _).
- omega.
- rewrite (HfF (S n) _). trivial.
Qed.



(*
=============================================================================
****************** SECTION 1: COUNTDOWN *************************************
=============================================================================
*)

(* **************** 1.1. DEFINITION *************************************)

Fixpoint countdown_worker (f : nat -> nat) (n n1 cd : nat) : nat
:=
match n with
| 0 => 0
| 1 => 0
| S n' => match n1 with
          | 0 => 1
          | 1 => 1
          | _ =>
          match cd with
          | 0 => match (f n1) with | n2 => S(countdown_worker f n' n2 (n1 - n2 - 1)) end
          | S cd' => countdown_worker f n' n1 cd'
          end
          end
end.

Definition countdown f n
:= match (f n) with | n1 => countdown_worker f n n1 (n - n1 - 1)
end.

Definition countdown_fast f n
:= match n with
   | 0 => 0
   | 1 => 0
   | _ => match (f n) with
          | n1 => S(countdown f n1) end
end.
=======
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

(** Anshuman's version: **)
Fixpoint next_level_worker' (f : nat -> nat) (n n1 cd : nat) : nat :=
  match n, n1 with
  | 0, _ | 1, _ => 0
  | _, 0 => 1 | _, 1 => 1
  | S n', _ =>
    match cd with
    | 0 => S (next_level_worker' f n' (f n1) (n1 - f n1 - 1))
    | S cd' => next_level_worker' f n' n1 cd'
    end
  end.

Definition next_level f n := next_level_worker f n (f n) (n - f n - 1).

Definition next_level' f n := next_level_worker' f n (f n) (n - f n - 1).


(** example of potential cleanup **)

Definition next_level_fast f n
  := match n with
     | 0 => 0
     | 1 => 0
     | _ => match (f n) with
            | n1 => S (next_level f n1) end
     end.

(* this is the countdown of f *)
Definition next_level_fast' f n :=
  match n with
  | 0 | 1 => 0
  | _ => S (next_level f (f n))
  end.
(* but we need to make it a fixpoint and explain the
   decreasing argument.
   Are there hidden requirements that have not been fleshed out?
   f needs to be shrinking?
 *) 

(* Fixpoint next_level_fix f n {struct n} := *)
(*   match n with *)
(*   | 0 | S 0  => 0 *)
(*   | S (S _) => S (next_level_fix f (f n)) *)
(*   end. *)

>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

Definition sub2 (n : nat) : nat := n - 2.
(* Just use "Nat.sub 2" ? *)

Compute next_level_fast' sub2 2.
Compute next_level_fast' sub2 3.
Compute next_level sub2 8.

Lemma countdown_gives_div_2: forall n,
    next_level (Nat.sub 2) n = n / 2 .
Proof. Abort.

Definition mylog := next_level' (next_level' sub2).

<<<<<<< HEAD

=======
Compute Nat.log2 3.

Lemma countdown_gives_log_2: forall n,
    next_level' (next_level' (Nat.sub 2)) n = Nat.log2 n.
Proof. Abort.        
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

(*==================================================================
**************** 1.2. THEOREMS ************************************* *)


(* LEMMAS ABOUT COUNTDOWN_WORKER *)

<<<<<<< HEAD
Lemma countdown_interstate_1 : forall f n n1 cd k,
(2 <= n1) -> (k <= cd) -> (k <= n)
-> countdown_worker f n n1 cd = countdown_worker f (n - k) n1 (cd - k).
Proof.
intros f n n1 cd k Hn1.
generalize dependent cd.
generalize dependent k.
induction n. { trivial. }
intros k cd Hk Hkn1.
destruct k. {
  replace (S n - 0) with (S n) by omega. 
  replace (cd - 0) with cd by omega. trivial. }
destruct cd. { inversion Hk. }
replace (S n - S k) with (n - k) by omega.
replace (S cd - S k) with (cd - k) by omega.
rewrite <- IHn.
- destruct n. { trivial. }
  destruct n1. { inversion Hn1. }
  destruct n1. { inversion Hn1. inversion H0. }
  trivial.
- omega.
- omega.
Qed.


Lemma countdown_interstate_2 : forall f n,
contracting f -> 2 <= n -> countdown f n = 1 + countdown f (f n).
Proof.
intros. unfold countdown.
destruct n. { omega. }
destruct n. { omega. }
remember (f (S (S n))) as n1.
destruct n1. { trivial. }
destruct n1. { trivial. }
remember (S (S n) - S (S n1) - 1) as cd.
rewrite (countdown_interstate_1 _ _ _ _ cd).
- replace (cd - cd) with 0 by omega.
  rewrite Heqcd.
  replace (S (S n) - (S (S n) - S (S n1) - 1)) with ((S (S (S n1)))).
  + trivial.
  + replace (S (S n) - S (S n1) - 1) with (S(S n) - (S(S(S n1)))) by omega.
    assert ((S(S n1)) <= (S n)). { rewrite Heqn1. apply H. } omega.
- omega.
- trivial.
- omega.
=======
Lemma next_level_interstate_1 : forall f n n1 cd k,
    2 <= n1 ->
    k <= cd ->
    k <= n ->
    next_level_worker f n n1 cd = next_level_worker f (n - k) n1 (cd - k).
Proof.
  intros f n n1 cd k Hn1. generalize dependent cd.
  generalize dependent k. induction n; trivial.
  intros k cd Hk Hkn1.
  destruct k; [repeat rewrite minus_n_0; trivial|]. 
  destruct cd; [inversion Hk|].
  apply le_S_n_m in Hk. rewrite <- le_S_n_m in Hkn1.
  repeat rewrite Nat.sub_succ. rewrite <- (IHn _ _ Hk Hkn1).
  destruct n; trivial.
  destruct n1; [inversion Hn1|].
  destruct n1; [inversion Hn1; inversion H0|]; trivial. 
Qed.

Lemma next_level_interstate_2 : forall f n,
    shrinking f ->
    2 <= n ->
    next_level f n = 1 + next_level f (f n).
Proof.
  intros. unfold next_level. destruct n; [inversion H0|].
  destruct n; [inversion H0; inversion H2|].
  remember (f (S (S n))) as n1.
  destruct n1; trivial. destruct n1; trivial.
  remember (S (S n) - S (S n1) - 1) as cd.
  rewrite (next_level_interstate_1 _ _ _ _ cd); [|omega | trivial | omega].
  rewrite Nat.sub_diag.
  assert (S (S n) - cd = (S (S (S n1)))). 
  { rewrite Heqcd. rewrite <- sub_add_distr, plus_comm, sub_compl; trivial.
    rewrite <- le_S_n_m. rewrite Heqn1. apply H. }
  rewrite H1. trivial.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.


(* CORRECTNESS THEOREMS *)

(* Another example *)

<<<<<<< HEAD
Theorem countdown_repeat_1 : forall f n k,
contracting f -> (repeat f k n <= 1 <-> countdown f n <= k).
Proof.
intros.
generalize dependent n.
induction k.
{ intro n. simpl.
  destruct n. { unfold countdown. simpl. omega. }
  destruct n. { unfold countdown. simpl. omega. }
  rewrite countdown_interstate_2. omega. trivial. omega.
}
intro n.
destruct n. { unfold countdown. rewrite contract_f_0. simpl. omega. trivial. }
destruct n. { unfold countdown. rewrite contract_f_1. simpl. omega. trivial. }
rewrite repeat_S_comm.
rewrite countdown_interstate_2.
- rewrite IHk. omega.
- trivial.
- omega.
Qed.


Theorem countdown_repeat_2 : forall (f : nat -> nat) (n k : nat),
        contracting f
        -> ((countdown f n = k)
        <-> (repeat f k n <= 1 /\ (forall p, repeat f p n <= 1 -> k <= p))). 
Proof.
intros f n k Hf.
split.
- intro Hk. split.
  + rewrite countdown_repeat_1. omega. trivial.
  + intros p Hp. rewrite <- Hk. rewrite <- countdown_repeat_1. trivial. trivial.
- intro Hk. destruct Hk as [Hk1 Hk2].
  apply le_antisym.
  + rewrite <- countdown_repeat_1. trivial. trivial.
  + apply (Hk2 (countdown f n)). rewrite countdown_repeat_1. trivial. trivial.
Qed.


(* CONTRACTING PRESERVE THEOREM *)

Theorem countdown_contract : forall f,
contracting f -> contracting (countdown f).
Proof.
intros f Hf. unfold contracting.
intros. rewrite <- countdown_repeat_1.
apply (Nat.le_trans _ (m - (m - 1)) _).
apply repeat_contract. trivial. omega. trivial.
Qed.

(* INCREASING PRESERVE THEOREM *)

Theorem countdown_incr : forall f,
contracting f -> increasing f -> increasing (countdown f).
Proof.
intros f Hf0 Hf1 n m Hnm.
apply countdown_repeat_1. trivial.
assert (increasing (repeat f (countdown f m))).
{ apply repeat_incr. trivial. }
specialize (H n m).
apply H in Hnm.
apply (Nat.le_trans _ (repeat f (countdown f m) m) _).
- trivial.
- apply countdown_repeat_1. trivial. trivial.
=======
Theorem next_level_repeat_1 : forall f n k,
    shrinking f ->
    repeat f k n <= 1 <-> next_level f n <= k.
Proof.
  intros. generalize dependent n. induction k; intro n.
  - simpl. destruct n.
    + unfold next_level. simpl; omega.
    + destruct n; [now unfold next_level|]. 
      rewrite next_level_interstate_2; [omega | trivial | omega].
  - destruct n.
    + unfold next_level. rewrite shrink_f_0; [simpl; omega | trivial].
    + destruct n.
      * unfold next_level. rewrite shrink_f_1; [simpl; omega | trivial].
      * rewrite repeat_S_comm, next_level_interstate_2, <- le_S_n_m;
          [trivial | trivial | omega].
Qed.

Theorem next_level_repeat_2 : forall (f : nat -> nat) (n k : nat),
    shrinking f ->
    next_level f n = k <->
    repeat f k n <= 1 /\ forall p, repeat f p n <= 1 -> k <= p. 
Proof.
  intros f n k Hf. split.
  - intro Hk. split.
    + rewrite next_level_repeat_1; [omega | trivial].
    + intros p Hp. rewrite <- Hk, <- next_level_repeat_1; trivial.
  - intro Hk. destruct Hk as [Hk1 Hk2].
    apply le_antisym.
    + rewrite <- next_level_repeat_1; trivial.
    + apply (Hk2 (next_level f n)); rewrite next_level_repeat_1; trivial. 
Qed.


(* PROPER SHRINKING PRESERVE THEOREM *)

Theorem next_level_shrink : forall f,
    shrinking f -> shrinking (next_level f).
Proof.
  intros f Hf. unfold shrinking.
  intros. rewrite <- next_level_repeat_1; trivial.
  assert (forall n k, repeat f k n <= n - k) by
      (apply repeat_shrink; trivial).
  specialize (H m (m - 1)); omega.
Qed.


(* INCREASING FUNCTIONS *)

Definition increasing (f : nat -> nat) : Prop := forall n m, n <= m -> f n <= f m.

Definition increasing_strict (f : nat -> nat) : Prop := forall n m, n < m -> f n < f m.

Lemma incr_S : forall f, increasing f <-> (forall n, f n <= f (S n)).
Proof.
  intro. split.
  - intros. apply H. omega.
  - unfold increasing. intros. generalize dependent n.
    induction m; intros; inversion H0; [omega | omega|].
    intros. inversion H0. omega. apply IHm in H2. apply (Nat.le_trans _ (f m) _); [trivial | apply H]. 
Qed.

Lemma incr_strict_S : forall f, increasing_strict f <-> (forall n, f n < f (S n)).
Proof.
  intro. split.
  - intros. apply H. omega.
  - unfold increasing_strict. intros. generalize dependent n. induction m.
    + intros. inversion H0.
    + intros. inversion H0; [apply H|].
      apply IHm in H2. apply (Nat.lt_trans _ (f m) _); [trivial | apply H].
Qed.

Lemma repeat_incr : forall f, increasing f -> (forall k, increasing (repeat f k)).
Proof.
  intro f. unfold increasing. intro Hf.
  induction k.
  - simpl. intros. trivial.
  - intros. simpl. apply Hf. apply IHk. trivial.
Qed.

Theorem next_level_incr : forall f,
    shrinking f ->
    increasing f ->
    increasing (next_level f).
Proof.
  intros f Hf0 Hf1 n m Hnm. apply next_level_repeat_1; trivial.
  assert (increasing (repeat f (next_level f m))) by
      (apply repeat_incr; trivial). 
  apply (H n m) in Hnm.
  apply (Nat.le_trans _ (repeat f (next_level f m) m) _); trivial.
  apply next_level_repeat_1; trivial.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.


(*
=============================================================================
****************** SECTION 2: REPEATER **************************************
=============================================================================
*)

<<<<<<< HEAD

Fixpoint repeater F n : nat :=
match n with
| 0 => 1
| S n' => F (repeater F n')
end.
=======
Definition can_inv_rel (f F : nat -> nat) : Prop
  := forall n N, f N <= n <-> N <= F n.

(* this is the repeater of F *)
Fixpoint next_can_level F n : nat :=
  match n with
  | 0 => 1
  | S n' => F (next_can_level F n')
  end.

Lemma repeater_gives_times_2: forall n,
    next_can_level (Nat.add 2) n = S (n * 2).
Proof.
  intros. induction n; trivial.
  simpl. do 2 f_equal.
  rewrite <- IHn; f_equal.
Qed.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

Lemma repeater_gives_times_n: forall n m,
    next_can_level (Nat.add n) m =  S (n * m).
Proof.
  intros. induction m; [simpl; omega|].
  replace (S (n * S m)) with (n + S (n * m)) by (rewrite Nat.mul_succ_r; omega).
  simpl; f_equal; omega.
Qed.
(** There is an off-by-one issue here, obviously **)

<<<<<<< HEAD
Theorem upp_inv_preserve : forall f F,
contracting f -> increasing f -> upp_inv_rel f F
-> upp_inv_rel (countdown f) (repeater F).
Proof.
intros f F Hf1 Hf2 HfF. unfold upp_inv_rel.
induction n.
{ simpl. intro. rewrite <- countdown_repeat_1. simpl. omega. trivial. }
intro. simpl.
destruct N. { unfold countdown. simpl. omega. }
destruct N.
{ unfold countdown. simpl. split.
  - intro. apply (contract_upp_inv_positive f F). trivial. trivial.
  - intro. omega. }
rewrite countdown_interstate_2. rewrite <- le_S_n_m.
rewrite (IHn (f (S (S N)))). apply HfF. trivial. omega.
=======
(** Let's try and fix the off-by-one issue. **)

(* this is the repeater of F with a dumb modification *)
Fixpoint next_can_level' F n : nat :=
  match n with
  | 0 => 0
  | S n' => F (next_can_level' F n')
  end.

Lemma repeater_gives_times_n_correctly: forall n m,
    next_can_level' (Nat.add n) m =  n * m.
Proof.
  intros. induction m; [simpl; omega|].
  simpl; rewrite IHm; rewrite Nat.mul_succ_r; omega.
Qed.

(* Fine... *)

Compute next_can_level' (Nat.add 2) 5.
Compute (next_can_level' (next_can_level' (Nat.add 2)) 5).
(* Well, this is very wrong... but this makes a lot of sense actually. *)

(* Okay so let's try and encode Wikipedia's definition of 
 * Knuth's Up Arrow *)

Require Coq.Program.Wf.

Fixpoint kua a n b :=
  match n with
  | 0 => a * b
  | S n' =>
    let fix kua' b :=
        match b with
        | 0 => 1
        | S b' => kua a n' (kua' b')
        end
    in kua' b
  end.

Definition growing (F : nat -> nat) : Prop := forall n, S n <= F n.

Lemma can_inv_growing : forall f F,
    shrinking f ->
    can_inv_rel f F ->
    growing F.
Proof.
  intros f F Hf HfF n. rewrite <- (HfF n _).
  apply (Nat.le_trans _ (S n - 1) _); [apply Hf | omega].
Qed.

Lemma can_inv_positive : forall f F,
    shrinking f ->
    can_inv_rel f F ->
    forall n, 0 < F n.
Proof.
  intros f F Hf HfF n. apply (Nat.le_trans _ (S n) _); [omega|].
  generalize dependent n. apply (can_inv_growing f F); trivial. 
Qed.

Lemma can_inv_increasing : forall f F,
    shrinking f ->
    increasing f ->
    can_inv_rel f F ->
    increasing F.
Proof.
  intros f F Hf_sh Hf_in HfF. rewrite incr_S. intro.
  rewrite <- (HfF (S n) _). apply (Nat.le_trans _ n _).
  rewrite (HfF n _). trivial. omega.
Qed.


Theorem inv_next_level_can : forall f F,
    shrinking f ->
    increasing f ->
    can_inv_rel f F ->
    can_inv_rel (next_level f) (next_can_level F).
Proof.
  intros f F Hf1 Hf2 HfF. unfold can_inv_rel.
  induction n.
  - simpl. intro. rewrite <- next_level_repeat_1; [simpl; omega | trivial].
  - intro. simpl. destruct N; [unfold next_level; simpl; omega|].
    destruct N.
    + unfold next_level. simpl. split.
      * intro. apply (can_inv_positive f F); trivial. 
      * omega. 
    + rewrite next_level_interstate_2, <- le_S_n_m; [|trivial | omega].
      rewrite (IHn (f (S (S N)))). apply HfF.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.


Print low_inv_rel.


(*
(* PACKING EVERYTHING *)

Definition inv_ack_like_rel f F : Prop :=
<<<<<<< HEAD
(contracting f) /\ (increasing f)
/\ (upp_inv_rel f F) /\ (st_expanding F) /\ (increasing F).



Theorem countdown_inv_ack_like : forall f F,
inv_ack_like_rel f F -> inv_ack_like_rel (countdown f) (repeater F).
Proof.
intros. destruct H. destruct H0. destruct H1. destruct H2.
assert (contracting (countdown f)). { apply countdown_contract. trivial. }
assert (upp_inv_rel (countdown f) (repeater F)).
{ apply upp_inv_preserve; trivial. }
split. { trivial. }
split. { apply countdown_incr; trivial. }
split. { apply upp_inv_preserve; trivial. }
split. { apply (contract_upp_inv_st_expand (countdown f) _); trivial. }
apply (contract_incr_upp_inv_incr (countdown f) _); trivial. apply countdown_incr; trivial.
=======
  shrinking f /\
  increasing f /\
  can_inv_rel f F /\
  growing F /\
  increasing F.

Theorem next_level_inv_ack_like : forall f F,
    inv_ack_like_rel f F ->
    inv_ack_like_rel (next_level f) (next_can_level F).
Proof.
  intros. destruct H as [? [? [? [? ?]]]].
  assert (shrinking (next_level f))
    by now apply next_level_shrink.
  assert (can_inv_rel (next_level f) (next_can_level F))
    by now apply inv_next_level_can.
  split; [trivial|].
  split; [apply next_level_incr; trivial|].
  split; [apply inv_next_level_can; trivial|].
  split; [apply (can_inv_growing (next_level f) _); trivial|].
  apply (can_inv_increasing (next_level f) _);
    [|apply next_level_incr|]; trivial.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.
*)


(* INVERSE ACKERMANN HIERARCHY *)

(* ZEROTH LEVEL : MINUS *)
Definition minus_b b n := n - b.

Definition minus_2 n :=
  match n with
  | 0 | 1 => 0
  | S (S n') => n'
  end.

Lemma minus_2_correct: forall n, minus_2 n = n - 2.
Proof.
  unfold minus_2. 
  destruct n; [trivial | destruct n; [trivial | omega]].
Qed.

<<<<<<< HEAD
Theorem minus_2_contract: contracting minus_2.
Proof.
intro. rewrite minus_2_correct. omega.
Qed.
=======
Theorem minus_2_shrink: shrinking minus_2.
Proof. intro. rewrite minus_2_correct. omega. Qed.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

Theorem minus_b_shrink: forall b, 0 < b -> shrinking (minus_b b).
Proof. unfold minus_b, shrinking. intros. omega. Qed.

(* HIGHER LEVELS *)

<<<<<<< HEAD
Fixpoint inv_ack_hier i n
:= match i with
   | 0 => minus_2 n
   | S i' => countdown (inv_ack_hier i') n
end.

Fixpoint ack_hier i n
:= match i with
   | 0 => S(S n)
   | S i' => repeater (ack_hier i') n
end.

Fixpoint inv_ack_hier_fast i n
:= match i with
   | 0 => minus_2 n
   | S i' => countdown_fast (inv_ack_hier i') n
end.

=======
(* I think you want minus_b here *)
Fixpoint inv_ack_hier i n :=
  match i with
  | 0 => minus_2 n
  | S i' => next_level (inv_ack_hier i') n
  end.

(* trying with minus_b instead... *)
Fixpoint inv_ack_hier_b b i n :=
  match i with
  | 0 => minus_b b n
  | S i' => next_level (inv_ack_hier_b b i') n
  end.

Fixpoint ack_hier i n :=
  match i with
  | 0 => S (S n)
  | S i' => next_can_level (ack_hier i') n
  end.

Fixpoint ack_hier_b b i n :=
  match i with
  | 0 => n + b
  | S i' => next_can_level (ack_hier_b b i') n
  end.

Fixpoint inv_ack_hier_fast i n :=
  match i with
  | 0 => minus_2 n
  | S i' => next_level_fast (inv_ack_hier i') n
  end.
(** Two things, 
   1. how about
      S i' => next_level_fast (inv_ack_hier_fast i') n
   2. how about minus_b instead? 
 **)

(** trying both of these below... **)
Fixpoint inv_ack_hier_faster_b b i n :=
  match i with
  | 0 => minus_b b n
  | S i' => next_level_fast (inv_ack_hier_faster_b b i') n
  end.

Lemma issame: forall f n,
    next_level f n = next_level_fast f n.
Abort.

Lemma issame2: forall i n,
    inv_ack_hier_fast i n = inv_ack_hier_faster_b 2 i n.
Proof.
  intros. unfold inv_ack_hier_faster_b, inv_ack_hier_fast.
  destruct i; [unfold minus_b; apply minus_2_correct|].
  f_equal. unfold inv_ack_hier.
  destruct i; [unfold minus_b; admit|]. 
Abort.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

Theorem inv_hier_ack_hier :
  forall i, inv_ack_like_rel (inv_ack_hier i) (ack_hier i).
Proof.
<<<<<<< HEAD
induction i.
- simpl. unfold inv_ack_like_rel. unfold minus_b. split.
  { unfold contracting. intro. apply minus_2_contract. } split.
  { unfold increasing. intros. repeat rewrite minus_2_correct. omega. } split.
  { unfold upp_inv_rel. intros. rewrite minus_2_correct. omega.  } split.
  { unfold st_expanding. intros. replace (S n) with (1 + n). omega. trivial. }
  { unfold increasing. intros. omega. }
- apply countdown_inv_ack_like. trivial.
=======
  induction i.
  - simpl. unfold inv_ack_like_rel.
    split; [unfold shrinking; apply minus_2_shrink|].
    split; [unfold increasing; intros; repeat rewrite minus_2_correct; omega|].
    split; [unfold can_inv_rel; intros; rewrite minus_2_correct; omega|].
    split; [unfold growing; intros; replace (S n) with (1 + n) by omega; trivial; omega|].
    unfold increasing. intros. omega. 
  - apply next_level_inv_ack_like. trivial.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.

Theorem inv_hier_ack_hier_b :
  forall b i,
    0 < b -> inv_ack_like_rel (inv_ack_hier_b b i) (ack_hier_b b i).
Proof.
  induction i; intro.
  - simpl. unfold inv_ack_like_rel; unfold minus_b.
    split; [unfold shrinking; apply minus_b_shrink; omega|].
    split; [unfold increasing; intros; omega|].
    split; [unfold can_inv_rel; intros; omega|].
    split; [unfold growing; intros; replace (S n) with (1 + n) by omega; trivial; omega|].
    unfold increasing. intros. omega.
  - apply next_level_inv_ack_like; specialize (IHi H); trivial.
Qed.

Corollary inv_ack_hier_each_incr : forall i, increasing (inv_ack_hier i).
  intro.
  pose proof inv_hier_ack_hier i.
  unfold inv_ack_like_rel in H.
  destruct H as [_ [H _]];  trivial.
Qed.

Corollary inv_ack_hier_each_incr_b : forall b i,
    0 < b -> increasing (inv_ack_hier_b b i).
  intros.
  pose proof (inv_hier_ack_hier_b b i H).
  unfold inv_ack_like_rel in H0.
  destruct H0 as [_ [H0 _]];  trivial.
Qed.

<<<<<<< HEAD
Corollary inv_ack_hier_each_contract : forall i, contracting (inv_ack_hier i).
intro. assert (H := (inv_hier_ack_hier i)). unfold inv_ack_like_rel in H.
destruct H as [H _]. trivial. Qed.
=======
Corollary inv_ack_hier_each_shrink : forall i, shrinking (inv_ack_hier i).
  intro. pose proof inv_hier_ack_hier i.
  unfold inv_ack_like_rel in H.
  destruct H as [H _]; trivial.
Qed.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

Corollary inv_ack_hier_each_shrink_b : forall b i, 0 < b -> shrinking (inv_ack_hier_b b i).
  intros. pose proof (inv_hier_ack_hier_b b i H).
  unfold inv_ack_like_rel in H0.
  destruct H0 as [H0 _]; trivial.
Qed.

<<<<<<< HEAD
Corollary inv_ack_hier_contract : forall i n,
(3 <= n) -> (inv_ack_hier (S i) n) <= inv_ack_hier i n.
Proof.
intros. assert (Hi := (inv_ack_hier_each_contract i)). simpl.
rewrite <- countdown_repeat_1. remember (inv_ack_hier i n) as m.
destruct m.
- simpl. destruct i. { simpl in Heqm. rewrite minus_2_correct in Heqm. omega. }
  symmetry in Heqm. simpl in Heqm. rewrite countdown_repeat_2 in Heqm.
  destruct Heqm as [Heqm _]. simpl in Heqm. trivial. apply inv_ack_hier_each_contract.
- rewrite repeat_S_comm. apply (Nat.le_trans _ (inv_ack_hier i n - m) _).
  apply repeat_contract. trivial. omega.
- trivial.
Qed.


Corollary inv_ack_hier_contract_gen : forall i j n,
(3 <= n) -> (i <= j) -> (inv_ack_hier j n) <= inv_ack_hier i n.
Proof.
intros i j n Hn Hij. generalize dependent i.
induction j. { intros. inversion Hij. trivial. }
intros. inversion Hij.
{ trivial. }
apply (Nat.le_trans _ (inv_ack_hier j n) _).
{ apply inv_ack_hier_contract. trivial. }
apply IHj. trivial.
=======
Corollary inv_ack_hier_shrink : forall i n,
    (3 <= n) -> (inv_ack_hier (S i) n) <= inv_ack_hier i n.
Proof.
  intros. assert (Hi := (inv_ack_hier_each_shrink i)). simpl.
  rewrite <- next_level_repeat_1 by trivial.
  remember (inv_ack_hier i n) as m; destruct m.
  - simpl. destruct i.
    + simpl in Heqm. rewrite minus_2_correct in Heqm. omega.
    + symmetry in Heqm. simpl in Heqm. rewrite next_level_repeat_2 in Heqm.
      * destruct Heqm as [Heqm _]. simpl in Heqm. trivial.
      * apply inv_ack_hier_each_shrink.
  - rewrite repeat_S_comm. apply (Nat.le_trans _ (inv_ack_hier i n - m) _);
                             [apply repeat_shrink; trivial | omega].
Qed.

Corollary inv_ack_hier_shrink_gen : forall i j n,
    3 <= n ->
    i <= j ->
    inv_ack_hier j n <= inv_ack_hier i n.
Proof.
  intros i j n Hn Hij. generalize dependent i.
  induction j.
  - intros. inversion Hij. trivial.
  - intros. inversion Hij; trivial.
    apply (Nat.le_trans _ (inv_ack_hier j n) _);
      [apply inv_ack_hier_shrink | apply IHj]; trivial.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
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
  induction n; trivial.
  unfold Ack. simpl. unfold Ack in IHn. rewrite IHn; trivial.
Qed.

Lemma ack_hier_1 : forall m, ack_hier m 1 = 3.
Proof. induction m; trivial. Qed.

Theorem ack_hier_Ack : forall m n, ack_hier m (n + 2) = Ack (m + 1) n + 2.
Proof.
  induction m.
  - intro. rewrite Ack_1. simpl. omega.
  - induction n; simpl.
    + rewrite <- (IHm 1). rewrite ack_hier_1. trivial. 
    + simpl in IHn. rewrite IHn. rewrite IHm. trivial.
Qed.

Theorem inv_ack_Ack : forall n x y,
    n <= Ack (S x) y <-> inv_ack_hier x (n + 2) <= y + 2.
Proof.
  intros. assert (inv_ack_like_rel (inv_ack_hier x) (ack_hier x)) by
      apply inv_hier_ack_hier. 
  destruct H as [_ [_ [H _]]]. 
  rewrite (H (y+2) (n+2)). rewrite ack_hier_Ack.
  replace (x+1) with (S x); omega. 
Qed.


(* INVERSE ACKERMANN DEFINITION *)

Definition inv_ack_rel n a := forall x,
    n <= Ack x x <-> a <= x.

(* Find minimum u such that inv_ack_hier u n <= u + 3 *)
Fixpoint inv_ack_worker n f cd1 cd0 :=
<<<<<<< HEAD
match cd0 with
| 0 => 0
| 1 => 1
| S cd0' => match cd1 with
            | 0 => match (countdown f) with
                   | f' => S (inv_ack_worker n f' (n - f' n - 1) cd0') end
            | S cd1' => inv_ack_worker (n - 1) f cd1' cd0' end
end.
=======
  match cd0 with
  | 0 => 0
  | 1 => 1
  | S cd0' =>
    match cd1 with
    | 0 => match (next_level f) with
             f' => S (inv_ack_worker n f' (n - f' n - 1) cd0') end 
    | S cd1' => inv_ack_worker (n - 1) f cd1' cd0'
    end
  end.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383

Definition inv_ack_helper i n :=
  match (inv_ack_hier i), (inv_ack_hier (S i)) with
  | f0, f1 => inv_ack_worker (f0 n) f1 (f0 n - f1 n) (f0 n - (i + 3))
  end.

Definition inv_ack n :=
  match n with
  | 0 | 1 => 0
  | _ => inv_ack_worker (S (S n)) minus_2 2 n
  end.

Theorem inv_ack_interstate_1 : forall n f cd1 cd0 k,
    k <= cd1 ->
    k < cd0 ->
    inv_ack_worker n f cd1 cd0 = inv_ack_worker (n - k) f (cd1 - k) (cd0 - k).
Proof.
  intros n f cd1 cd0 k. generalize dependent cd0.
  generalize dependent cd1. generalize dependent n.
  induction k.
  - intros. repeat rewrite minus_n_0. trivial.
  - intros n cd1 cd0 HSk1 HSk0.
    destruct cd0; [omega|].
    destruct cd0; [omega|].
    destruct cd1; [omega|].
    rewrite <- le_S_n_m in HSk1. rewrite <- lt_S_n_m in HSk0.
    apply (IHk (n - 1) cd1 (S cd0)) in HSk1; trivial.
    repeat rewrite <- minus_S. rewrite <- sub_add_distr in HSk1.
    unfold plus in HSk1. rewrite <- HSk1; trivial.
Qed.

Theorem inv_ack_interstate_2 : forall n f cd1 cd0,
<<<<<<< HEAD
(1 <= cd0) -> inv_ack_worker n f cd1 cd0
= S (inv_ack_worker (n - cd1) (countdown f)
     ((n - cd1) - (countdown f (n - cd1)) - 1) (cd0 - cd1 - 1)).
=======
    1 <= cd0 ->
    inv_ack_worker n f cd1 cd0 =
    S (inv_ack_worker (n - cd1) (next_level f)
                      ((n - cd1) - (next_level f (n - cd1)) - 1) (cd0 - cd1 - 1)).
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Proof.
  intros n f cd1 cd0 H. remember (cd0 - cd1) as m.
  destruct m.
  - rewrite (inv_ack_interstate_1 _ _ _ _ (cd0 - 1)); [|omega..].
    simpl. rewrite sub_compl; trivial.
  - rewrite (inv_ack_interstate_1 _ _ _ _ cd1); [|trivial | omega].
    rewrite Nat.sub_diag.
    destruct m; [simpl; rewrite <- Heqm; trivial|]. 
    rewrite <- Heqm. rewrite <- minus_S. rewrite minus_n_0. trivial.
Qed.

Theorem inv_ack_interstate_3 : forall i n, 
<<<<<<< HEAD
(i + 4 <= inv_ack_hier i n) -> inv_ack_helper i n = 1 + inv_ack_helper (S i) n.
Proof.
intros i n Hin.
unfold inv_ack_helper. remember (inv_ack_hier i) as f0.
remember (inv_ack_hier (S i)) as f1. remember (inv_ack_hier (S(S i))) as f2.
assert (4 <= n) as Hn.
{ assert (H := (inv_ack_hier_each_contract i n)). rewrite <- Heqf0 in H. omega. }
assert (f1 n <= f0 n).
{ rewrite Heqf1. rewrite Heqf0. apply inv_ack_hier_contract. omega. }
rewrite inv_ack_interstate_2. simpl.
replace (f0 n - (f0 n - f1 n)) with (f1 n).
assert (f2 = countdown f1) as Hf12. { rewrite Heqf1. rewrite Heqf2. trivial. }
rewrite <- Hf12.
rewrite <- sub_add_distr. replace (f2 (f1 n) + 1) with (f2 n).
replace (f0 n - (i + 3) - (f0 n - f1 n) - 1) with (f1 n - S (i + 3)).
- trivial.
- rewrite <- sub_sub_comm. rewrite <- (sub_add_distr _ (i + 3) _).
  rewrite (plus_comm 1 _). rewrite <- sub_sub_comm. omega.
- rewrite Hf12. rewrite plus_comm.
  rewrite countdown_interstate_2. trivial.
  rewrite Heqf1. apply inv_ack_hier_each_contract. omega.
- omega.
- omega.
=======
    i + 4 <= inv_ack_hier i n ->
    inv_ack_helper i n = 1 + inv_ack_helper (S i) n.
Proof.
  intros i n Hin.
  unfold inv_ack_helper. remember (inv_ack_hier i) as f0.
  remember (inv_ack_hier (S i)) as f1. remember (inv_ack_hier (S(S i))) as f2.
  assert (4 <= n) as Hn by
        (assert (H := (inv_ack_hier_each_shrink i n)); rewrite <- Heqf0 in H; omega).
  assert (f1 n <= f0 n) by
      (rewrite Heqf1; rewrite Heqf0; apply inv_ack_hier_shrink; omega). 
  rewrite inv_ack_interstate_2; [|omega].
  replace (f0 n - (f0 n - f1 n)) with (f1 n); [|omega].
  assert (f2 = next_level f1) as Hf12; [rewrite Heqf1, Heqf2; trivial|]. 
  rewrite <- Hf12, <- sub_add_distr.
  replace (f2 (f1 n) + 1) with (f2 n).
  replace (f0 n - (i + 3) - (f0 n - f1 n) - 1) with (f1 n - S (i + 3)).
  - trivial.
  - rewrite <- sub_sub_comm, <- (sub_add_distr _ (i + 3) _), 
    (plus_comm 1 _), <- sub_sub_comm. omega.
  - rewrite Hf12. rewrite plus_comm.
    rewrite next_level_interstate_2; [trivial| |omega].
    rewrite Heqf1. apply inv_ack_hier_each_shrink.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.

Theorem inv_ack_interstate_4 : forall n,
<<<<<<< HEAD
(2 <= n) -> inv_ack n = 1 + inv_ack_helper 0 (S(S n)).
Proof.
intro. unfold inv_ack_helper. simpl.
destruct n. { omega. } destruct n. { omega. }
assert (S(S(S(S n))) - 2 = S(S n)). { omega. }
intro. clear H0. unfold inv_ack. rewrite inv_ack_interstate_2.
rewrite H. rewrite <- sub_add_distr. rewrite <- sub_add_distr.
rewrite plus_comm. rewrite <- minus_2_correct in H.
rewrite <- H. rewrite <- (countdown_interstate_2 minus_2 _). trivial.
apply minus_2_contract. omega. omega.
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
  apply inv_ack_hier_contract_gen. trivial. omega.
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
  apply inv_ack_hier_contract_gen. trivial. omega. simpl. omega.
- intro. omega. }
rewrite inv_ack_interstate_4. destruct x. { simpl. omega. }
rewrite <- le_S_n_m. rewrite inv_ack_Ack.
rewrite not_lt. rewrite not_lt.
rewrite <- le_succ_l. rewrite <- le_succ_l.
replace x with (x + 0). replace (S (S (x + 0) + 2)) with (x + 0 + 4).
rewrite (inv_ack_helper_thm x 0 _). rewrite (plus_comm _ 2). simpl.
omega. omega. omega. omega. omega.
=======
    2 <= n ->
    inv_ack n = 1 + inv_ack_helper 0 (S (S n)).
Proof.
  intro. unfold inv_ack_helper. simpl.
  destruct n; [omega|].
  destruct n; [omega|].
  assert (S (S (S (S n))) - 2 = S (S n)) by omega.
  intro. clear H0. unfold inv_ack.
  rewrite inv_ack_interstate_2 by omega.
  rewrite H. rewrite <- sub_add_distr. rewrite <- sub_add_distr.
  rewrite plus_comm. rewrite <- minus_2_correct in H.
  rewrite <- H, <- (next_level_interstate_2 minus_2 _);
    [trivial | apply minus_2_shrink | omega].
Qed.

Theorem inv_ack_helper_thm : forall i k n,
    3 <= n ->
    i + k + 4 <= inv_ack_hier (i + k) n <->
    S i <= inv_ack_helper k n.
Proof.
  intros i k n Hn. generalize dependent k.
  (** maybe make this a lemma? *)
  assert (forall k, k + 4 <= inv_ack_hier k n <-> 1 <= inv_ack_helper k n) as H0.
  { split.
    - intro. rewrite inv_ack_interstate_3; [omega | trivial].
    - unfold inv_ack_helper. intro. rewrite not_lt. rewrite plus_comm.
      simpl. rewrite lt_succ_r. intro.
      assert (inv_ack_hier k n - (k + 3) = 0) by omega.
      rewrite H1 in H; simpl in H; inversion H. }
  induction i; [apply H0|]. 
  intro. specialize (IHi (S k)).
  replace (i + S k) with (S i + k) in IHi by omega.
  split.
  - intro. assert (H1 := H). rewrite IHi in H.
    rewrite inv_ack_interstate_3; [omega|].
    apply (Nat.le_trans _ (inv_ack_hier (S i + k) n) _).
    + apply (Nat.le_trans _ (S i + k + 4) _); [omega | trivial].
    + apply inv_ack_hier_shrink_gen; [trivial | omega].
  - intro. rewrite IHi. rewrite inv_ack_interstate_3 in H;
                          [|rewrite H0]; omega.
Qed.

Theorem inv_ack_correct' : forall x n, (inv_ack n <= x <-> n <= Ack x x).
Proof.
  destruct n; [simpl; omega|]. 
  destruct n.
  - simpl. destruct x; [simpl; omega|].
    rewrite inv_ack_Ack. simpl. split.
    + intro. apply (Nat.le_trans _ (inv_ack_hier 0 3) _).
      * apply inv_ack_hier_shrink_gen; [trivial | omega].
      * simpl. omega.
    + intro. omega. 
  - rewrite inv_ack_interstate_4. destruct x. { simpl. omega. }
                                              rewrite <- le_S_n_m. rewrite inv_ack_Ack.
    rewrite not_lt. rewrite not_lt.
    rewrite <- le_succ_l. rewrite <- le_succ_l.
    replace x with (x + 0). replace (S (S (x + 0) + 2)) with (x + 0 + 4).
    rewrite (inv_ack_helper_thm x 0 _). rewrite (plus_comm _ 2). simpl.
    omega. omega. omega. omega. omega.
Qed.

Theorem inv_ack_correct : forall x n, (inv_ack n <= x <-> n <= Ack x x).
Proof.
  destruct n; [simpl; omega|]. 
  destruct n.
  - simpl. destruct x; [simpl; omega|].
    rewrite inv_ack_Ack. simpl. split.
    + intro. apply (Nat.le_trans _ (inv_ack_hier 0 3) _).
      * apply inv_ack_hier_shrink_gen; [trivial | omega].
      * simpl. omega.
    + intro. omega. 
  - rewrite inv_ack_interstate_4 by omega.
    destruct x; [simpl; omega |]. 
    rewrite <- le_S_n_m. rewrite inv_ack_Ack.
    repeat rewrite not_lt. rewrite <- le_succ_l, <- le_succ_l.
    replace x with (x + 0) by omega.
    replace (S (S (x + 0) + 2)) with (x + 0 + 4) by omega.
    rewrite (inv_ack_helper_thm x 0 _) by omega.
    rewrite (plus_comm _ 2). simpl; omega.
>>>>>>> ea3ab7244c9a81f06217436752a28ec6aacdf383
Qed.

Fixpoint sum_f (f : nat -> nat) (k n : nat) :=
  match k with
  | 0 => n
  | S k' => n + sum_f f k' (f n)
  end.

Definition HS n := match (inv_ack_hier 2), (inv_ack_hier 3 n) with
                   | f, m => m + sum_f f (m - 1) (f n) end.

Compute HS 5.
Compute HS 6.
Compute HS 9.
Compute HS 4.

Time Compute (inv_ack 10000).