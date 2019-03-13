(* Ackermann *)
Require Import Omega.
Require Import Setoid.

(* Some properties of relations on N *)
Definition total_rel {A B : Type} (r : A -> B -> Prop) : Prop :=
  forall a, exists b, r a b.

Definition functional_rel {A B : Type} (r : A -> B -> Prop) : Prop :=
  forall a b1 b2,
    r a b1 ->
    r a b2 ->
    b1 = b2.

Definition monotone_rel (r : nat -> nat -> Prop) : Prop :=
  forall n1 r1 n2 r2,
    r n1 r1 ->
    r n2 r2 ->
    n1 <= n2 ->
    r1 <= r2.

Definition increasing_rel (r : nat -> nat -> Prop) : Prop :=
  forall n1 r1 n2 r2,
    r n1 r1 ->
    r n2 r2 ->
    n1 < n2 ->
    r1 < r2.

Lemma increasing_monotone_rel: forall r,
  functional_rel r ->
  increasing_rel r ->
  monotone_rel r.
Proof.
  repeat intro.
  assert (n1 = n2 \/ n1 < n2) by omega.
  destruct H4.
  + subst n2. rewrite (H _ _ _ H1 H2). constructor.
  + apply Nat.lt_le_incl. eapply H0; eauto.
Qed.

Definition inverse_rel {A B : Type} (r : A -> B -> Prop) : B -> A -> Prop :=
  fun a b => r b a.

Lemma inverse_rel_monotone: forall r,
  increasing_rel r ->
  monotone_rel (inverse_rel r).
Proof.
  unfold inverse_rel. repeat intro.
  assert (r1 <= r2 \/ r2 < r1) by omega.
  destruct H3; auto.
  specialize (H _ _ _ _ H1 H0 H3).
  exfalso. omega.
Qed.

(* Some properties of functions with relations *)
Definition compute_rel {A B : Type} (r : A -> B -> Prop) (f : A -> B) : Prop :=
  forall a b, (r a b <-> f a = b).

Definition fun_rel {A B : Type} (f : A -> B) : A -> B -> Prop :=
  fun a b => f a = b.

Lemma fun_rel_compute: forall A B (r : A -> B -> Prop) (f : A -> B),
  compute_rel r f ->
  forall a b, fun_rel f a b <-> r a b.
Proof. unfold fun_rel, compute_rel. firstorder. Qed.

Lemma compute_fun_rel: forall A B (f : A -> B),
  compute_rel (fun_rel f) f.
Proof. unfold fun_rel, compute_rel. tauto. Qed.

Lemma compute_rel_total: forall A B (r : A -> B -> Prop) (f : A -> B),
  compute_rel r f ->
  total_rel r.
Proof.
  repeat intro. exists (f a).
  rewrite (H a (f a)). trivial.
Qed.

Lemma compute_rel_functional: forall A B (r : A -> B -> Prop) (f : A -> B),
  compute_rel r f ->
  functional_rel r.
Proof.
  repeat intro.
  rewrite (H a b1) in H0.
  rewrite (H a b2) in H1.
  congruence.
Qed.

Definition monotone (f : nat -> nat) : Prop :=
  forall n m,
    n <= m ->
    f n <= f m.

Definition increasing (f : nat -> nat) : Prop :=
  forall n m,
    n < m ->
    f n < f m.

(*
Lemma reflect_compute: forall A B (P : (A -> B -> Prop) -> Prop),
  forall r f,
    compute_rel r f ->
    P r ->
    P (fun_rel f).
(r : A -> B -> Prop)
*)

Lemma compute_rel_increasing: forall (r : nat -> nat -> Prop) (f : nat -> nat),
  compute_rel r f ->
  increasing_rel r <->
  increasing f.
Proof.
  split; repeat intro.
  + eapply H0; eauto;
    rewrite (H _ _); trivial.
  + rewrite (H _ _) in H1.
    rewrite (H _ _) in H2.
    rewrite <- H1. rewrite <- H2.
    apply H0. trivial.
Qed.

Lemma compute_rel_monotone: forall (r : nat -> nat -> Prop) (f : nat -> nat),
  compute_rel r f ->
  monotone_rel r <->
  monotone f.
Proof.
  split; repeat intro.
  + eapply H0; eauto;
    rewrite (H _ _); trivial.
  + rewrite (H _ _) in H1.
    rewrite (H _ _) in H2.
    rewrite <- H1. rewrite <- H2.
    apply H0. trivial.
Qed.

(* A little more abstract, but an interesting
   way to try.  Not obviously shorter, though. *)
Lemma increasing_monotone: forall (f : nat -> nat),
  increasing f ->
  monotone f.
Proof.
  intros.
  rewrite <- (compute_rel_monotone _ _ (compute_fun_rel _ _ _)).
  apply increasing_monotone_rel.
  eapply compute_rel_functional, compute_fun_rel.
  rewrite (compute_rel_increasing). apply H.
  apply compute_fun_rel.
Qed.

(* Ackermann's function/relation *)
Inductive Ackrel : nat -> nat -> nat -> Prop :=
  | Ackrel_0: forall n, Ackrel 0 n (1 + n)
  | Ackrel_S0: forall m' r, 
               Ackrel m' 1 r ->
               Ackrel (1 + m') 0 r
  | Ackrel_SS: forall m' n' r' r'',
               Ackrel (1 + m') n' r' ->
               Ackrel m' r' r'' ->
               Ackrel (1 + m') (1 + n') r''.

Fixpoint Ack (m n : nat) : nat :=
  match m with
   | 0 => 1 + n
   | S m' => let fix Ack' (n : nat) : nat :=
             match n with
              | 0 => Ack m' 1
              | S n' => Ack m' (Ack' n')
             end
             in Ack' n
  end.

Theorem Ackrel_Ack: forall m, compute_rel (Ackrel m) (Ack m).
Proof.
  split.
  + induction 1; subst; auto.
  + intro. subst b. revert a.
    induction m as [|m' IHm'].
    - constructor.
    - intro a. generalize dependent m'.
      induction a as [|n' IHn'];
      econstructor; eauto.
Qed.

Lemma Ackrel_increasing2S: forall m n r1 r2,
  Ackrel m n r1 ->
  Ackrel m (1 + n) r2 ->
  r1 < r2.
Proof.
  intros. inversion H0; subst.
  - inversion H. constructor.
  - rewrite (compute_rel_functional _ _ _ _ (Ackrel_Ack _) _ _ _ H H2).
    clear -H4. induction H4; omega.
Qed.

Lemma Ackrel_increasing2: forall m,
  increasing_rel (Ackrel m).
Proof.
  repeat intro.
  assert (n2 = 1 + (n2 - n1 - 1) + n1) by omega.
  revert H2. generalize (n2 - n1 - 1). intros j eq. 
  subst n2. rename n1 into n. clear H1. revert m n r1 r2 H H0.
  induction j.
  - apply Ackrel_increasing2S.
  - simpl. intros.
    apply lt_trans with (Ack m (1 + j + n)).
    + eapply IHj; eauto. apply Ackrel_Ack. trivial.
    + eapply Ackrel_increasing2S.
      * apply Ackrel_Ack; reflexivity.
      * apply H0.
Qed.

Lemma Ack_increasing2: forall m,
  increasing (Ack m).
Proof.
  repeat intro; eapply Ackrel_increasing2; eauto; apply Ackrel_Ack; reflexivity.
Qed.

(* This one is a real pain in the rear. *)
Lemma Ackrel_increasing1S: forall m n r1 r2,
  Ackrel m n r1 ->
  Ackrel (1 + m) n r2 ->
  r1 < r2.
Proof.
  induction m.
  + rewrite plus_0_r.
    intros. inversion H. subst. clear H.
    generalize dependent r2. induction n; intros.
    - inversion H0. inversion H1. constructor.
    - inversion H0. subst. specialize (IHn _ H2).
      inversion H3; subst. clear H3. omega.
  + induction n; intros.
    - inversion H. inversion H0. subst.
      eapply IHm; eauto.
    - inversion H. inversion H0. subst.
      clear H H0.
      apply lt_trans with (Ack (S m) r').
      eapply IHm; eauto. apply Ackrel_Ack. trivial.
      eapply Ackrel_increasing2; eauto. apply Ackrel_Ack. trivial.
Qed.

Lemma Ackrel_increasing1: forall n,
  increasing_rel (fun m => Ackrel m n).
Proof.
  repeat intro. rename n into m.
  assert (n2 = 1 + (n2 - n1 - 1) + n1) by omega.
  revert H2. generalize (n2 - n1 - 1). intros j eq.
  subst n2. rename n1 into n. clear H1. revert m n r1 r2 H H0.
  induction j.
  - intros. eapply Ackrel_increasing1S; eauto.
  - simpl. intros.
    apply lt_trans with (Ack (1 + j + n) m).
    + eapply IHj; eauto. apply Ackrel_Ack. trivial.
    + eapply Ackrel_increasing1S.
      * apply Ackrel_Ack; reflexivity.
      * apply H0.
Qed.

Lemma Ack_increasing1: forall n,
  increasing (fun m => Ack m n).
Proof.
  repeat intro; eapply Ackrel_increasing1; eauto; apply Ackrel_Ack; reflexivity.
Qed.

Definition Arel (n r : nat) : Prop :=
  Ackrel n n r.

Definition A (n : nat) : nat :=
  Ack n n.

Theorem Arel_A: compute_rel Arel A.
Proof. repeat intro. apply Ackrel_Ack. Qed.

Lemma Arel_increasing:
  increasing_rel Arel.
Proof.
  repeat intro. apply lt_trans with (Ack n1 n2).
  eapply Ackrel_increasing2; eauto. apply Ackrel_Ack; trivial.
  eapply Ackrel_increasing1; eauto. apply Ackrel_Ack; trivial.
Qed.

Lemma A_increasing:
  increasing A.
Proof. repeat intro. eapply Arel_increasing; eauto; apply Arel_A; trivial. Qed.

Compute A 0.
Compute A 1.
Compute A 2.
Compute A 3.
(* I'll stop here with my unit tests. *)

(*
Definition Ackrel_inv (m n r : nat) : Prop :=
  Ack m n <= 
*)

Definition Ainvrel (n r : nat) : Prop :=
  (n = 0 /\ r = 0) \/
  (A r <= n < A (1 + r)).

Lemma Ainvrel_A: forall n,
  Ainvrel (A n) n.
Proof.
  right. split. apply le_n. apply A_increasing. omega.
Qed.

Lemma A_positive: forall n,
  0 < A n.
Proof.
  induction n. compute. omega.
  apply lt_trans with (A n). auto.
  apply A_increasing. auto.
Qed.

Lemma Ainvrel_total:
  total_rel Ainvrel.
Proof.
  red. induction a as [|n' [r' [IHn' | [Hr1 Hr2]]]].
  + exists 0. left. auto.
  + exists 0. right. compute. omega.
  + destruct n' as [|n'].
    exists 0. compute. omega. 
    assert (S (S n') < A (1 + r') \/
            S (S n') = A (1 + r')) by omega.
    destruct H.
    * exists r'. right. split; omega.
    * exists (1 + r'). right. split. omega.
      rewrite H. apply A_increasing. omega.
Qed.

Lemma A_inv_functional: 
  functional_rel Ainvrel.
Proof.
  intros n r r' [[H1 H2] | [Ha Hb]] [[H3 H4] | [Hc Hd]]; subst; auto.
  + exfalso. generalize (A_positive r'). omega.
  + exfalso. generalize (A_positive r). omega.
  + assert (r = r' \/ 
            r' = 1 + r \/ r = 1 + r' \/ 
            r' > 1 + r \/ r > 1 + r') by omega.
    destruct H; auto. exfalso.
    destruct H as [H | [H | [H | H]]]; subst; try omega.
    - assert (A (1 + r) < A r') by (apply A_increasing, H). omega.
    - assert (A (1 + r') < A r) by (apply A_increasing, H). omega.
Qed.

Lemma Ainvrel_monotone: 
  monotone_rel Ainvrel.
Proof.
  intros n r n' r' [[Ha Hb] | H] [[Hc Hd] | H']; subst; try omega; intro.
  + exfalso. generalize (A_positive r). omega.
  + assert (r <= r' \/ r' < r) by omega.
    destruct H1; auto; exfalso.
    assert (r = 1 + r' \/ 1 + r' < r) by omega. destruct H2.
    - subst. omega.
    - assert (A (1 + r') < A r) by (apply A_increasing; auto).
      omega.
Qed.

Example Ainvrel1: Ainvrel 7 2.
Proof. red. unfold A. simpl. omega. Qed.

Example Ainvrel2: Ainvrel 10 2.
Proof. red. unfold A. simpl. omega. Qed.

Example Ainvrel3: Ainvrel 60 2.
Proof. red. unfold A. simpl. omega. Qed.

Example Ainvrel4: Ainvrel 61 3.
Proof.
  right. split. 
  - constructor.
  - change 61 with (A 3).
    apply A_increasing.
    constructor.
Qed.

Example Ainvrel5: Ainvrel 100 3.
Proof.
  right. split.
  - compute. omega.
  - admit. (* Of course true, but how can
              we prove it in reasonable time? *)
Abort.


Definition smooth_rel (r : nat -> nat -> Prop) : Prop :=
  forall a b b',
    r a b ->
    r (1 + a) b' ->
    b = b' \/ b' = 1 + b.

(* Inverse Ackermann Hierarchy *)

Inductive InvAckHier : nat -> nat -> nat -> Prop :=
  | IAH_base: forall n r, 
              n = r + r \/ n + 1 = r + r ->
              InvAckHier 0 n r
  | IAH_succ: forall l' n n' r',
              InvAckHier l' n n' ->
              (n' = 1) \/ (InvAckHier (S l') n' r') ->
              InvAckHier (S l') n (S r').

Theorem IAHT: forall n m r,
  n > 0 ->
  Ackrel n m r ->
  InvAckHier r m n.
Proof.
  induction n; intros. inversion H.
  clear H.
  destruct r.
  exfalso.
  assert (m + 1 < 0). { eapply Ackrel_increasing1.
    2: apply H0. rewrite plus_comm. constructor. omega. }
  omega.
  inversion H0; subst;
econstructor.
apply IHn in H1. 2: admit.
inversion H1; subst. Abort.

(*
econstructor.

; econstructor.
  

  inversion H0. subst.
  
  inversion H. subst.
*)
Definition InvA (n r : nat) : Prop :=
  (exists x, InvAckHier r n x /\ x <= 3) /\ 
  (forall y, InvAckHier (r - 1) n y -> y > 3).


(* DivFC *)

Definition euclid_S (et : nat * nat * nat) : nat * nat * nat :=
  match et with
    | (n, m, 0) => (S n, 0, m)
    | (n, m, S c) => (n, S m, c)
  end.

Fixpoint div_helper (n : nat) (et : nat * nat * nat) : nat * nat * nat :=
  match n with
   | 0 => et
   | S n' => div_helper n' (euclid_S et)
  end.

Definition divf (n m : nat) : nat * nat :=
  match m with
   | 0 => (0,0)
   | S m' => match div_helper n (0,0,m') with
             (d,r,_) => (d,r)
             end
  end.

Definition divc (n m : nat) : nat * nat :=
  match m with
   | 0 => (0,0)
   | S m' => match div_helper n (0,0,m') with
             | (d,0,_) => (d,0)
             | (d,r,_) => (1 + d, m - r)
             end
  end.



Lemma IAHB: forall n,
  InvAckHier 0 n (fst (divc n 2)).
Proof.
Admitted.

(* Definition InvA (n r : nat) : Prop := *)
(*   (exists x, InvAckHier r n x /\ x <= 3) /\  *)
(*   (forall y, InvAckHier (r - 1) n y -> y > 3). *)

Compute (A 3).

(*
Goal InvA 55 3.
  split. exists 3. split; auto.
  { econstructor. instantiate (1 := 3).
    * econstructor. instantiate (1 := 6).
        - econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
        - right. econstructor. instantiate (1 := 3).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
          right. econstructor. instantiate (1 := 2).
          apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
        - 
      + econstructor. instantiate (1 := 6).
        - econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
        - right. econstructor. instantiate (1 := 3).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
          right.
          econstructor. instantiate (1 := 2). 
          econstructor. apply IAHB. 
          right. econstructor. apply IAHB.
          auto.
          right.
          econstructor. instantiate (1 := 1).
          econstructor. apply IAHB. auto.
          auto.
      + right. econstructor. instantiate (1 := 3).
        - econstructor. instantiate (1 :=  3).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.

*)

Goal InvA 60 4.
Proof.
  split. exists 3. split; auto.
  { econstructor. instantiate (1 := 4).
    * econstructor. instantiate (1 := 5).
      + econstructor. instantiate (1 := 6).
        - econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
        - right. econstructor. instantiate (1 := 3).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
          right.
          econstructor. instantiate (1 := 2). 
          econstructor. apply IAHB. 
          right. econstructor. apply IAHB.
          auto.
          right.
          econstructor. instantiate (1 := 1).
          econstructor. apply IAHB. auto.
          auto.
      + right. econstructor. instantiate (1 := 3).
        - econstructor. instantiate (1 :=  3).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
          right. econstructor. instantiate (1 := 2).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
          right. econstructor. instantiate (1 := 1).
          econstructor. apply IAHB.
          auto.
          auto.
        - right. econstructor. instantiate (1 := 2).
          econstructor. instantiate (1 := 2).
          econstructor. apply IAHB.
          right. econstructor. apply IAHB.
          auto.
          right. econstructor. instantiate (1 := 1).
          econstructor. apply IAHB.
          auto. auto.
          right. econstructor. instantiate (1 := 1).
          econstructor. instantiate (1 := 1).
          econstructor. apply IAHB.
          auto. auto. auto.
    * right. econstructor. instantiate (1 := 2).
      + econstructor. instantiate (1 := 2).
        - econstructor. instantiate (1 := 2). 
          econstructor. apply IAHB.
          right. econstructor. apply IAHB. auto.
          right. econstructor. instantiate (1 := 1).
          econstructor. apply IAHB. auto. auto.
        - right. econstructor. instantiate (1 := 1).
          econstructor. instantiate (1 := 1).
          econstructor. apply IAHB. auto. auto. auto.
      + right. econstructor. instantiate (1 := 1).
        econstructor. instantiate (1 := 1).
        econstructor. instantiate (1 := 1).
        econstructor. instantiate (1 := 1).
        apply IAHB. auto. auto. auto. auto. }
  { intros [|[|[|[|y']]]]; simpl. 5: omega.
    + inversion 1.
    + inversion 1. subst. destruct H4.
      subst. inversion H2. subst.
      destruct H5. subst. inversion H3.
      destruct H6. subst. inversion H4.
      exfalso. omega. subst. inversion H6.
      inversion H0.
      inversion H0.
    + inversion 1. subst. destruct H4.
      subst. inversion H2. subst.
      destruct H5. subst. inversion H3.
      destruct H6. subst. inversion H4.
      exfalso. omega. subst. inversion H6.
      inversion H0.
      inversion H0. subst.
      destruct H6. subst. inversion H4.
      destruct H7; subst.
      inversion H5. destruct H8; subst.
      inversion H6. subst. destruct H1; subst.
      inversion H2. destruct H9; subst.
      inversion H7. destruct H10; subst.
      inversion H8. exfalso. omega.
      inversion H10.
      inversion H9. destruct H11; subst.
      inversion H8. destruct H12; subst.
      inversion H10. destruct H1; subst.
      inversion H7. inversion H11. assert (n' = 30) by omega. subst.
      destruct H13. inversion H1.
      inversion H1. destruct H16; subst.
      inversion H13. exfalso. omega.
      inversion H16. assert (n' = 1) by omega. subst.
      inversion H7. inversion H12.
      destruct H14; subst. exfalso. omega.
      inversion H14. inversion H12.
      inversion H11.
      assert (n' = 1) by omega. subst.
      inversion H2. destruct H10. 2: inversion H10.
      subst. inversion H8.
      destruct H11. 2: inversion H11. subst.
      inversion H9. exfalso. omega.
      inversion H8. inversion H7. inversion H1.
    + inversion 1; exfalso; subst.
      admit.
Abort.


(*
 inversion H10.
      inversion H10.
    + 
2: discriminate.

    econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    auto.
    right. econstructor. instantiate (1 := 3).
    econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    auto.
    right.

 econstructor. instantiate (1 := 2).
    econstructor. apply IAHB. simpl.
    right. econstructor. apply IAHB. simpl.
    auto.
    right. 



 apply IAHB.





 simpl. instantiate (1 := 5).



 induction 1.
*)
Goal InvAckHier 1 9 4.
econstructor. apply IAH_base. instantiate (1 := 5). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 3). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
Qed.

Goal InvAckHier 1 33 6.
econstructor. apply IAH_base. instantiate (1 := 17). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 9). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 5). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 3). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
Qed.

Lemma invfact: InvAckHier 1 3 2.
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
Qed.

Lemma invfact0: InvAckHier 1 6 3.
econstructor. apply IAH_base. instantiate (1 := 3). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
Qed.

Lemma invfact1: InvAckHier 1 64 6.
econstructor. apply IAH_base. instantiate (1 := 32). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 16). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 8). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 4). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
Qed.

Goal InvAckHier 2 64 4.
econstructor. apply invfact1.
right. econstructor. apply invfact0.
right. econstructor. apply invfact.
right. econstructor. 2: left; reflexivity.
econstructor. 2: left; reflexivity.
econstructor. auto.
Qed.

Goal InvAckHier 2 17 4.
econstructor. instantiate (1 := 5).
econstructor. econstructor. instantiate (1 := 9). auto.
right. econstructor. econstructor. instantiate (1 := 5). auto.
right. econstructor. econstructor. instantiate (1 := 3). auto.
right. econstructor. econstructor. instantiate (1 := 2). auto.
right. econstructor. econstructor. instantiate (1 := 1). auto.
auto.
right. econstructor. instantiate (1 := 3).
econstructor. econstructor. instantiate (1 := 3). auto.
right. econstructor. econstructor. instantiate (1 := 2). auto.
right. econstructor. econstructor. instantiate (1 := 1). auto.
auto.
right. econstructor. instantiate (1 := 2).
econstructor. econstructor. instantiate (1 := 2). auto.
right. econstructor. econstructor. instantiate (1 := 1). auto.
auto.
right. econstructor. instantiate (1 := 1).
econstructor. econstructor. instantiate (1 := 1). auto.
auto.
auto.
Qed.

Goal InvAckHier 2 16 3.
econstructor. instantiate (1 := 4).
econstructor. econstructor. instantiate (1 := 8). auto.
right. econstructor. econstructor. instantiate (1 := 4). auto.
right. econstructor. econstructor. instantiate (1 := 2). auto.
right. econstructor. econstructor. instantiate (1 := 1). auto.
auto.
right. econstructor. instantiate (1 := 2).
econstructor. econstructor. instantiate (1 := 2). auto.
right. econstructor. econstructor. instantiate (1 := 1). auto.
auto.
right. econstructor. instantiate (1 := 1).
econstructor. econstructor. instantiate (1 := 1). auto.
auto.
auto.
Qed.



(* right. econstructor. econstructor. instantiate (1 := 1). auto. *)
(* auto. *)








(*  apply invfact1. *)
(* right. econstructor. apply invfact0. *)
(* right. econstructor. apply invfact. *)
(* right. econstructor. 2: left; reflexivity. *)
(* econstructor. 2: left; reflexivity. *)
(* econstructor. auto. *)

(*
 instantiate (1 := 3).
econstructor. 
 apply IAH_base. instantiate (1 := 3). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
right.
econstructor. instantiate (1 := 1).
econstructor. apply IAH_base. instantiate (1 := 2). auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.
right.
econstructor. apply IAH_base. instantiate (1 := 1). auto.
auto.

Qed.
*)


Lemma Ainvrel_smooth:
  smooth_rel Ainvrel.
Proof.
  red. induction a; intros b b' [[Ha Hb] | [H1 H2]] [[Hc Hd] | [H3 H4]]; subst; simpl in *; try discriminate; auto.
  + destruct b' as [| [| b'']]; auto.
    assert (A 1 < A (S (S b''))) by (apply A_increasing; omega).
    change (A 1) with 3 in H. exfalso. omega.
  + exfalso. generalize (A_positive b). omega.
  + admit.
Abort.
 (*    assert ((S a < A (S b')) \/ (S a =  *)

 (* assert (A b' <= S a \/ A b' = S (S a)) by omega. *)
 (*    destruct H.  *)






Definition inverse_rel_alt (r : nat -> nat -> Prop) : nat -> nat -> Prop :=
  fun a b => forall y y',
    r b y -> 
    r (1 + b) y' ->
    y <= a < y'.

Lemma inverse_rel_equiv_inverse_rel_alt: 
  forall r,
    total_rel r ->
    smooth_rel (inverse_rel r) ->
    functional_rel r ->
    increasing_rel r ->
      forall a b,
        inverse_rel r a b <-> inverse_rel_alt r a b.
Proof. Abort.
(*
  unfold inverse_rel.
  split; repeat intro.
  + specialize (H1 _ _ _ H3 H4). subst y.
    specialize (H2 _ _ _ _ H4 H5).
    split; omega.
  + destruct (H b) as [a1 Ha1].
    destruct (H (1 + b)) as [a2 Ha2].
    specialize (H0 b a1 a2 Ha1 Ha2).
    specialize (H3 _ _ Ha1 Ha2).


 destruct H1.
*)
Lemma Ackrel_total: forall m, total_rel (Ackrel m).
Proof.
  induction m as [|m' IHm']. intro n. exists (1 + n). apply Ackrel_0.
  intros n. generalize dependent m'.
  induction n as [|n' IHn'].
  - intros. destruct (IHm' 1) as [r ?]. exists r. apply Ackrel_S0. apply H.
  - intros. specialize (IHn' m' IHm').
    destruct IHn' as [r Hr].
    destruct (IHm' r) as [r' Hr'].
    exists r'.
    apply Ackrel_SS with r.
    apply Hr.
    apply Hr'.
Qed.

Lemma Ackrel_functional: forall m, functional_rel (Ackrel m).
Proof.
  intros m n r r' H. revert r'.
  induction H; intros.
  - inversion H. trivial.
  - inversion H0. subst. eauto.
  - inversion H1. subst.
    specialize (IHAckrel1 _ H4). subst r'1.
    auto.
Qed.


Lemma Ackrel_Ack': forall m n,
  Ackrel m n (Ack m n).
Proof.
  induction m.
  - simpl. apply Ackrel_0.
  - intro n. generalize dependent m.
    induction n as [|n' IHn']; intros.
    + simpl. apply Ackrel_S0. apply IHm.
    + eapply Ackrel_SS. apply IHn'. apply IHm.
      apply IHm.
Qed.

Lemma Ackrel_inv3: forall m n r,
  Ackrel m n r ->
  r = Ack m n.
Proof. induction 1; subst; auto. Qed.

Lemma Ackrel_total_alt: forall m n, exists r,
  Ackrel m n r.
Proof. intros m n. exists (Ack m n). now apply Ackrel_Ack. Qed.

Lemma Ackrel_functional_alt: forall m n r r',
  Ackrel m n r ->
  Ackrel m n r' ->
  r = r'.
Proof. intros. apply Ackrel_inv3 in H. apply Ackrel_inv3 in H0. congruence. Qed.
