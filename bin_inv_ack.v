Require Import BinNat.
Require Import Omega.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Program.Basics.
Require Import Nnat.
Require Import bin_prelims.
Require Import bin_repeater.
Require Import bin_countdown.

Require inverse.
Require inv_ack.


(* f is the upper inverse of F: f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : N -> N) : Prop :=
    forall n m, f m <= n <-> m <= F n.

(* This version for N correctly mirrors its nat counterpart *)
Theorem upp_inv_rel_correct : forall f F,
    upp_inv_rel f F <-> inverse.upp_inv_rel (to_nat_func f) (to_nat_func F).
Proof.
  intros f F. unfold upp_inv_rel. unfold inverse.upp_inv_rel.
  unfold to_nat_func. split; intros H n m.
  - repeat rewrite le_nat_N. repeat rewrite N2Nat.id. apply H.
  - specialize (H (N.to_nat n) (N.to_nat m)). repeat rewrite le_nat_N in H.
    repeat rewrite N2Nat.id in H. apply H.
Qed.

(* Translation of the upper inverse computation from nat to N *)
Definition upp_inv (F : N -> N) : N -> N := to_N_func (inverse.upp_inv (to_nat_func F)).

Theorem upp_inv_correct :
    forall F, increasing F -> upp_inv_rel (upp_inv F) F.
Proof.
  intros F HF n m. unfold upp_inv. unfold to_N_func.
  rewrite le_N_nat, Nat2N.id. rewrite to_nat_func_incr in HF.
  apply inverse.upp_inv_correct in HF. rewrite (HF _ _).
  unfold to_nat_func. rewrite N2Nat.id. symmetry. apply le_N_nat.
Qed.

Lemma to_nat_diag_ack :
    (fun n => repeater.ackermann n n) = to_nat_func (fun n : N => ackermann n n).
Proof.
  apply functional_extensionality. unfold to_nat_func. intro n.
  rewrite ackermann_correct. repeat rewrite Nat2N.id. trivial.
Qed.

(* Diagonal Strict Increasing *)
Lemma diag_ack_incr : increasing (fun n => ackermann n n).
Proof.
  rewrite to_nat_func_incr. rewrite <- to_nat_diag_ack. apply inv_ack.diag_ack_incr.
Qed.


(* *********** INVERSE ACKERMANN HIERARCHY ******************* *)

(* Definition *)
Fixpoint alpha (m : nat) (x : N) : N :=
  match m with
  | 0%nat => x - 1
  | 1%nat => x - 2
  | 2%nat => N.div2 (x - 2)
  | S m'  => countdown (alpha m') 1 (alpha m' x)
  end.

(* Recursion *)
Theorem alpha_recursion : forall m, (2 <= m)%nat ->
    alpha (S m) = compose (countdown (alpha m) 1) (alpha m).
Proof. destruct m as [|[|m]]; [omega|omega|trivial]. Qed.


(* ******* CORRECTNESS OF INVERSE ACKERMANN HIERARCHY ************** *)

(* Countdown composed with self preserves binary contractiveness *)
Theorem countdown_bin_contract : forall f a b,
    bin_contract_strict_above a f -> bin_contract_strict_above b (compose (countdown f a) f).
Proof.
  intros f a b Haf0. assert (H:=Haf0). destruct H as [Hf Haf].
  split; intro n; [ |intro Hbn]; unfold compose;
  rewrite countdown_repeat by assumption; rewrite <- repeat_S_comm;
  rewrite N.le_ngt; intro; apply (repeat_bin_contract_strict _ _ _ _ Haf0) in H.
  - specialize (nat_size_contract n). omega.
  - replace (nat_size n) with (S (nat_size (N.div2 n))) in H.
    + specialize (nat_size_contract (N.div2 n)). omega.
    + destruct n; [contradict Hbn; lia|induction p; trivial].
Qed.

Lemma alpha_2_correct : forall n,
    alpha 2 n = N.of_nat (inv_ack.alpha 2 (N.to_nat n)).
Proof.
  intro n. unfold alpha. unfold to_N_func. remember (N.to_nat n) as m.
  replace (n - 2) with (N.of_nat (m - 2)) by lia.
  rewrite <- Nat2N.inj_div2. f_equal. clear Heqm. clear n.
  replace (inv_ack.alpha 2 m) with
   (countdown.countdown_to 1 (inv_ack.alpha 1) (inv_ack.alpha 1 m)) by trivial.
  rewrite inv_ack.alpha_1. generalize (m - 2)%nat. clear m. intro n.
  assert (Nat.div2 n = countdown.countdown_to 1 (fun n0 : nat => (n0 - 2)%nat) n
   /\ Nat.div2 (S n) = countdown.countdown_to 1 (fun n0 : nat => (n0 - 2)%nat) (S n)).
  { induction n; split; trivial. apply IHn.
    destruct (countdown.countdown_recursion 1 (fun n0 => (n0-2)%nat) (S(S n))) as [_ H].
    - split; intro m; omega.
    - rewrite H by omega. replace (S(S n) - 2)%nat with n by omega.
      simpl. f_equal. apply IHn. }
  apply H.
Qed.

(* Every alpha level starting from 2 is strictly binary contracting above 1,
   so countdown to 1 works properly for them *)
Theorem alpha_contract_strict_above_1 : forall m,
    (2 <= m)%nat -> bin_contract_strict_above 1 (alpha m).
Proof.
  destruct m as [|[|m]]; try omega; intro; clear H. induction m.
  - split; intro n; simpl; rewrite le_N_nat; repeat rewrite N2Nat.inj_div2;
    rewrite N2Nat.inj_sub; replace (N.to_nat 2) with 2%nat by trivial;
    remember (N.to_nat n) as m; clear Heqm; [|intro; clear H n].
    + apply Nat.div2_decr. omega.
    + repeat rewrite Nat.div2_div. apply Nat.div_le_mono; omega.
  - rewrite alpha_recursion; [|omega]. apply (countdown_bin_contract _ _ _ IHm).
Qed.

Theorem alpha_correct :
    forall m, alpha m = to_N_func (inv_ack.alpha m).
Proof.
  induction m as [|[|[|m]]]; apply functional_extensionality;
  intro n; unfold to_N_func. 2: rewrite inv_ack.alpha_1.
  1,2: simpl; lia. 1: apply alpha_2_correct.
  rewrite alpha_recursion by omega. unfold compose.
  rewrite countdown_correct by (apply alpha_contract_strict_above_1; omega).
  rewrite IHm. rewrite <- nat_N_func_id.
  replace (N.to_nat 1) with 1%nat by trivial.
  unfold to_N_func. f_equal. rewrite Nat2N.id. trivial.
Qed.

Corollary alpha_ackermann :
    forall m, upp_inv_rel (alpha m) (ackermann (N.of_nat m)).
Proof.
  intros m n p. rewrite <- (N2Nat.id n). rewrite ackermann_correct.
  rewrite alpha_correct. unfold to_N_func. rewrite <- le_nat_N.
  rewrite le_N_nat. repeat rewrite Nat2N.id.
  destruct (inv_ack.alpha_correct m) as [_ H]. apply H.
Qed.

(* *********** INVERSE ACKERMANN FUNCTION ******************** *)

Fixpoint inv_ack_worker (f : N -> N) (n k : N) (bud : nat) : N :=
  match bud with
  | 0%nat  => k
  | S bud' =>
    if n <=? k then k
      else let g := (countdown f 1) in
      inv_ack_worker (compose g f) (g n) (N.succ k) bud'
  end.

(* Definition by hard-coding the second alpha level, runtime O(n) *)
Definition inv_ack n :=
  if (n <=? 1) then 0
  else if (n <=? 3) then 1
  else let f := (alpha 2) in
        inv_ack_worker f (f n) 2 (nat_size n).

(* Intermediate lemmas about inv_ack_worker *)
Lemma alpha_contr : forall i n,
    (S i < N.to_nat (alpha (S i) n))%nat -> (i < N.to_nat (alpha i n))%nat.
Proof.
  intros i n. specialize (alpha_ackermann i (N.of_nat i) n).
  specialize (alpha_ackermann (S i) (N.of_nat (S i)) n).
  specialize (diag_ack_incr (N.of_nat i) (N.of_nat (S i))). lia.
Qed.

Lemma inv_ack_worker_intermediate : forall i n b,
    (S i < N.to_nat (alpha (S i) n))%nat -> (S i < b)%nat ->
      inv_ack_worker (alpha 2) (alpha 2 n) 2 b
       = inv_ack_worker (alpha (S (S i))) (alpha (S (S i)) n) (N.of_nat (S (S i))) (b - i).
Proof.
  induction i; intros n b Hn Hib; symmetry;
  [f_equal; omega|rewrite alpha_recursion by omega].
  rewrite IHi; [replace (b - i)%nat with (S (b - S i))%nat by omega
    |apply (alpha_contr _ _ Hn)|omega].
  rewrite lt_nat_N, N2Nat.id in Hn. rewrite <- N.leb_gt in Hn.
  unfold inv_ack_worker at 2. rewrite Hn. rewrite <- Nat2N.inj_succ. trivial.
Qed.

(* Proof that inv_ack_worker is correct given sufficient budget *)
Lemma inv_ack_worker_sufficient :
    forall n b, (4 <= n <= ackermann b b) ->
     inv_ack_worker (alpha 2) (alpha 2 n) 2 (N.to_nat b)
      = upp_inv (fun m => ackermann m m) n.
Proof.
  assert (Hincr := diag_ack_incr). assert (Hack := upp_inv_correct _ Hincr).
  unfold upp_inv_rel in Hack. intros n b [Hn Hnb].
  remember (N.to_nat (upp_inv (fun m : N => ackermann m m) n)) as p.
  rewrite <- (Nat2N.id p) in Heqp. apply N2Nat.inj in Heqp.
  assert (n <= ackermann (N.of_nat p) (N.of_nat p)) as Hp0 by (apply Hack; lia).
  destruct p as [|[|p]].
  1,2 : unfold N.of_nat in Heqp; unfold ackermann in Hp0; simpl in Hp0; lia.
  assert (ackermann (N.of_nat (S p)) (N.of_nat (S p)) < n) as Hp1
   by (rewrite N.lt_nge; rewrite <- Hack; lia).
  assert (S p < N.to_nat b)%nat as Hpb. { rewrite Nat.lt_nge. intro Hc.
  inversion Hc as [Hc0|Hc1]. rewrite <- Hc0 in Hp1. rewrite N2Nat.id in Hp1. lia.
  rewrite prelims.lt_S_le, lt_nat_N, N2Nat.id in H. apply Hincr in H. lia. }
  rewrite (inv_ack_worker_intermediate p).
  - replace (N.to_nat b - p)%nat with (S (N.to_nat b - S p))%nat by omega.
    unfold inv_ack_worker.
    replace (alpha (S (S p)) n <=? N.of_nat (S (S p))) with true; trivial.
    symmetry. rewrite N.leb_le.  rewrite (alpha_ackermann (S (S p)) _ _). apply Hp0.
  - rewrite lt_nat_N. rewrite N2Nat.id. rewrite N.lt_nge.
    rewrite (alpha_ackermann (S p) _ _). lia.
  - apply Hpb.
Qed.

(* Helper lemmas regarding ackermann at level 3 *)
Open Scope nat_scope.

Lemma ack_2 : forall n, repeater.ackermann 2 n = 2 * n + 3.
Proof.
  induction n; trivial. replace (repeater.ackermann 2 (S n)) with
    (repeater.ackermann 1 (repeater.ackermann 2 n)) by trivial.
  rewrite IHn. rewrite inv_ack.ack_1. omega.
Qed.

Lemma ack_3 : forall n, repeater.ackermann 3 n = 2 ^ (n + 3) - 3.
Proof.
  induction n; trivial. replace (repeater.ackermann 3 (S n)) with
    (repeater.ackermann 2 (repeater.ackermann 3 n)) by trivial.
  rewrite IHn. rewrite ack_2. replace (S n + 3) with (S (n + 3)) by trivial.
  replace (2 ^ (S (n+3))) with (2 * 2 ^ (n+3)) by trivial.
  assert (3 <= 2 ^ (n+3)). { apply (Nat.le_trans _ (2^3) _); [simpl; omega|].
    apply Nat.pow_le_mono_r; omega. } omega.
Qed.

Close Scope nat_scope.

(* Proof that inv_ack is correct *)
Theorem inv_ack_correct : inv_ack = to_N_func (inv_ack.inv_ack).
Proof.
  apply functional_extensionality. intro n.
  assert (n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ 4 <= n) as Hn by lia.
  repeat destruct Hn as [Hn|Hn]; try rewrite Hn; trivial.
  unfold inv_ack. replace (n <=? 1) with false by (symmetry; rewrite N.leb_gt; lia).
  replace (n <=? 3) with false by (symmetry; rewrite N.leb_gt; lia).
  rewrite <- (Nat2N.id (nat_size n)). rewrite inv_ack_worker_sufficient.
  - unfold upp_inv. f_equal. rewrite <- to_nat_diag_ack. symmetry.
    apply inverse.upp_inv_unique. apply inv_ack.diag_ack_incr.
    apply inv_ack.inv_ack_correct.
  - split; trivial. rewrite ackermann_correct. rewrite Nat2N.id.
    apply (N.le_trans _ (N.of_nat (repeater.ackermann 3 (nat_size n))) _).
    + clear Hn. rewrite le_N_nat. rewrite Nat2N.id.
      rewrite ack_3. destruct n; simpl; [lia|].
      induction p; [| |simpl; lia]; simpl;
      [rewrite Pos2Nat.inj_xI|rewrite Pos2Nat.inj_xO];
      assert (3 <= 2 ^ ((fix nat_pos_size (x : positive) : nat :=
       match x with
       | (y~1)%positive | (y~0)%positive => S (nat_pos_size y)
       | 1%positive => 1
       end) p + 3))%nat
       by (apply (Nat.le_trans _ (2^3) _); [simpl; omega|];
         apply Nat.pow_le_mono_r; omega); omega.
    + rewrite <- le_nat_N. rewrite Nat.le_ngt.
      assert (H := inv_ack.ack_incr_by_lvl (nat_size n)).
      apply (increasing_expanding.incr_twoways _ (nat_size n) 3) in H.
      simpl in *. rewrite <- H. apply nat_size_incr in Hn. simpl in Hn. omega.
Qed.