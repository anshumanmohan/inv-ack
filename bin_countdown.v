Require Import BinNat.
Require Import Omega.
Require Import Logic.FunctionalExtensionality.
Require Import Program.Basics.
Require Import micromega.Lia.
Require Import Nnat.
Require Import bin_prelims.

Require countdown.

Open Scope N_scope.

(* ****** CONTRACTIONS ****************** *)

Definition contracting (f : N -> N) : Prop :=
  forall n, f n <= n.

Definition bin_contract_strict_above (a : N) (f : N -> N) : Prop :=
  (contracting f) /\ (forall n, a < n -> f n <= N.div2 n).

(* TODO: CONVERT THIS TO BINARY
(* Upper inverse of strict from a expansions contract above a *)
Theorem upp_inv_expand_contract_strict :
    forall a f F, expand_strict_from a F -> upp_inv_rel f F -> contract_strict_above a f.
Proof.
  intros a f F HF HfF. destruct HF as [HF HaF].
  split.
  - apply (upp_inv_expand_contract _ F); assumption.
  - intro n. destruct n; [omega|]. repeat rewrite <- le_S_n_m.
    rewrite (HfF n _). apply HaF.
Qed.
*)

(* ****** PROPERTIES OF CONTRACTIONS ************ *)

(* Correct counterpart of contractions on nat *)
Lemma contract_Nnat : forall f,
    contracting f <-> countdown.contracting (to_nat_func f).
Proof.
  intro f. unfold to_nat_func. split; intros H n.
  - rewrite le_nat_N. rewrite N2Nat.id. apply H.
  - specialize (H (N.to_nat n)). simpl in H. rewrite le_nat_N in H.
    repeat rewrite N2Nat.id in H. apply H.
Qed.

(* strict binary contractions are strict contractions on nat *)
Lemma bin_contract_strict_Nnat : forall a f,
   bin_contract_strict_above a f -> countdown.contract_strict_above (N.to_nat a) (to_nat_func f).
Proof.
  intros a f [Hf Haf]. split.
  - rewrite <- contract_Nnat. apply Hf.
  - intros n. unfold to_nat_func. repeat rewrite le_nat_N.
    repeat rewrite Nat2N.inj_succ. repeat rewrite N2Nat.id.
    intro Han. rewrite N.le_succ_l. apply (N.le_lt_trans _ (N.div2 (N.of_nat n)) _).
    + apply Haf. lia.
    + apply div2_contr; lia.
Qed.

(* repeat of contractions make the result smaller *)
Lemma repeat_contract :
  forall f n k l,
    contracting f -> (k <= l)%nat -> repeat f l n <= repeat f k n.
Proof.
  intros f n k l Hf Hkl.
  induction l; inversion Hkl; [lia |lia |].
  apply IHl in H0.
  apply (N.le_trans _ (repeat f l n) _); [apply Hf | apply H0].
Qed.

(* strict version *)
Lemma repeat_bin_contract_strict :
  forall a f n k,
    bin_contract_strict_above a f ->
    a < repeat f k n -> ((S k) + nat_size (repeat f (S k) n) <= nat_size n)%nat.
Proof.
  intros a f n k [Hf Haf] Han. induction k.
  - simpl in Han. apply div2_nat_size; [lia| apply Haf; trivial]. 
  - apply (Nat.le_trans _ (S k + nat_size (repeat f (S k) n)) _).
    + simpl. simpl in Han. assert (H := Han). apply Haf in H.
      apply div2_nat_size in H; lia.
    + assert (a < repeat f k n) as Han0.
    { apply (N.lt_le_trans _ (repeat f (S k) n) _); [apply Han| apply Hf]. }
    apply (IHk Han0).
Qed.


(* ****** COUNTDOWN *************************************)

Fixpoint countdown_worker (f : N -> N) (a n : N) (b : nat) : N :=
  match b with
  | O    => 0
  | S b' => if (n <=? a) then 0
             else 1 + countdown_worker f a (f n) b'
  end.

Definition countdown (f : N -> N) (a n : N) : N
  := countdown_worker f a n (nat_size n).


Lemma bin_contract_strict_threshold : forall a f n,
    bin_contract_strict_above a f -> exists (t : nat),
    (repeat f t n <= a
    /\ forall k, repeat f k n <= a -> (t <= k)%nat).
Proof.
  intros a f n Haf. destruct Haf as [Hf Haf].
  remember (N.to_nat (n - a)) as m eqn: Hm.
  symmetry in Hm. rewrite <- Nat2N.id in Hm.
  apply N2Nat.inj in Hm. generalize dependent a.
  induction m.
  - exists 0%nat. simpl. split.
    + rewrite <- N.sub_0_le. apply Hm.
    + intros. omega.
  - intros a Haf Hm. rewrite Nat2N.inj_succ in Hm.
    destruct (IHm (N.succ a)) as [x [Hax Haxn]];
    [intros; apply Haf; lia| lia| ].
    apply N.le_lteq in Hax. rewrite N.lt_succ_r in Hax.
    destruct Hax as [Hax | Hax]; [exists x| exists (S x)];
    split; try assumption.
    + intros k Hk. apply Haxn. lia.
    + rewrite <- N.lt_succ_r. simpl. rewrite Hax.
      apply (N.le_lt_trans _ (N.div2 (N.succ a)) _).
      * apply Haf. lia.
      * apply div2_contr; lia.
    + intros k Hk. assert (repeat f k n <= N.succ a) as H by lia.
      apply Haxn in H. destruct H; [lia| omega].
Qed.


Lemma countdown_base : forall f a n b,
    n <= a -> countdown_worker f a n b = 0.
Proof.
  intros f a n b Han. destruct b; trivial.
  rewrite <- N.leb_le in Han. simpl. rewrite Han. trivial.
Qed.

Lemma countdown_intermediate : forall f a n b i,
    contracting f -> ((S i) <= b)%nat -> (a < repeat f i n)
    -> countdown_worker f a n b =
       N.of_nat (S i) + countdown_worker f a (repeat f (S i) n) (b - (S i)).
Proof.
  intros f a n b i Hf.
  generalize dependent b. generalize dependent n.
  induction i; intros n b Hib Han; rewrite <- N.leb_gt in Han.
  - destruct b. inversion Hib. replace (S b - 1)%nat with b by omega.
    unfold countdown_worker. simpl in Han. rewrite Han. trivial.
  - rewrite IHi.
    + replace (b - S i)%nat with (S (b - S(S i))) by omega.
      unfold countdown_worker. rewrite Han.
      replace (N.of_nat (S(S i))) with (N.of_nat (S i) + 1).
      apply N.add_assoc. rewrite N.add_1_r.
      repeat rewrite Nat2N.inj_succ. trivial.
    + omega.
    + rewrite N.leb_gt in Han.
      apply (N.lt_le_trans _ (repeat f (S i) n) _).
      apply Han. apply Hf.
Qed.

Theorem countdown_repeat : forall f a n m,
    bin_contract_strict_above a f ->
    countdown f a n <= m <-> repeat f (N.to_nat m) n <= a.
Proof.
  intros f a n m Hf. unfold countdown.
  destruct (bin_contract_strict_threshold a f n Hf) as [t [Ht0 Ht1]].
  destruct t.
  - simpl in Ht0. rewrite (countdown_base _ _ _ _ Ht0).
    split; intro; try lia. apply (N.le_trans _ (repeat f 0 n) _).
    apply repeat_contract. apply Hf. omega. apply Ht0.
  - assert (a < repeat f t n) as Ht.
    { rewrite N.lt_nge. intro. apply Ht1 in H. omega. }
    rewrite (countdown_intermediate _ _ _ _ t).
    rewrite (countdown_base _ _ _ _ Ht0). rewrite N.add_0_r.
    replace m with (N.of_nat (N.to_nat m)) at 1 by apply N2Nat.id.
    unfold N.le at 1. rewrite <- Nat2N.inj_compare.
    rewrite Nat.compare_le_iff.
    split; intro.
    + apply (N.le_trans _ (repeat f (S t) n) _).
      apply repeat_contract. apply Hf. apply H. apply Ht0.
    + apply (Ht1 _ H).
    + apply Hf.
    + apply (Nat.le_trans _ (S t + nat_size (repeat f (S t) n))%nat _).
      omega. apply (repeat_bin_contract_strict a _ _ _ Hf Ht).
    + apply Ht.
Qed.

(* This countdown definition is consistent with its nat counterpart for
   strict binary contractions *)
Theorem countdown_correct : forall f a,
    bin_contract_strict_above a f ->
     countdown f a = to_N_func (countdown.countdown_to (N.to_nat a) (to_nat_func f)).
Proof.
  intros f a Haf. apply functional_extensionality. intro n.
  assert (countdown.contract_strict_above (N.to_nat a) (to_nat_func f))
  as Haf0 by apply (bin_contract_strict_Nnat a f Haf).
  unfold to_N_func. apply le_antisym.
  - rewrite countdown_repeat by apply Haf. rewrite Nat2N.id.
    rewrite le_N_nat. rewrite to_N_func_repeat. unfold to_N_func.
    rewrite Nat2N.id. rewrite <- countdown.countdown_repeat; trivial.
  - rewrite le_N_nat. rewrite Nat2N.id.
    rewrite countdown.countdown_repeat by apply Haf0.
    rewrite to_nat_func_repeat. rewrite <- N_nat_func_id.
    unfold to_nat_func. rewrite N2Nat.id. rewrite <- le_N_nat.
    rewrite <- countdown_repeat. lia. trivial.
Qed.