Require Import Omega.
Require Import Logic.FunctionalExtensionality.
Require Import prelims.
Require Import repeater.
Require Import increasing_expanding.

(* ****** UPPER INVERSE ****************** *)

(* f is the upper inverse of F: f N is the smallest n such that F n >= N *)
Definition upp_inv_rel (f F : nat -> nat) : Prop :=
    forall n N, f N <= n <-> N <= F n.

(* An increasing F has a recursively definable upper inverse
   Under assumption F is increasing, the below definition will compute its upper inverse
   Do not use it for not always increasing functions *)
Fixpoint upp_inv (F : nat -> nat) (n : nat) : nat :=
  match n with
  | 0 => 0
  | S n' => let m := upp_inv F n' in
            if F m =? n' then S m else m
  end.

(* Proof that the above upper inverse definition is correct *)
Theorem upp_inv_correct :
    forall F, increasing F -> upp_inv_rel (upp_inv F) F.
Proof.
  intros F HF n N. generalize dependent n.
  induction N; intro n.
  - simpl. omega.
  - assert (N <= F (upp_inv F N)) as HN by (apply IHN; omega).
    simpl. remember (upp_inv F N) as m. remember (F m =? N) as b.
    symmetry in Heqb. destruct b.
    + rewrite Nat.eqb_eq in Heqb. rewrite <- Heqb.
      apply incr_twoways. apply HF.
    + rewrite Nat.eqb_neq in Heqb.
      assert (N < F m) as HNm by omega.
      split; rewrite IHN;
      [rewrite <- IHN; rewrite not_lt; rewrite incr_twoways by apply HF | ];
      omega.
Qed.

(* Proof that upper inverse is unique *)
Theorem upp_inv_unique :
    forall f F, increasing F -> (upp_inv_rel f F <-> f = upp_inv F).
Proof.
  intros f F HF.
  assert (upp_inv_rel (upp_inv F) F) as H by (apply upp_inv_correct; apply HF).
  split; intro.
  - apply functional_extensionality. intro N.
    assert (f N <= upp_inv F N).
    { rewrite (H0 _ N). rewrite <- (H _ N). trivial. }
    assert (upp_inv F N <= f N).
    { rewrite (H _ N). rewrite <- (H0 _ N). trivial. }
    omega.
  - rewrite H0. trivial.
Qed.

(* Repeat preserves upper inverse relation *)
Lemma upp_inv_repeat : forall k f F,
    upp_inv_rel f F -> upp_inv_rel (repeat f k) (repeat F k).
Proof.
  unfold upp_inv_rel. intros k f F HfF. induction k.
  1: intros n N; simpl; reflexivity.
  intros n N. rewrite repeat_S_comm. split.
  - intro. rewrite IHk in H. simpl. apply HfF. apply H.
  - simpl; rewrite <- HfF; rewrite IHk; trivial.
Qed.

(* The inverse of (repeater_from a F) is the minimum number of applications
   of (inverse F) to the input to get a result less than or equal to a.
   This serves as motivation to countdown (later on) and contractions. *)
Lemma upp_inv_repeater : forall a f F f',
    upp_inv_rel f F -> upp_inv_rel f' (repeater_from F a)
    -> (forall n m, f' n <= m <-> repeat f m n <= a).
Proof.
  intros a f F f' HfF Hf'F n m.
  rewrite (Hf'F m n). rewrite repeater_from_repeat.
  symmetry. apply (upp_inv_repeat m f F HfF a n).
Qed.

(* ****** CONTRACTIONS ****************** *)

(* Definition of non-strict contractions *)
Definition contracting (f : nat -> nat) : Prop :=
  forall n, f n <= n.

(* Definition of strict expansion *)
Definition contract_strict_above (a : nat) (f : nat -> nat) : Prop :=
  contracting f /\ (forall n, S a <= n -> S (f n) <= n).

(* Upper inverse of expansions are contractions *)
Theorem upp_inv_expand_contract :
    forall f F, expanding F -> upp_inv_rel f F -> contracting f.
Proof.
  intros f F HF HfF n. rewrite (HfF n n). apply HF.
Qed.

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

(* ****** PROPERTIES OF CONTRACTIONS ************ *)

(* repeat of contractions make the result smaller *)
Lemma repeat_contract :
  forall f n k l,
    contracting f -> k <= l -> repeat f l n <= repeat f k n.
Proof.
  intros f n k l Hf Hkl. induction l; inversion Hkl; trivial.
  apply IHl in H0.
  apply (Nat.le_trans _ (repeat f l n) _); [apply Hf | apply H0].
Qed.

(* strict version *)
Lemma repeat_contract_strict :
  forall a f n k,
    contract_strict_above a f ->
    S a <= repeat f k n -> (S k) + repeat f (S k) n <= n.
Proof.
  intros a f n k Hf Han. destruct Hf as [Hf Haf]. induction k.
  1: simpl in Han; simpl; apply Haf in Han; omega. 
  apply (Nat.le_trans _ (S k + repeat f (S k) n) _).
  - apply Haf in Han. simpl. simpl in Han. omega.
  - assert (S a <= repeat f k n) as Han0.
    { apply (Nat.le_trans _ (repeat f (S k) n) _); [apply Han|].
      apply Haf in Han. simpl. apply Hf. }
    apply IHk in Han0. omega.
Qed.


(* 
 * Cleaning up to replace "S a <= b" with "a < b".
 * The exact same proof works. 
 *)
Lemma repeat_contract_strict' :
  forall a f n k,
    contract_strict_above a f ->
    a < repeat f k n ->
    k + repeat f (S k) n < n.
Proof. apply repeat_contract_strict. Qed.
(* 
 * I wonder if maybe we can replace it like this everywhere,
 * provided it doens't affect the computation.
 *)
