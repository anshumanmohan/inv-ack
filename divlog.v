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

Definition div (n m : nat) : nat * nat :=
  match m with
   | 0 => (0,0)
   | S m' => match div_helper n (0,0,m') with
             (d,r,_) => (d,r)
             end
  end.

Definition div_c (n m : nat) : nat * nat :=
  match div n m with
   | (d,0) => (d,0)
   | (d,r) => (1 + d, m - r)
  end.

Compute (div 14 5).
Compute (div_c 14 5).

(* Church's version *)
Definition cnat : Type :=
  forall X : Type, (X -> X) -> X -> X.

Definition cnat_nat (n : cnat) : nat :=
  n nat S 0.

Definition czero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

Definition csucc (n : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (n X f x).

Definition cplus (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (n X f) (m X f x).

Definition cmult (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (n X (m X f) x).

Definition cexp (n m : cnat) : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => (m (X -> X) (n X) f x).

Fixpoint nat_cnat (n : nat) : cnat :=
  match n with
  | 0 => czero
  | S n' => csucc (nat_cnat n')
  end.

Definition div' (n m : nat) :=
  match m with
  | 0 => (0,0)
  | S m' => match nat_cnat n _ euclid_S (0,0,m') with
             (d,r,_) => (d,r)
             end
  end.

(* Primative recursive log, same basic function diagram trick *)
Require Import List.

(* O(1) amortised *)
Fixpoint inc_b (b : nat) (r : list (nat * nat)) : list (nat * nat) :=
  match r with
   | nil => (1, b - 1) :: nil
   | (d, S x) :: r' => (S d, x) :: r'
   | (d, 0) :: r' => (0,b) :: inc_b b r'
  end.

Definition repeat_n {X} n (f : X -> X) : X -> X :=
  nat_cnat n _ f.

(* b = base - 1,
   c = num digits before repeat - 1 
   amortised O(1) *)
Fixpoint inc_l1 (b : nat) (c : nat) (r : list (nat * nat * nat)) : list (nat * nat * nat) :=
  match r with
   | nil => (c, 1, b - 1) :: nil
   | (l, d, S x) :: r' => (l, S d, x) :: r'
   | (_, d, 0) :: r' => match inc_l1 b c r' with
      | nil => nil (* should never happen? *)
      | ((0, _, _) :: _) => nil
      | ((S l', _, _) :: _) as t => (l', 0, b) :: t
     end
  end.

Fixpoint hrm (n m : nat) :=
  match n with
   | 0 => 0
   | _ => match m with
           | 0 => 0
           | S m' => hrm n m'
          end
  end.

Lemma hrm_hrm: forall m, hrm 0 m = 0.
Proof.
  intro m. Fail reflexivity.
Abort.

(*
Lemma inc_l1_inv_nil: forall b c, exists r,
  inc_l1 b c r = nil.
Proof.
  induction c.
  + exists ((0,b-1,0) :: nil). trivial.
  + exists ((0,0,0) :: nil). simpl. trivial.

 destruct IHc.
  induction r; auto. intros.
  exfalso. destruct r; simpl in H;
  destruct a,p,n, c; try discriminate.
   simpl in H.
  
admit.
*)

Compute (repeat_n 1 (inc_l1 1 0) nil).
Compute (repeat_n 8 (inc_l1 1 2) nil).

Fixpoint exp b c :=
  match c with
   | 0 => 1
   | S c' => b * exp b c'
  end.

Fixpoint inc_l2 (b : nat) (r : list (nat * list (nat * nat * nat))) 
  : list (nat * list (nat * nat * nat)) :=
  match r with
  | nil => (0,inc_l1 b 0 nil) :: nil
  | (c,d) :: r' => match inc_l1 b c d with
    | nil => let n := exp (S b) c in
             (n, inc_l1 b n nil) :: inc_l2 b r'
    | d' => (c, d') :: r'
    end
  end.

Compute (repeat_n 1 (inc_l2 1) nil).
Compute (repeat_n 2 (inc_l2 1) nil).
Compute (repeat_n 3 (inc_l2 1) nil).
Compute (repeat_n 4 (inc_l2 1) nil).
Compute (repeat_n 5 (inc_l2 1) nil).
Compute (repeat_n 6 (inc_l2 1) nil).
Compute (repeat_n 7 (inc_l2 1) nil).
Compute (repeat_n 8 (inc_l2 1) nil).
Compute (repeat_n 15 (inc_l2 1) nil).
Compute (repeat_n 19 (inc_l2 1) nil).

Compute (repeat_n 66000 (inc_l2 1) nil).



Compute (repeat_n 8 (inc_b' 1 2) nil).


(S l, 0, b) :: 

(* O(n) *)
Definition log (n m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => length (repeat_n n (inc_b m') nil) - 1
  end.
Print Nat.add.

Fixpoint logger b n lc c : nat :=
match b with
| 0 => 0
| S _ => match n with
       | 0 => 0
       | S n' => match c with
                 | 0 => S (logger b n' (lc * b) (lc - 1))
                 | S c' => logger b n' lc c'
                 end
       end
end.

Lemma logger_simpl : forall b n lc c, logger b n lc c = logger b (n - c) lc 0.
Proof.
induction n.
- simpl. intros. reflexivity.
- destruct c.
  + reflexivity.
  + destruct b. simpl.
destruct (n-c); trivial.

Definition logger b n lc c : nat :=
match b with
| 0 => 0
| S _ => let fix logger' n lc c {struct n} :=
       match n with
       | 0 => 0
       | S n' => match c with
                 | 0 => S (logger' n' (lc * b) (lc - 1))
                 | S c' => logger' n' lc c'
                 end
       end in logger' n lc c
end.

Lemma logger_b_0 : forall n lc c, logger 0 n lc c = 0.
Proof.
intros.
simpl.
trivial.
Qed.

destruct n. simpl.
trivial.
simpl.
trivial.
Qed.


Fixpoint logger b n lc c : nat :=
match b with
| 0 => 0
| S _ => match n with
       | 0 => 0
       | S n' => match c with
                 | 0 => S (logger b n' (lc * b) (lc - 1))
                 | S c' => logger b n' lc c'
                 end
       end
end.

Print logger.

Lemma logger_b_0 : forall n lc c, logger 0 n lc c = 0.
Proof.
intros.
destruct n. simpl.
trivial.
simpl.
trivial.
Qed.

 unfold logger. simpl.

 reflexivity. simpl.

Fixpoint logger b n lc c : nat :=
  match n with
   | 0 => 0
   | S n' => match c with
              | 0 => S (logger b n' (lc * b) (lc - 1))
              | S c' => logger b n' lc c'
             end
  end.

Definition log' b n : nat :=
  logger b n (b * (b - 1)) (b - 1).

Fixpoint exp b e : nat :=
  match e with
   | 0 => 1
   | S e' => b * (exp b e')
  end.

Compute (log' 7 (exp 7 6)).

Definition fst_map {X Y Z : Type} (f : X -> Y) (p : X * Z) : Y * Z :=
  match p with (x, z) => (f x, z) end.

Definition snd_map {X Y Z : Type} (f : Y -> Z) (p : X * Y) : X * Z :=
  match p with (x, y) => (x, f y) end.

Fixpoint logger' b n lc c r : nat * nat :=
  match n with
   | 0 => (0,r)
   | S n' => match c with
              | S c' => logger' b n' lc c' (S r)
              | 0 => fst_map S (logger' b n' (lc * b) (lc - 1) 0)
             end
  end.

Definition log'' b n : nat * nat :=
  logger' b n (b * (b - 1)) (b - 1) 0.

Definition div''' a b := fst (div a b).
Definition log''' b n := fst (log'' b n).

Example change_of_base_broken:
  div''' (log''' 2 100) (log''' 2 7) <> log''' 7 100.
Proof. inversion 1. Qed.

Compute (log'' 3 80).
Compute (log'' 3 81).
Compute (log'' 3 82).



Fixpoint logger' b n lbase value logcount nextcount countercount thiscount : nat :=
  match value with
   | 0 => logcount
   | S n' => match thiscount with
              | S c' => logger' base n' logcount nextcount countercount c'
              | 0 => match counter



Fixpoint logger' base l

Compute (log' 10 1025).

Compute (logger 3 27 6 2).
Compute (78 - 2 - 6 - 18).


Compute (logger 10 3 6 2).
Compute (logger 25 3 18 6).
Compute (logger 19 3 18 0).


logger 28 3 6 2 |->
logger 27 3 6 1 |->
logger 26 3 6 0 |->
S (logger 25 3 18 6) |->


S (logger 19 3 18 0)


Definition log' n b : nat :=
  match b with
   | 0 => 0
   | S b' => S (logger (n - 1) b (b * (b-1)) (b-1))
  end.

Compute (log' 5 2).

Compute (logger 20 3 6 2).

Compute (82 - 1 - 2 - 6 - 18 - (18 * 3)).

Compute (log 2 2).
Compute (log 256 2).
Compute (log 81 3).

Compute (log 200 3).

