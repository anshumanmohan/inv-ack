Require Import Omega.
Require Import Setoid.

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
   | S m' => match div_helper n (0,0,m') with (* *)
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

(* Church's version *) (* can see, eg, SF for further info *)
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

(* Primitive recursive log, same basic function diagram trick *)
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

(* O(n) *)
Definition log (n m : nat) : nat :=
  match m with
  | 0 => 0
  | S m' => length (repeat_n n (inc_b m') nil) - 1
  end.

Fixpoint logger b n lc c : nat :=
  match n with
   | 0 => 0
   | S n' => match c with
              | 0 => S (logger b n' (lc * b) (lc - 1)) (* *)
              | S c' => logger b n' lc c'
             end
  end.
(* O(n) *)
Definition log' b n : nat :=
  logger b n (b * (b - 1)) (b - 1).

Fixpoint logger1 (b:nat) n lc c acc add : nat :=
  match n with
   | 0 => 0
   | S n' => match c with
              | 0 => S (logger1 b n' acc (lc - 1) (acc+add) add) (* key change *)
              | S c' => logger1 b n' lc c' (acc+add) add
             end
  end.

(* We want to argue that this is O(n) *)
Definition log1 b n : nat :=
  logger1 b n (b * (b - 1)) (b - 1) (b * (b-1)) (b * (b-1)).
(* the last arg is just a pre-calculated magic number
 * which we will add to acc at every step.
 * acc also starts with that number.
 *) 

Lemma checklog'log1: forall n b,
    log' b n = log1 b n.
Proof.
Abort.

Compute log1 5 700.
Compute log' 5 700.    

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



(* Fixpoint logger' b n lbase value logcount nextcount countercount thiscount : nat := *)
(*   match value with *)
(*    | 0 => logcount *)
(*    | S n' => match thiscount with *)
(*               | S c' => logger' base n' logcount nextcount countercount c' *)
(*               | 0 => match counter *)



(* Fixpoint logger' base l *)

Compute (log' 10 1025).

Compute (logger 3 27 6 2).
Compute (78 - 2 - 6 - 18).


Compute (logger 10 3 6 2).
Compute (logger 25 3 18 6).
Compute (logger 19 3 18 0).


(* logger 28 3 6 2 |-> *)
(* logger 27 3 6 1 |-> *)
(* logger 26 3 6 0 |-> *)
(* S (logger 25 3 18 6) |-> *)


(* S (logger 19 3 18 0) *)


(* Definition log' n b : nat := *)
(*   match b with *)
(*    | 0 => 0 *)
(*    | S b' => S (logger (n - 1) b (b * (b-1)) (b-1)) *)
(*   end. *)

(* Compute (log'' 5 2). *)

Compute (logger 20 3 6 2).

Compute (82 - 1 - 2 - 6 - 18 - (18 * 3)).

Compute (log 2 2).
Compute (log 256 2).
Compute (log 81 3).

Compute (log 200 3).

