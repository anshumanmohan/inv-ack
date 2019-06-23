Require Import Omega.
Require Import Program.Basics.
Require Import BinNat.

(* ********** COUNTDOWN AND INVERSE ACKERMANN ON NAT ********** *)

(* Countdown worker function *)
Fixpoint countdown_worker (f : nat -> nat) (a n k : nat) : nat :=
  match k with
  | 0    => 0
  | S k' => if (n <=? a) then 0 else
              S (countdown_worker f a (f n) k')
  end.

(* Countdown *)
Definition countdown_to f a n := countdown_worker f a n n.

(* Inverse Ackermann worker function *)
Fixpoint inv_ack_worker (f : nat -> nat) (n k b : nat) : nat :=
  match b with
  | 0    => k
  | S b' => match (n - k) with
            | 0   => k
            | _ => let g := (countdown_to f 1) in
                     inv_ack_worker (compose g f) (g n) (S k) b'
            end
  end.

(* Inverse Ackermann function *)
(* Definition by hard-coding up to the second bin_alpha level, runtime O(n) *)
Definition inv_ack_linear n :=
  match n with
  | 0 | 1 => 0
  | _     => let f := (fun x => x - 2) in inv_ack_worker f (f n) 1 (n - 1)
  end.


(* ********** COUNTDOWN AND INVERSE ACKERMANN ON N (BINARY) ********** *)

Open Scope N_scope.

(* Supporting function - Use to compute the budget for bin_cdn_wkr and inv_ack_wrk
   Returns length of the binary representation in type "nat" *)
Definition nat_size (n : N) : nat :=
  match n with
  | 0 => 0%nat
  | Npos p => let fix nat_pos_size (x : positive) : nat :=
                  match x with
                  | xH => 1%nat
                  | xI y | xO y => S (nat_pos_size y) end
                  in nat_pos_size p
  end.

(* Countdown worker function *)
Fixpoint bin_cdn_wkr (f : N -> N) (a n : N) (b : nat) : N :=
  match b with
  | O    => 0
  | S b' => if (n <=? a) then 0
             else 1 + bin_cdn_wkr f a (f n) b'
  end.

(* Countdown *)
Definition bin_countdown_to (f : N -> N) (a n : N) : N
  := bin_cdn_wkr f a n (nat_size (n - a)).

(* Inverse Ackermann worker function *)
Fixpoint bin_inv_ack_worker (f : N -> N) (n k : N) (bud : nat) : N :=
  match bud with
  | 0%nat  => k
  | S bud' =>
    if n <=? k then k
      else let g := (bin_countdown_to f 1) in
      bin_inv_ack_worker (compose g f) (g n) (N.succ k) bud'
  end.

(* Inverse Ackermann function *)
(* Definition by hard-coding up to the fourth bin_alpha level, runtime O(log n) *)
Definition bin_inv_ack n :=
  if (n <=? 1) then 0
  else if (n <=? 3) then 1
  else if (n <=? 7) then 2
  else let f := (fun x => N.log2 (x + 2) - 2) in
        bin_inv_ack_worker f (f n) 3 (nat_size n).