Require Import Omega.
Require Import Program.Basics.

Fixpoint countdown_worker (f : nat -> nat) (a n k : nat) : nat :=
  match k with
  | 0    => 0
  | S k' => if (n <=? a) then 0 else
              S (countdown_worker f a (f n) k')
  end.

Definition countdown_to f a n := countdown_worker f a n n.

Fixpoint inv_ack_worker (f : nat -> nat) (n k b : nat) : nat :=
  match b with
  | 0    => k
  | S b' => match (n - k) with
            | 0   => k
            | _ => let g := (countdown_to f 1) in
                     inv_ack_worker (compose g f) (g n) (S k) b'
            end
  end.

Definition inv_ack_linear n :=
  match n with
  | 0 | 1 => 0
  | _     => let f := (fun x => x - 2) in inv_ack_worker f (f n) 1 (n - 1)
  end.