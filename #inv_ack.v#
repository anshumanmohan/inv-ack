Require Import divlog.

Definition div := divlog.div.

Definition div_c (b n : nat) : nat :=
  match div n b with
   | (d,0) => d
   | (d,r) => S d
  end.

Fixpoint logger (b n nb m nbb : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| S n' => match m with
          | 0 => S(logger b n' nbb (nb - nbb - 1) (div_c b nbb))
          | S m' => logger b n' nb m' nbb
          end
end.

Definition log_helper b n nb := logger b n nb (n - nb - 1) (div_c b nb).

Definition log b n := log_helper b n (div_c b n).

Fixpoint logger_star (b n lgc m lglgc : nat) : nat :=
match n with
| 0 => 0
| 1 => 0
| S n' => match m with
          | 0 => S(logger_star b n' lglgc (lgc - lglgc - 1) (log b lglgc))
          | S m' => logger_star b n' lgc m' lglgc
          end
end.

Definition log_star_helper b n lgc := logger_star b n lgc (n - lgc - 1) (log b lgc).

Definition log_star b n := log_star_helper b n (log b n).

Compute log_star 2 15.
Compute log_star 2 16.
Compute log_star 2 17.
Compute log_star 2 25.


Fixpoint next_inv_ack_level_worker (f : nat -> nat -> nat) (b n fn cd ffn : nat) : nat
:=
match n with
| 0 => 0
| 1 => 0
| S n' => match cd with
          | 0 => S(next_inv_ack_level_worker f b n' ffn (fn - ffn - 1) (f b ffn))
          | S cd' => next_inv_ack_level_worker f b n' fn cd' ffn
          end
end.

Definition next_inv_ack_level (f : nat -> nat -> nat) b n
:= match (f b n) with
   | fn => match (f b fn) with
           | ffn => next_inv_ack_level_worker f b n fn (n - fn - 1) ffn
           end
   end.

Definition log' b n := next_inv_ack_level div_c b n.
Definition log_star' b n := next_inv_ack_level log' b n.

Compute log_star' 2 15.
Compute log_star' 2 16.
Compute log_star' 2 17.
Compute log_star' 2 25.


Fixpoint inv_ack_hier (i b n : nat) : nat :=
match i with
| 0 => n
| 1 => div_c b n
| S i' => next_inv_ack_level (inv_ack_hier i') b n
end.

Compute inv_ack_hier 3 2 15.
Compute inv_ack_hier 3 2 16.
Compute inv_ack_hier 3 2 17.
Compute inv_ack_hier 3 2 25.

Fixpoint inv_ack_hier_test i n : list nat :=
match n with
| 0 => nil
| S n' => (inv_ack_hier i 2 n') :: (inv_ack_hier_test i n')
end.

(* Compute inv_ack_hier_test 1 25.
Compute inv_ack_hier_test 2 25.
Compute inv_ack_hier_test 3 25.
Compute inv_ack_hier_test 4 25. *)

Fixpoint inv_ack_countdown_worker
         (f f1 f2 : nat -> nat -> nat)
         (b n n1 cd n2 : nat) 
: nat :=
match n with
| 0 => 0
| 1 => 0
| 2 => 0
| 3 => 0
| 4 => 1

| S n' =>
  match cd with
  | 0 => S(inv_ack_countdown_worker
           f1 f2 (next_inv_ack_level f2)
           b n' n2 (n1-n2-1) (S (f2 b n2)))

  | S cd' => inv_ack_countdown_worker
             f f1 f2
             b n' n1 cd' n2
  end
end.

Definition inv_ack_countdown_helper
           (f f1 : nat -> nat -> nat) (b n n1 : nat)
:= inv_ack_countdown_worker
   f f1 (next_inv_ack_level f1)
   b n n1 (n - n1 - 1) (S (f1 b n1)).

Definition inv_ack_countdown (f : nat -> nat -> nat) b n
:= inv_ack_countdown_helper f (next_inv_ack_level f) b n (f b n).

Compute inv_ack_countdown div_c 2 4.
Compute inv_ack_countdown div_c 2 25.