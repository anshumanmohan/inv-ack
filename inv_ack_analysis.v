Require Import inv_ack.

Fixpoint inv_ack_countdown_states_worker
         (f f1 f2 : nat -> nat -> nat)
         (b n n1 cd n2 : nat)
         (count : nat)
: list (nat * nat * nat * nat * nat) :=
match n with
| 0 => nil
| 1 => nil
| 2 => nil
| 3 => nil

| S n' =>
  match cd with
  | 0 => (n', n1, 0, n2, (S count))
          :: (inv_ack_countdown_states_worker
              f1 f2 (next_inv_ack_level f2)
              b n' n2 (n1-n2-1) (S (f2 b n2)) (S count))

  | S cd' => (n', n1, cd', n2, count)
              :: inv_ack_countdown_states_worker
                 f f1 f2 b n' n1 cd' n2 count
  end
end.

Definition inv_ack_countdown_states_helper_0
           (f f1 : nat -> nat -> nat) (b n n1 cd n2: nat)
: list (nat * nat * nat * nat * nat) :=
(n, n1, cd, n2, 0) :: (inv_ack_countdown_states_worker
                       f f1 (next_inv_ack_level f1)
                       b n n1 cd n2 0).

Definition inv_ack_countdown_states_helper
           (f f1 : nat -> nat -> nat) (b n n1 : nat)
:= inv_ack_countdown_states_helper_0
   f f1 b n n1 (n - n1 -1) (S (f1 b n1)).

Definition inv_ack_countdown_states (f : nat -> nat -> nat) b n
:= inv_ack_countdown_states_helper f (next_inv_ack_level f) b n (f b n).

Compute inv_ack_countdown_states div_c 2 25.
Compute div_c 2 4.