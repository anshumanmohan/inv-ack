Require Import divlog.

Definition div := divlog.div.

Definition div_c (b n : nat) : nat :=
match div n b with
| (d,0) => d
| (d,r) => S d
end.

Definition div_c_cost (b n : nat) : nat * nat :=
match div n b with
| (d, 0) => (d, n)
| (d, r) => (S d, n)
end.


Fixpoint logger (it b n : nat) : nat :=
match it with
| 0 => n
| S it' => match (div_c b n) with
           | 0 => 0
           | 1 => 1
           | n1 => S(logger it' b n1)
           end
end.

Definition log b n := logger n b n.

Fixpoint logger_cost (it b n cost : nat) : nat * nat :=
match it with
| 0 => (n, cost)
| S it' => match (div_c_cost b n) with
           | (0, c) => (0, c + cost)
           | (1, c) => (1, c + cost)
           | (n1, c) => match (logger_cost it' b n1 cost) with
                        | (v, c') => (S v, S (c + c' + cost)) end
           end
end.

Definition log_cost b n : nat * nat := logger_cost n b n 0.


Fixpoint next_inv_ack_level_worker (f : nat -> nat -> nat) (it b n : nat)
: nat :=
match it with
| 0 => n
| S it' => match (f b n) with
           | 0 => 0
           | 1 => 1
           | n1 => S(next_inv_ack_level_worker f it' b n1)
           end
end.

Definition next_inv_ack_level f b n := next_inv_ack_level_worker f (f b n) b n.


