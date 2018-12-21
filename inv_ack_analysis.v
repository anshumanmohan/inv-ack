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

Compute div_c 2 4.


Definition euclid_S_cost (et : nat * nat * nat) : nat * nat * nat :=
  match et with
    | (n, m, 0) => (S n, 0, m)
    | (n, m, S c) => (n, S m, c)
  end.



Fixpoint div_helper_cost (n : nat) (et : nat * nat * nat)   : nat * nat * nat
:=
  match n with
   | 0 => et
   | S n' => div_helper_cost n' (euclid_S_cost et)
  end.

Definition div_cost (n m cost : nat) : nat * nat * nat :=
  match m with
   | 0 => (0,0, cost)
   | S m' => match div_helper_cost n (0,0,m') with (* *)
             (d,r,_) => (d,r, n + cost)
             end
  end.
  
Definition div_c_cost (m n cost : nat) : nat * nat :=
  match div_cost n m cost with
   | (d,0,c) => (d, c)
   | (d,r,c) => (1 + d, c)
  end.


Fixpoint next_inv_ack_level_worker_cost
        (f : nat -> nat -> nat -> nat * nat)
        (b n fn cd ffn : nat)
        (cost : nat)
: nat * nat :=
match n with
| 0 => (0, cost)
| 1 => (0, cost)
| S n' => match cd with
          | 0 => match (f b ffn 0) with
                 | (t, c0) => match (next_inv_ack_level_worker_cost
                               f b n' ffn (fn - ffn - 1) t cost) with
                              | (v, c) => (S v, (1 + ffn + c0 + c))
                              end
                 end
          | S cd' => match (next_inv_ack_level_worker_cost f b n' fn cd' ffn cost) with
                     | (v, c) => (v, S c)
                     end
          end
end.

Definition next_inv_ack_level_cost (f : nat -> nat -> nat -> nat * nat) b n cost
:= match (f b n 0) with
   | (fn, c0)
      => match (f b fn 0) with
         | (ffn, c1)
            => match (next_inv_ack_level_worker_cost
                      f b n fn (n - fn - 1) ffn cost) with
               | (v, c) => (v, c0 + c1 + fn + c)
               end
         end
  end.


Definition log_cost' b n cost := next_inv_ack_level_cost div_c_cost b n cost.

Definition log_star_cost' b n cost := next_inv_ack_level_cost log_cost' b n cost.

Definition log_star_cost'' b n cost :=
match (next_inv_ack_level_cost log_cost' b (log b n) cost) with
| (v, c) => (S v, S c) end.


Fixpoint inv_ack_hier_cost (i b n cost : nat) : nat * nat :=
match i with
| 0 => (n, 0)
| 1 => div_c_cost b n cost
| S i' => next_inv_ack_level_cost (inv_ack_hier_cost i') b n cost
end.
