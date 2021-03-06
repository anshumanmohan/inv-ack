Require Import BinNat.

Open Scope N_scope.

Definition exp x y :=
match y with
| 0 => 1
| Npos y'
  => match x with
     | 0 => 0
     | _ => let fix expPos (p : positive) :=
             match p with
             | xH => x
             | xI p' => let t := expPos p' in t * t * x
             | xO p' => let t := expPos p' in t * t
             end in expPos y'
     end
end.

Print N.pos_div_eucl.

Fixpoint countdown_worker (a : N) (f : N -> N) (n : N) (b : nat) : N :=
match b with
| O => 0
| S b' => if (n <=? a) then 0 else N.succ (countdown_worker a f (f n) b')
end.

Definition countdown a f n := countdown_worker a f n (N.to_nat n).

Print N.size.
