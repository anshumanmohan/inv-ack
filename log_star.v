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
