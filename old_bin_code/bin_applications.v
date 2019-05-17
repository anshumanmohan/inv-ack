Require Import BinNat.
Require Import Omega.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.
Require Import Nnat.
Require Import bin_prelims.
Require Import bin_repeater.
Require Import bin_countdown.
Require Import bin_inverse.

Require applications.

Definition countdown_to_1 (f : N -> N) (n : N) : N
  := countdown_worker f 1 n (nat_size (n - 1)).

Theorem countdown_to_1 (f : N -> N) (n : N) : N
  := 


Fixpoint inv_hyperop (a : N) (n : nat) (b : N) :=
  match n with
  | 0%nat => b - 1
  | 1%nat => b - a
  | 2%nat => (b + a - 1) / a
  | 