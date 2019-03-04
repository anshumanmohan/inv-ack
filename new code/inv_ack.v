Require Import Omega.
Require Import prelims.
Require Import countdown_repeater.
Require Import inverse.
Require Import countdown_compute.

(*
=============================================================================
**************** SECTION 5: INVERSE OF KNUTH, ACKERMANN *********************
=============================================================================
*)

(* ****** 5.1. HYPEROPS, KNUTH ARROWS, ACKERMANN ****************************)

Fixpoint hyperop (n a b : nat) :=
match n with
| 0 => S b
| S n1 => match n1 with
          | 0 => repeater_from a (hyperop n1 a) b
          | S n2 => match n2 with
                    | 0 => repeater_from 0 (hyperop n2 a) b
                    | S n3 => repeater_from 1 (hyperop n3 a) b
                    end
          end
end.