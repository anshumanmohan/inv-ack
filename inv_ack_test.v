Require Import Omega.
Require Import Program.Basics.
Require Import BinNat.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.

Require Import inv_ack.
Require Import bin_inv_ack.

(* Demonstrating Linear Runtime *)
Time Compute inv_ack_linear 100.
Time Compute inv_ack_linear 1000.
Time Compute inv_ack_linear 10000.
Time Compute inv_ack_linear 100000.
Time Compute inv_ack_linear 1000000.
Time Compute inv_ack_linear 10000000.

(* Further, our code can be extracted to OCaml by running the two lines below: *)
(*
Require Extraction. 
Recursive Extraction inv_ack_linear.
 *)

(* 
 * Next, assuming inv_ack_linear is in the same OCaml file,
 * our benchmarks can be tested in OCaml as follows: 
 *)

(*
let time n f x =
    let t = Sys.time() in
    let ans = f x in
    Printf.printf "Execution time for %d: \t%fs\n" n (Sys.time() -. t); ans;;

let rec buildnat j acc = 
  if j = 0 then acc else buildnat (j-1) (S acc);;

let time_print n = 
  time n inv_ack_linear (buildnat n O);;

time_print 100;;
time_print 1000;;
time_print 10000;;
time_print 100000;;
time_print 1000000;;
time_print 10000000;;
 *)

Open Scope N.

Definition bignum1 := 2^2^2^2.   (* tetration makes this 65536. *)
Definition bignum2 := bignum1^2. (* 4.3 e09 *)
Definition bignum3 := 2^bignum1. (* tetration makes this 2.0 e19728 *)
Definition bignum4 := bignum3^2. (* 4.0 e39456 *)

Time Compute (bin_inv_ack bignum1).
Time Compute (bin_inv_ack bignum2).
Time Compute (bin_inv_ack bignum3).
Time Compute (bin_inv_ack bignum4).

Close Scope N.