Require Import Omega.
Require Import Program.Basics.
Require Import BinNat.
Require Import micromega.Lia.
Require Import Logic.FunctionalExtensionality.

Require Import inv_ack.
Require Import bin_inv_ack.

(* Demonstrating Linear Runtime *)
(* Commented out for clean builds on the command line. 
 * Interested readers are encouraged to uncomment and run these lines. *)
(*
Time Compute inv_ack_linear 10000.
Time Compute inv_ack_linear 100000.
Time Compute inv_ack_linear 1000000.
Time Compute inv_ack_linear 10000000.
 *)

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
 *)