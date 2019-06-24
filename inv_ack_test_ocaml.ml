

type bool =
| True
| False

type nat =
| O
| S of nat

(** val sub : nat -> nat -> nat **)

let rec sub n m =
  match n with
  | O -> n
  | S k -> (match m with
            | O -> n
            | S l -> sub k l)

(** val compose : ('a2 -> 'a3) -> ('a1 -> 'a2) -> 'a1 -> 'a3 **)

let compose g f x =
  g (f x)

module Nat =
 struct
  (** val leb : nat -> nat -> bool **)

  let rec leb n m =
    match n with
    | O -> True
    | S n' -> (match m with
               | O -> False
               | S m' -> leb n' m')
 end

(** val cdn_wkr : (nat -> nat) -> nat -> nat -> nat -> nat **)

let rec cdn_wkr f a n = function
| O -> O
| S k' ->
  (match Nat.leb n a with
   | True -> O
   | False -> S (cdn_wkr f a (f n) k'))

(** val countdown_to : (nat -> nat) -> nat -> nat -> nat **)

let countdown_to f a n =
  cdn_wkr f a n n

(** val inv_ack_wkr : (nat -> nat) -> nat -> nat -> nat -> nat **)

let rec inv_ack_wkr f n k = function
| O -> k
| S b' ->
  (match Nat.leb n k with
   | True -> k
   | False ->
     let g = countdown_to f (S O) in inv_ack_wkr (compose g f) (g n) (S k) b')

(** val inv_ack_linear : nat -> nat **)

let inv_ack_linear n = match n with
| O -> O
| S n0 ->
  (match n0 with
   | O -> O
   | S _ ->
     let f = fun x -> sub x (S (S O)) in
     inv_ack_wkr f (f n) (S O) (sub n (S O)))

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