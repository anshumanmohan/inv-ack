theory inv_ack_standalone
  imports "HOL-Library.Log_Nat" HOL.Divides
begin

value "floorlog (7::nat) 343" 

(* Countdown worker function *)
primrec cdn_wkr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 
                    nat \<Rightarrow> nat \<Rightarrow> nat" where
   "cdn_wkr f a n 0 = 0" |
   "cdn_wkr f a n (Suc k) = 
      (if n \<le> a then 0 else Suc (cdn_wkr f a (f n) k))"

(* Countdown *)
fun countdown_to :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"countdown_to f a n = cdn_wkr f a n n"

(* Inverse Ackermann worker function *)
primrec inv_ack_wkr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
"inv_ack_wkr f n k 0 = k" |
"inv_ack_wkr f n k (Suc b) = (if n \<le> k then k
                              else let g = (countdown_to f 1) in
                              inv_ack_wkr (g o f) (g n) (Suc k) b)"

(* Inverse Ackermann function in linear time *)
fun inv_ack_linear :: "nat \<Rightarrow> nat" where
"inv_ack_linear 0 = 0" |
"inv_ack_linear (Suc 0) = 0" |
"inv_ack_linear (Suc (Suc n)) = inv_ack_wkr (\<lambda> x. (x - 2)) n 1 (Suc n)"
 
value "inv_ack_linear 61" 
value "inv_ack_linear 100"
value "inv_ack_linear 61"
value "inv_ack_linear 1000"
value "inv_ack_linear 61"
value "inv_ack_linear 10000"
value "inv_ack_linear 61"
value "inv_ack_linear 100000"
value "inv_ack_linear 61"
value "inv_ack_linear 1000000"

end
