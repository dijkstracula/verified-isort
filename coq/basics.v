Require Import Arith.

(* Here are two functions in Coq that consume and produce natural numbers. *)
Definition twice (n: nat) := n + n.
Definition two_times (n: nat) := 2 * n.

(* A notational fact about the natural numbers in Coq: "S n" refers to
 * the successor of some nat n; i.e. n + 1.  Equivalently: if we have
 * some natural number that is expressed as "S n", then n is its predecessor
 * (i.e. n-1). *)

(* We can evaluate those functions with an argument and 
 * get back the value we would expect. *)

(* It might be the case that if we were writing a compiler, we might want to 
 * know for sure that it is always possible to substitute x+x for 2*x and 
 * vice versa... How would you prove a property like this in CS 311H? *)
Theorem twice_is_two_times: forall n, twice n = two_times n.
Proof. 
(* Admitted means "assume that the proposition is true, without a proof of it.". 
 * You never want to leave anything Admitted because it might be wrong! *)
Admitted.
