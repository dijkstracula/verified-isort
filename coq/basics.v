Require Import Arith.

(* Here are two functions in Coq that consume and produce natural numbers. *)
Definition twice (n: nat) := n + n.
Definition two_times (n: nat) := 2 * n.

(* A notational fact about the natural numbers in Coq: "S n" refers to
 * the successor of some nat n; i.e. n + 1.  Equivalently: if we have
 * some natural number that is expressed as "S n", then n is its predecessor
 * (i.e. n-1). *)
Compute 2 + 2.
Compute S 17.

(* We can evaluate those functions with an argument and 
 * get back the value we would expect. *)
Compute twice 21.
Compute two_times (S 17).

(* How would you prove a property like this in CS 311H? *)
Theorem twice_is_two_times: forall n, twice n = two_times n.
Proof. 
    (* Let n be some natural number... introduces n to our context. *)
    intro n.
    (* Apply induction on n... Our goal is now split in two! *)
    induction n.

    (* Base case: *)
    - unfold twice. unfold two_times.
      Search (_ + 0 = _). rewrite Nat.add_0_r.
      Search (_ * 0 = _). rewrite Nat.mul_0_r.
      reflexivity.

    (* Inductive case: *)
    - unfold twice. unfold two_times. 
      simpl.
      rewrite Nat.add_0_r.
      reflexivity.
Qed.
