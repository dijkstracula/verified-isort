Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* A bit more notation: if x is a T, and y is a list of Ts, then:
 * The expression "x :: y" is the element x prepended onto
 * the start of the list y. *)

(* Adapted from Software Foundations volume 3: 
*  https://softwarefoundations.cis.upenn.edu/vfa-current/Sort.html
*) 

(* Okay, here's my Python version of insertion sort, ported to Coq: *)
Fixpoint insert (x : nat) (l : list nat) : list nat :=
    match l with
    | [] => [x]
    | h :: t => 
        if x <=? h then x :: h :: t 
        else h :: insert x t
    end.

Fixpoint isort (l: list nat) : list nat :=
    match l with
    | [] => []
    | h :: t => insert h (isort t)
    end.

(* What can we say about lists that are sorted? *)
Inductive sorted : list nat -> Prop := | sorted_todo: sorted [1;2;3].

(* We informally said that the list argument to `insert` had 
 * to be sorted for the return value to also be sorted.  This
 * proof is a bit gnarly, so let's assume that it is true (which
 * it is!) and come back to it later if we have time. *)
Lemma insert_remains_sorted: forall x l, sorted l -> sorted (insert x l).
Proof.
Admitted.

(* Once we have the above lemma, proving that isort is correct no matter its
 *input is actually not that
 * difficult! *)
Theorem isort_sorts: forall l, sorted (isort l).
Proof.
Admitted.


(* One last thing that we can do: now that we know our sorting
 * algorithm is correct, let's _extract_ it to a more common
 * language (in this example, Haskell) so we can use it in 
 * conjunction with other, non-verified code! *)
Require Import ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "isort.hs" isort insert.
