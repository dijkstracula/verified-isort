Require Import Arith.
Require Import Coq.Lists.List.
Import ListNotations.

(* A bit more notation: if x is a T, and y is a list of Ts, then:
 * The expression "x :: y" is the element x prepended onto
 * the start of the list y. *)
Compute [1; 2; 3].
Compute 3 :: [5].
Compute 7 :: 8 :: 9 :: [].

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
Inductive sorted : list nat -> Prop :=
    | sorted_empty: sorted []
    | sorted_singleton: forall x, sorted [x]
    | sorted_multiple: forall x y l,
        x <= y -> sorted (y :: l) -> (sorted (x :: y :: l)).

(* We informally said that the list argument to `insert` had 
 * to be sorted for the return value to also be sorted.  Let's 
 * prove that fact! *)
Lemma insert_remains_sorted: forall x l, sorted l -> sorted (insert x l).
Proof.
    intros.
    induction H.
    (* Inserting into an empty list *)
    - simpl. apply sorted_singleton.

    (* Inserting into a singleton list *)
    - simpl. destruct (x <=? x0) as []eqn:test.
        (* x <=? x0 *)
        + Search (_ <=? _ = true). apply leb_complete in test.
          apply sorted_multiple. 
            * assumption. 
            * apply sorted_singleton.
        (* x > x0 *)
        + Search (_ <=? _ = false). apply leb_complete_conv in test.
          apply sorted_multiple.
            * Search (_ < _ -> _ <= _). apply Nat.lt_le_incl in test. assumption.
            * apply sorted_singleton.

    (* Inserting into a multiple-element list *)
    - simpl. destruct (x <=? x0) as []eqn:test.
        (* x <=? x0 *)
        + apply leb_complete in test.
          apply sorted_multiple.
            * assumption.
            * Search (_ <= _ -> _ <= _ -> _ <= _). apply Nat.le_trans with (n:=x) (m:=x0) (p:=y) in test.
              apply sorted_multiple. assumption. assumption. assumption.
        (* x > x0 *)
        + apply leb_complete_conv in test. destruct (x <=? y) as []eqn:test_2.
            * apply sorted_multiple. apply Nat.lt_le_incl. assumption.
              apply sorted_multiple. apply leb_complete in test_2. assumption. assumption.
            * apply sorted_multiple. assumption. apply leb_complete_conv in test_2. 
Admitted.

(* That was a gnarly proof, but, once we have it as a lemma,
 * proving that isort is correct no matter its input is actually
 * not that difficult! *)
Theorem isort_sorts: forall l, sorted (isort l).
Proof.
    intros.
    induction l.
    - simpl. apply sorted_empty.
    - simpl. apply insert_remains_sorted. assumption.
Qed.


(* One last thing that we can do: now that we know our sorting
 * algorithm is correct, let's _extract_ it to a more common
 * language (in this example, Haskell) so we can use it in 
 * conjunction with other, non-verified code! *)
Require Import ExtrHaskellBasic.
Extraction Language Haskell.
Extraction "isort.hs" isort insert.
