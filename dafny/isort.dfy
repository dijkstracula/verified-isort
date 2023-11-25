// Dafny is designed to be familiar to those programming in an OOP language like
// Java, so, we have plain old ordinary mutable arrays rather than the functional
// list data structures that we saw in Coq.  This means that unlike our Coq
// and Python examples, we can sort our array in-place and avoid needing a whole
// bunch of intermediary allocations.

// Just as before, we need a way of defining what it means for an array of nats
// to be sorted:
predicate sorted(a: seq<nat>)
{
    forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
}

// Here's insertion sort in pseudocode (c/o Wikipedia):
// n ← 1
// while n < length(A)
//    k ← n
//    while k > 0 and A[k-1] > A[k]
//        swap A[k-1] and A[k]
//        k ← k-1
//    end while
//    n ← n+1
// end while


method Isort(a: array<nat>)
    modifies a
    ensures sorted(a[..])
{
    if a.Length == 0 {
        return;
    }

    var n := 1;
    while n < a.Length
        invariant 1 <= n <= a.Length
        invariant sorted(a[..n])
    {
        var k := n;
        while k > 0 && a[k-1] > a[k]
            invariant forall i,j :: 0 <= i < j <= n && j != k ==> a[i] <= a[j]
        {
            a[k], a[k-1] := a[k-1], a[k];
            k := k-1;
        }

        n := n + 1;
    }
}