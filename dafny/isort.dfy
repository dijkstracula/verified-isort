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

method Isort(a: array<nat>)
    modifies a
    ensures sorted(a[..])
{
    if a.Length == 0 {
        return;
    }

    // Here is the thing that we have to get Dafny to understand:
    //
    // We are going to iterate from left to right in the input array.  As we
    // progress, everything to the left of the current element is going to be
    // in sorted order, so that when we finish iterating through the array all
    // elements are going to be in their correct order.
    //
    // Let's look at some iteration of that main loop, where we're neither at the
    // beginning nor at the end of the process:
    // 
    //      0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
    //    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    //  a | ✓ | ✓ | ✓ | ✓ | ✓ | = |   |   |   |   |   |   |   |   |   |   |
    //    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    //    \------------------/^
    //     These elements are |
    //       in sorted order  n == 5: this element will be placed in its right place
    //                                by the end of the current loop iteration...
    //

    // In particular, there's some index j on [0..n) where a[j-1] <= a[n] and a[j] > a[n].
    //
    //      0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
    //    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    //  a | <=| <=| <=| > | > | = |   |   |   |   |   |   |   |   |   |   |
    //    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    //    \----------/^\-----/
    //       <= a[n]  | > a[n]
    //                |
    //                +--- k == 3: This is the index of where a[5] should go!

    // So, we'll shift all the elements on [j, n) over by one, so they're now 
    // located on [j+1, n+1), and then place the old value of a[n] into a[j].
    //
    //      0   1   2   3   4   5   6   7   8   9  10  11  12  13  14  15
    //    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    //  a | <=| <=| <=| = | > | > |   |   |   |   |   |   |   |   |   |   |
    //    +---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+---+
    //    \----------/     \-----/
    //       <= a[n]        > a[n]
    //
    // And now we have one more element in the correct place!  We are now ready
    // to begin the next iteration of the loop.

    var n := 1;
    while n < a.Length
        invariant 1 <= n <= a.Length
        invariant sorted(a[..n])
    {

        var curr := a[n];

        // 1. Find our pivot position k, the location where we should insert the
        // current value.
        var k := n;
        while k > 0 && a[k-1] > curr
            invariant forall i :: k <= i < n ==> a[i] > curr
        {
            k := k-1;
        }

        a[n] := a[n-1]; // Hack to help the verifier with invariant sorted(a[k..n+1])

        // 2. Shift all elements between k and n to the right by one.
        var j := n-1;
        while j >= k
            invariant j < n
            invariant sorted(a[..k])
            invariant sorted(a[k..n+1])
            invariant forall i :: 0 <= i < k ==> a[i] <= curr
            invariant forall i :: k <= i < n ==> a[i] > curr
        {
            assert a[j+1] >= a[j];
            a[j+1] := a[j];
            j := j-1;
        }

        assert forall i :: 0 <= i < k ==> a[i] <= curr;
        assert forall i :: k <= i < n ==> a[i] > curr;
        assert sorted(a[..k]);
        assert sorted(a[k..n+1]);

        // 3. Put curr in its place!
        a[k] := curr;

        assert forall i :: 0 <= i <= k ==> a[i] <= curr;
        assert a[k] == curr;
        assert forall i :: k < i < n ==> a[i] > curr;
        
        assert sorted(a[..k+1]);
        assert sorted(a[k..n+1]);
        assert sorted(a[..n+1]);

        n := n + 1;
    }
}
