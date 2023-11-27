// In Coq, we wrote functions, made logical statements about those functions,
// and then explicitly wrote out the proof derivation that those statements
// hold.  Dafny takes a different approach: it uses an automated theorem prover
// called an SMT solver

// Here is a standard implementation of absolute value that would use a branch
// instruction depending on the sign of the (BigInteger)-style int.  A Dafny
// ghost function is a mathematical function and only exists to the verifier; if
// we extracted this Dafny program it wouldn't appear.
ghost function abs(n: int): int
    // TODO: what fact should be true about the return value of abs()?
{
    if n > 0 then n else -n
}

// Here is another way to compute the absolute value for a 8-bit value without needing
// a branch instruction.  I certainly cannot prove that this is equivalent to
// our abs() function, but maybe Dafny can...?
method AbsU8(x: bv8) returns (ret: bv8)
    // TODO: how does the return value of AbsU8 relate to the return value of abs()?
{
    var y := x >> 8;
    ret := (x ^ y) - y;
}

// Unfortunately, Dafny isn't a mind-reader, and often needs help to understand
// what facts are true within and following a loop body in order to finish its proof.
method dec() returns (n: int)
    ensures n == 0
{
    var i := 100;
    while i > 0 
        // TODO: what loop invariant does Dafny need to know about?
    {
        i := i - 2;
    }
    n := i;
}


// Unfortunately, and, because this verification process is automated, things
// that ought to feel simple to prove cause the verifier to hang seemingly
// forever.  Here's another classic bit-twiddling hack to swap two 32-bit values
// that Dafny times out on:
method Swap(a: bv32, b: bv32)
{
    var x := a;
    var y := b;

    x := x ^ y;
    y := x ^ y;
    x := x ^ y;

    //assert (x, y) == (b, a);
}