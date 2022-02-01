//#Safe
// Date: 2014-01-27
// Author: Matthias Heizmann
// Reveals bug in quantifier elimination up to revision 13376.
// Using DER we replaced for the term ∃x (a[x] == x) the variable x by a[x]
// although, a[x] contains x itself.

implementation main() returns (){

    mem[i] := i;
    assume i <= 42;
    assume ii <= mem[i];
    i := ii;
    assert i <= 42;
}

var mem : [int]int;
var i : int;
var ii : int;

procedure main() returns ();
modifies mem, i, ii;

