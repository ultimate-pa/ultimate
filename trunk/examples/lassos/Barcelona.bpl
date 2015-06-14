//#rNonTerminationDerivable
// Author: Matthias Heizmann
// Date: 21.12.2013

// In r10729 the following incorrect affine ranking function is found.
// Problem seems to be related to Madrid.bpl

// Ranking function f = -1
// Supporting invariants [2*d - 1 > 0, 2*d - 1 >= 0, 4*d - 1 > 0, 2*d - 1 >= 0]

var d : int;

procedure main() returns ()
modifies d;
{
    assume( d >= 23);
    while (true)
    {

    }
}
