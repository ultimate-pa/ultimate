//#rNontermination
// Author: Matthias Heizmann
// Date: 21.12.2013

// In r10729 the following incorrect affine ranking function is found.

// Ranking function f = -1
// Supporting invariants [2*d - 1 > 0, 2*d - 1 >= 0, 4*d - 1 > 0, 2*d - 1 >= 0]

var d : int;

procedure main() returns ()
modifies d;
{
    d := 2;
    while (true)
    {

    }
}