//#rTerminationDerivable
/*
 * Date: 2014-03-19
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans
 * Needs boolean support for supporting invariants
 *
 * f(x) = x is a ranking function with the supporting invariant b == true
 */

procedure SyntaxSupportBooleans3() returns (b: bool, x : int)
{
    assume(b);
    while (x >= 0) {
        if (b) {
          x := x - 2;
        }
        x := x + 1;
    }
}
