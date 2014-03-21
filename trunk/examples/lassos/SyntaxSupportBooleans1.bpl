//#rTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans
 *
 * f(x) = x is a ranking function
 */

procedure SyntaxSupportBooleans1() returns (x: int, y:int)
{
    var b: bool;
    assume(true);
    while (x >= 0) {
        if (b) {
            x := x - 1;
        }
        if (!b) {
            x := x - 1;
        }
    }
}
