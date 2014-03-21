//#rTerminationDerivable
/*
 * Date: 2014-03-19
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans
 *
 * f(x) = (b ? 1 : 0) is a ranking function
 */

procedure SyntaxSupportBooleans2() returns (b: bool)
{
    assume(b);
    while (b) {
        b := false;
    }
}
