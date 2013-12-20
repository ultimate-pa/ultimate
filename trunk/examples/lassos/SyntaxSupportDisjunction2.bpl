//#rTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of disjunctions in the loop condition
 */

procedure SyntaxSupportDisjunction2() returns (x: int, y:int)
{
    assume(true);
    while (x >= 0 || y >= 0) {
        if (x >= 0) {
            x := x - 1;
        } else if (y >= 0) {
            y := y - 1;
        }
    }
}
