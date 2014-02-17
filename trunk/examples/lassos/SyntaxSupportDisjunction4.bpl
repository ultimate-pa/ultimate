//#rTerminationDerivable
/*
 * Date: 2013-12-21
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of disjunctions in the loop condition
 */

procedure SyntaxSupportDisjunction4() returns (x: int, y:int)
{
    var y_old: int;
    assume(true);
    while (x >= 0 || y >= 0) {
        y_old := y;
        if (x >= 0) {
            x := x - 1;
            havoc y;
            assume(y >= y_old + x);
        } else if (y >= 0) {
            x := x - 1;
            y := y + x;
        }
    }
}
