//#rTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Was previously known as SyntaxSupportDisjunction2 and Canberra.bpl.
 *
 * Has the 2-parallel ranking function:
 * f = max{0, x + 1} + max{0, y + 1}
 */

procedure main() returns (x: int, y:int)
{
    while (true) {
        if (x >= 0) {
            x := x - 1;
        } else {
            assume(y >= 0);
            y := y - 1;
        }
    }
}
