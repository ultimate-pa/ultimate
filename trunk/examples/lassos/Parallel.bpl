//#rTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Was previously known as SyntaxSupportDisjunction2 and Canberra.bpl.
 *
 * Terminates, but requires a new kind of ranking function.
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
