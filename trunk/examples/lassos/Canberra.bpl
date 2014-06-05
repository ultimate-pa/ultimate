//#rTermination
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Was previously known as SyntaxSupportDisjunction2.
 *
 * Terminates, but requires a new kind of ranking function.
 */

procedure Canberra() returns (x: int, y:int)
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
