//#rNonTerminationDerivable
/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 * Has the fixed point x = 3 and hence does not terminate.
 */

procedure main() returns ()
{
    var x: int;
    while (x > 0) {
        x := -2*x + 9;
    }
}

