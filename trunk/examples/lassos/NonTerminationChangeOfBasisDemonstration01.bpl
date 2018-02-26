//#rNonTerminationDerivable
/*
 * Date: 2018-02-14
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
    var a,b: int;
    a := 1;
    while (b >= -2 && 3*a +2 >= b && a+b >= 1) {
        a := 3 * a - 1;
        b := 2 * b + a + 1;
    }
}

