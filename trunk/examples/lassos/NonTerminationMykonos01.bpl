//#rNonTerminationDerivable
/*
 * Date: 2018-02-14
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Probably smallest examples where we need a mu that is not zero.
 *
 */

procedure main() returns ()
{
    var a,b: int;
//      a := 1;
//      b := 1;
    while (
        a-b >= -2
        && b >= 1
    ) {
        a := 3 * a;
        b := 2 * b;
    }
}

