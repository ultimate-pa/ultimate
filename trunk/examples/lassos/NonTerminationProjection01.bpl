//#rNonTerminationDerivable
/*
 * Date: 2018-03-13
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * 
 *
 */

procedure main() returns ()
{
    var a,b: real;
//      a := 1;
//      b := 1;
    while (
        a-b >= -2
        && b >= 1
    ) {
        a, b := 0.75 * a + 0.25 * b, 0.25 * a + 0.75 * b + 2.0;
        
    }
}

