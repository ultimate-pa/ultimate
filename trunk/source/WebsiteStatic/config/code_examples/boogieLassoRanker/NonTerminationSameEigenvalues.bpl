//#rNonTerminationDerivable
/*
 * Date: 2018-04-02
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Example where matrix of determinisic program has the
 * same eigenvalue twice
 *
 */

procedure main() returns ()
{
    var a,b: int;
//      a := 1;
//      b := -1;
    while (
        b <= -1
    ) {
        a := 2 * a + b ;
        b := 2 * b;
    }
}

