//#rNonTerminationDerivable
/*
 * Date: 2018-03-13
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 */

procedure main() returns ()
{
    var a,b: real;
//      a := -3.0;
//      b := 1.0;
    while (//*
         1.0*a-b >= -5.0
         && -a+4.0*b <= 4.0
    ) {
        a, b := 0.75 * a + 0.25 * b, 0.25 * a + 0.75 * b + 2.0;
        
    }
}

