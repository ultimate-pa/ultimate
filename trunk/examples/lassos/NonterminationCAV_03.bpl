//#rNonTerminationDerivable
/*
 * Date: 2016-01-27
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
  var a, b: int;
   b := 2;
//    a := 1;
  while (a >= b && b >= 1) {
	  a := 3*a + b;
	  b := 2*b;
  }
}

