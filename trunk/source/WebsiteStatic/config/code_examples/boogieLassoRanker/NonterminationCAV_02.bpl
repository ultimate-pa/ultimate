//#rNonTerminationDerivable
/*
 * Date: 2016-01-27
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
  var a, b: int;
  b := 1;
  while (a + b >= 3) {
    a := 3*a - 2;
    b := 2*b;
  }
}

