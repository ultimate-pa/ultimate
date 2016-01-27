//#rNonTerminationDerivable
/*
 * Date: 2016-01-27
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
  var a, b: int;
  b := 2;
  while (a >= 1) {
    a := 3*a;
    b := 2*b;
  }
}

