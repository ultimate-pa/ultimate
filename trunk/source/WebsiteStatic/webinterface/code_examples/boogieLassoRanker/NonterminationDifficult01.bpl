//#rNonTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Difficult example for non-termination
 *
 * y = x^log_2(3)
 */

procedure main() returns (x: int, y: int)
{
  x := 1;
  y := 1;
  while (x >= 0) {
    x := 2*x;
    y := 3*y;
  }
}

