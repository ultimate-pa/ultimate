//#rNonTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Even more difficult example for non-termination
 *
 * y = x^log_2(3)
 * y grows faster than x
 */

procedure main() returns (x: int, y: int)
{
  while (x + y >= 1 && x <= -1) {
    x := 2*x;
    y := 3*y;
  }
}

