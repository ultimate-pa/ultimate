//#rNonTerminationDerivable
/*
 * Date: 2015-09-07
 * Author: Jan Leike
 *
 * Even more difficult example for non-termination
 *
 * y = x^log_2.5(3)
 * y grows faster than x
 * Needs nilpotent components even though M is diagonalizable
 */

procedure main() returns (x, y: real)
{
  while (x + y >= 1.0 && x + 1.0 <= 0.0) {
    x := 2.5*x;
    y := 3.0*y;
  }
}

