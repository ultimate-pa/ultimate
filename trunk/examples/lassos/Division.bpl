//#rNonTerminationDerivable
/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for 0 <= x <= 10
 * due to rounding in integer division.
 */

procedure Division(x: int) returns (y: int)
{
  y := x;
  while (y >= 0 && y <= 10) {
    y := (2*y + 1) / 2;
  }
}
