//#rTerminationDerivable
/*
 * Date: 2013-01-19
 * Author: leike@informatik.uni-freiburg.de
 *
 * Has the ranking function f(x) = x
 * Needs support for integer division.
 */

procedure main() returns (x: int)
{
  while (x >= 1) {
    x := x / 2;
  }
}
