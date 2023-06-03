//#rTerminationDerivable
/*
 * Date: 2013-03-06
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 * with supporting invariant y >= 0
 * (this supporting invariant is not non-decreasing)
 *
 */

procedure main() returns (x: int, y: int)
{
  assume(y >= 1);
  while (x >= 0) {
    x := x - y;
    y := 2*y;
  }
}
