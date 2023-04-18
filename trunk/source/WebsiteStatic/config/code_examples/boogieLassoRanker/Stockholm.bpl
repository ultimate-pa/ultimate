//#rTerminationDerivable
/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, a, b) = x;
 * needs the loop invariant b >= a.
 */

procedure Stockholm(a: int, b: int) returns (x: int)
free requires a == b;
{
  while (x >= 0) {
    x := x + a - b - 1;
  }
}
