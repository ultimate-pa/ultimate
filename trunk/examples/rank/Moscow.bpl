//#rTerminationDerivable
/*
 * Date: 2012-02-12
 * Author: leikej@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = 2x + y.
 */

procedure Moscow(c: int) returns (x: int, y: int)
free requires c > 0;
{
  while (2*x + y >= 0) {
    x := x - c;
    y := y + c;
  }
}
