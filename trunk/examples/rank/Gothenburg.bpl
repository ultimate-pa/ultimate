//#rTermination
/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y, a, b) = x + y;
 * needs the loop invariant a = b.
 * (More diffcult version of Stockholm.)
 */

procedure Gothenburg(a: int, b: int) returns (x: int, y: int)
free requires a == b;
{
  while (x >= 0 || y >= 0) {
    x := x + a - b - 1;
    y := y + b - a - 1;
  }
}
