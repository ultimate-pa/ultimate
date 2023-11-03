//#rTermination
/*
 * Date: 2013-01-11
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = x
 * provided with the supporting invariant y > 0.
 * Needs support for strict inequalities in the supporting invariant.s
 */

procedure BangaloreStrictIneq(y: real) returns (x: real)
{
  assume(y > 0.0);
  while (x >= 0.0) {
    x := x - y;
  }
}
