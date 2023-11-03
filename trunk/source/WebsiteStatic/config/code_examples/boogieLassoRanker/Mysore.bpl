//#rTerminationDerivable
/*
 * Date: 2012-02-18
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, c) = x + c;
 * needs the for the lower bound to be able to depend on c.
 */

procedure Mysore() returns (x: int)
{
  var c: int;
  assume(c >= 2);
  while (x + c >= 0) {
    x := x - c;
    c := c + 1;
  }
}
