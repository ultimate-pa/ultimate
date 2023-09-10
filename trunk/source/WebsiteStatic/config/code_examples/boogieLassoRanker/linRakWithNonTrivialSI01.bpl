//#rTerminationDerivable
/*
 * Date: 8.1.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = x
 * provided with the supporting invariant x > y.
 */

procedure main() returns ()
{
  var x, y, oldy: int;
  assume(x - y >= 1);
  while (x >= 0) {
    oldy := y;
    y := 2*y - x;
    x := oldy;
  }
}
