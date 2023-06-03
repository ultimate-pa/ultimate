//#rTerminationDerivable
/*
 * Date: 11.12.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = x
 * provided with the supporting invariant y >= 1.
 */

procedure Bangalore() returns ()
{
  var x, y: int;
  assume(y >= 1);
  while (x >= 0) {
    x := x - y;
  }
}

