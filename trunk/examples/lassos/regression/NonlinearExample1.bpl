//#rTerminationDerivable
/*
 * Date: 2014-06-25
 * Author: leike@informatik.uni-freiburg.de
 *
 * This example needs nonlinear constraint solving or good Motzkin coefficient
 * guessing to work.
 *
 * Supporting invariant: y >= 1
 * Ranking function: f(x, y) = x
 */

procedure main() returns ()
{
  var x, y: int;
  assume(y >= 1);
  while (x >= 0) {
    x := x - y;
    y := 5*y;
  }
}

