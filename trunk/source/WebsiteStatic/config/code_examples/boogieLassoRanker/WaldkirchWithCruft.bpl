//#rTerminationDerivable
/*
 * Date: 2014-06-08
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 * This is the Waldkirch example with some irrelevant variables a, b, and c
 * added deliberately.
 */

procedure main() returns ()
{
  var x, a, b, c : int;
  assume(a == b);
  assume(c >= 3);
  while (x >= 0) {
    x := x - 1;
    a := a - 3;
    c := c + 2*b;
  }
}

