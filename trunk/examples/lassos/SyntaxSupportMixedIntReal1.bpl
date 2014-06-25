//#rTerminationDerivable
/*
 * Date: 2014-06-25
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for mixing int and real variables in one loop
 *
 * This lasso has a two possible linear ranking functions:
 *
 * f(x, y) = x (int-valued)
 * f(x, y) = y (real-valued)
 */

var x: int;
var y: real;

procedure main() returns ()
modifies x,y;
{
  while (x >= 0 && y >= 0.0) {
    x := x - 1;
    y := y - 1.0;
  }
}
