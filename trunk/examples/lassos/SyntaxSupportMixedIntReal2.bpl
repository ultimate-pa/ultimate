//#rTerminationDerivable
/*
 * Date: 2014-02-17
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for mixing int and real variables in one loop
 *
 * This lasso has a 2-phase ranking function.
 */

var x: int;
var y: real;

procedure main() returns ()
modifies x,y;
{
  while (x >= 0 || y >= 0.0) {
    x := x - 1;
    y := y - 1.0;
  }
}
