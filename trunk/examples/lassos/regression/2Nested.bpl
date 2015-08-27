//#rTerminationDerivable
/*
 * Date: 2012-08-10
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following multiphase ranking function:
 * f_0(x, y) = y + 1
 * f_1(x, y) = x
 */

procedure main() returns (x: int, y: int)
{
  assume true;
  while (x >= 0) {
    x := x + y;
    y := y - 1;
  }
}

