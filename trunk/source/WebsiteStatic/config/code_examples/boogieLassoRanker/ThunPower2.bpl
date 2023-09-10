//#rTerminationDerivable
/*
 * Date: 2012-06-14
 * Author: leike@informatik.uni-freiburg.de, heizmann@informatik.uni-freiburg.de
 *
 * Two sucessive iterations of the program Thun.
 * Ranking function: f(x, y) = 3x+y
 * 
 */

procedure Thun() returns (x: int, y: int)
{
  assume true;
  while (x >= 0) {
    x := x + y;
    y := -2*y - 1;
    assume (x >= 0);
    x := x + y;
    y := -2*y - 1;

  }
}
