//#rTerminationDerivable
/*
 * Date: 2012-04-02
 * Author: leike@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of division
 */

procedure SyntaxSupportDivision1() returns (x: int, y: int)
{
  var x_old: int;
  y := 0;
  assume(x >= 2);
  while (y >= 0) {
    x_old := x;
    x := x / 2;
    if (x_old > x) {
      y := -1;
    }
  }
}
