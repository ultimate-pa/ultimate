//#rNonTermination
/*
 * Does not terminate for x = 1.
 *
 * Date: 06.04.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure Cairo2() returns (x: int)
{
  assume(x > 0);
  while (x != 0) {
    x := x - 2;
  }
}
