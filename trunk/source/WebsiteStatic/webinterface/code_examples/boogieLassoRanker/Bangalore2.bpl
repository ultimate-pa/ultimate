//#rNonTermination
/*
 * Date: 11.12.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Does not terminate for c = 0.
 */

procedure Bangalore2(c: int, y: int) returns (x: int)
{
  assume(c >= 0);
  while (x >= 0 && y == 0) {
    x := x - c;
  }
}

