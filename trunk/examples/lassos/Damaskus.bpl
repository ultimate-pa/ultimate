//#rTerminationDerivable
/*
 * Date: 2012-07-31
 * Author: leike@informatik.uni-freiburg.de
 *
 * Terminates over the integers, but not over the reals
 */

procedure Damaskus(y: int) returns (x: int)
{
  assume y > x;
  while (x != y) {
    x := x + 1;
  }
}

