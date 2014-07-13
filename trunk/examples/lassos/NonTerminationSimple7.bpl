//#rNonTerminationDerivable
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

procedure main(c: int) returns (x: int)
{
  assume c == 0;
  while (x >= 0) {
    x := x + c;
  }
}

