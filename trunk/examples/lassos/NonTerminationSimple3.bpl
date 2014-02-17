//#rNonTerminationDerivable
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for c >= 0.
 */

procedure NonTerminationSimple3(c: int) returns (x: int)
{
  assume true;
  while (x >= 0) {
    x := x + c;
  }
}

