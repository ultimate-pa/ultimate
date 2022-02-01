//#rNonTerminationDerivable
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Rotates x and y by 90 degrees
 * Does not terminate.
 */

procedure NonTerminationSimple2() returns (x: int, y: int)
{
  assume true;
  while (true) {
    x, y := -y, x;
  }
}

