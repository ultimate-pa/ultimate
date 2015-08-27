//#rNonTerminationDerivable
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Simple example for non-termination
 */

procedure NonTerminationSimple2() returns (x: int)
{
  assume true;
  while (x >= 0) {
    x := x + 1;
  }
}

