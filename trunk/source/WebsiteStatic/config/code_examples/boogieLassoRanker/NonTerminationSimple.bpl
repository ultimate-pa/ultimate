//#rNonTerminationDerivable
/*
 * Date: 2013-12-16
 * Author: leike@informatik.uni-freiburg.de
 *
 * Very simple example for non-termination
 */

procedure NonTerminationSimple() returns (x: int)
{
  assume true;
  while (true) {
    // do nothing
  }
}

