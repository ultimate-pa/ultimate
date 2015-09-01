//#rNonTerminationDerivable
/*
 * Date: 2013-09-01
 * Author: leike@informatik.uni-freiburg.de
 *
 * TODO: text
 */

procedure NonTerminationMoreDifficult() returns (x, y, z: real)
{
  while (y + z >= 1.0 && x >= 1.0 && x + y <= 0.0 - 1.0) {
    x := 2.0*x;
    y := 3.0*y;
    z := 7.0*z;
  }
}

