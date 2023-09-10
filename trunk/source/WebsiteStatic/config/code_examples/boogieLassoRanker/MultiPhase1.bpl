//#rTerminationDerivable
/*
 * Date: 2012-08-10
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following multiphase ranking function:
 * f_0(x, y) = x + y
 * f_1(x, y) = z
 * provided with the supporting invariants:
 * a - b <= 0
 * c >= 1
 */

procedure MultiPhase1(a: int, b: int, c: int) returns (x: int, y: int, z: int)
{
  assume(a == b && c >= 1);
  while (z >= 0) {
    x, y := y - c, x;
    z := z + x + y - a + b;
  }
}

