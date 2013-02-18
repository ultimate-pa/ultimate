//#rTerminationDerivable
/*
 * Date: 2012-08-10
 * Author: leikej@informatik.uni-freiburg.de
 *
 * This program has the following multiphase ranking function:
 * f_0(c, x, y, z, w) = w + 1
 * f_1(c, x, y, z, w) = z
 * f_2(c, x, y, z, w) = y
 * f_3(c, x, y, z, w) = x
 * provided with the supporting invariant c > 0.
 */

procedure FourPhase(c: int) returns (x: int, y: int, z: int, w: int)
{
  assume c > 0;
  while (x >= 0) {
    x := x + y;
    y := y + z;
    z := z + w;
    w := w - c;
  }
}

