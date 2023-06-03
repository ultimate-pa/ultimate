//#rNonTerminationDerivable
/*
 * Author: Jan Leike
 * Date: 2016-01-08
 */

procedure main() returns (x, y, z: real)
{
  while (x >= 1.0 && y >= 1.0 && z >= 1.0) {
    x, y, z := 10.0*x - 8.0*y + 9.0*z,
                0.0*x + 5.0*y + 7.0*z,
                0.0*x + 0.0*y + 2.0*z;
  }
}

