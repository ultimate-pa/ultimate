//#rNonTerminationDerivable
/*
 * Date: 2015-12-06
 */

procedure main() returns (x, y, z: real)
{
  while (y > x && z > y && x > 0.0 && y > 0.0 && z > 0.0) {
    x := 2.0*x;
    y := 3.0*y;
	z := 23.0*z;
  }
}

