//#rNonTermination
/*
 * We should be able to solve it without stem, we cannot solve it with stem.
 * Currently we cannot solve it because Z3 runs into a timeout.
 * Date: 2015-09-01
 * Author: Jan Leike, Matthias Heizmann
 */

procedure main() returns (x, y, z: real)
{
//  assume(x > 0.0 && y > 0.0);
  while (z >= 0.0) {
    x, y := x + y, y - x + 1.0;
	z := z + x + 1.0;
  }
}

