//#rTerminationDerivable
/*
 * Date: 2013-12-20
 * Author: leike@informatik.uni-freiburg.de
 *
 * Has the 3-parallel ranking function:
 * f = max{0, x + 1} + max{0, y + 1} + max{0, z + 1}
 */

procedure main() returns (x: int, y: int, z: int)
{
	while (x >= 0) {
		if (z < 0) {
			if (y < 0) {
				x := x - 1;
			} else {
				y := y - 1;
			}
		} else {
			z := z - 1;
		}
	}
}
