//#rTerminationDerivable
/*
 * Date: 2014-06-29
 * Author: leike@informatik.uni-freiburg.de
 *
 * This program has the following 3-phase ranking function:
 * f_0(x, y, z) = z
 * f_1(x, y, z) = y
 * f_2(x, y, z) = x
 *
 * The program does not have a nested ranking function.
 */

procedure main() returns (x: int, y: int, z:int)
{
	assume true;
	while (x >= 0) {
		if (*) {
			x := x + y;
		} else {
			x := x + z;
		}
		y := y + z;
		z := z - 1;
	}
}
