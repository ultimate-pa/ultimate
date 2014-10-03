//#rTerminationDerivable
/*
 * Date: 2014-10-03
 * Author: Jan Leike
 *
 * This program has the following 2-phase ranking function:
 * f_0(x, y, z) = y
 * f_1(x, y, z) = x
 *
 * The program does not have a nested ranking function.
 */

procedure main() returns (x: int, y: int)
{
	assume true;
	while (x >= 0 || y >= 0) {
		if (y < 0) {
			x := x - 1;
		} else {
			havoc x;
		}
		y := y - 1;
	}
}
