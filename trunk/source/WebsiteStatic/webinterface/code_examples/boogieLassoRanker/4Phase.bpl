//#rTerminationDerivable
/*
 * Date: 2014-10-07
 * Author: Jan Leike
 *
 * This program has a 4-phase ranking function.
 * It does not have a nested ranking function.
 */

procedure main() returns (a: int, b: int, c: int, d: int)
{
	assume true;
	while (a >= 0 || c >= 0) {
		a := a + b;
		b := b + c;
		c := c + d;
		d := d - 1;
	}
}
