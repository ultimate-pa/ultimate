//#rTermination
/*
 * Date: 2014-10-05
 * Author: Jan Leike
 *
 * This program has a 5-phase ranking function.
 * It does not have a nested ranking function.
 */

procedure main() returns (a: int, b: int, c: int, d: int, e: int)
{
	assume true;
	while (a >= 0 || c >= 0) {
		a := a + b;
		b := b + c;
		c := c + d;
		d := d + e;
		e := e - 1;
	}
}
