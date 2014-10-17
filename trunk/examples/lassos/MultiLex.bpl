//#rTermination
/*
 * Date: 2014-10-17
 * Author: Jan Leike
 *
 * Program targeted at the lex(2-phase, 2-phase) template.
 *
 */

procedure main() returns (q: int, x: int, y: int)
{
	while (q >= 0) {
		if (*) {
			q := q - x;
			x := x + 1;
		} else {
			q := q - y;
			y := y + 1;
		}
	}
}
