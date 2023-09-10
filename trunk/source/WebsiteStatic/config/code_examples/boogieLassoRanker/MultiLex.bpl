//#rTermination
/*
 * Date: 2014-10-17
 * Author: Jan Leike
 *
 * Program targeted at the lex(2-phase, 2-phase) template.
 *
 */

procedure main() returns (p: int, q: int, x: int)
{
	while (p >= 0) {
		if (q >= 0) {
			q := q - 1;
		} else {
			p := p - x;
			x := x + 1;
			havoc q;
		}
	}
}
