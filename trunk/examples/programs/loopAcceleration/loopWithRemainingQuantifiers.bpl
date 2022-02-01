//#Safe
/* Date: 2017-03-24
 * Author: denniswoelfing@gmx.de
 *
 * A loop that where we can calculate an accelerated Icfg but where we cannot
 * eliminate quantifiers.
 */

procedure main() {
	var x : int;
	x := 0;
	while (x < 1000000) {
		x := x + 2;
	}
	assert x == 1000000;
}
