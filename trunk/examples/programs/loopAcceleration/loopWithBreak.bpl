//#Unsafe
/* Date: 2017-04-15
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;
	x := 0;
	while (x < 100) {
		if (x == 42) {
			break;
		}
		x := x + 1;
	}
	assert x == 100;
}
