//#Safe
/* Date: 2017-03-31
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x, y : int;
	x := 0;
	y := 0;
	while (x < 1000000) {
		if (x > 5000000) {
			y := y + 1;
		}
		x := x + 1;
	}
	assert x == 1000000;
	assert y == 0;
}
