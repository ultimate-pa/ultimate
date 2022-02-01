//#Safe
/* Date: 2017-04-24
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x, y : int;
	x := 0;
	y := 0;
	while (x < 1000) {
		x := x + 1;
		y := 1;
	}

	while (x < 1000) {
		y := 2;
	}
	assert x == 1000;
	assert y == 1;
}
