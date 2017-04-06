//#Safe
/* Date: 2017-04-04
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x, y : int;
	x := 0;
	y := 0;
	while (x < 1000000) {
		if (*) {
			y := y + 2;
		} else {
			y := y + 1;
		}
		x := x + 1;
	}
	assert y >= x;
	assert y <= 2 * x;
}
