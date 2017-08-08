//#Unsafe
/* Date: 2017-08-08
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;
	x := 0;
	while (x < 10) {
		x := x + 1;
	}
	assert x != 10;
}
