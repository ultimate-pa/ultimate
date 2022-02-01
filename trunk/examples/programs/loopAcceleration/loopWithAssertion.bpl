//#Unsafe
/* Date: 2017-04-15
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;
	x := 0;
	while (x < 1000) {
		x := x + 1;
		assert x < 1000;
	}
}
