//#Unsafe
/* Date: 2017-08-26
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;
	x := 1;
	if (*) {
		assert x >= 0;
	} else {
		assert x <= 0;
	}
}
