//#Unsafe
/* Date: 2017-08-08
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;
	x := 0;
	x := x + 1;
	assert x == 0;
}
