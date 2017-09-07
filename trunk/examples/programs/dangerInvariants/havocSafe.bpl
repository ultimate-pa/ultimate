//#Safe
/* Date: 2017-08-22
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x, y : int;
	x := 1;
	havoc y;
	assert x != 2 * y;
}
