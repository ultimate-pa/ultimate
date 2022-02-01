//#Safe
/* Date: 2017-05-17
 * Author: denniswoelfing@gmx.de
 */

procedure main() {
	var x : int;

	if (*) {
		goto loop;
	}

	while (x < 1000000) {
loop:
		x := x + 1;
	}
}
