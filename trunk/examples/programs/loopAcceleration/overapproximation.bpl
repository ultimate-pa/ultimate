//#Safe
/* Date: 2017-03-31
 * Author: denniswoelfing@gmx.de
 *
 * A program where we cannot prove correctness because of overapproximation.
 */

procedure main() {
	var x : int;
	x := 0;
	while (x < 1000) {
		if (x < 500) {
			x := x + 3;
		} else {
			x := x + 2;
		}
	}
	assert x == 1001;
}
