//#Safe
/* Date: 2017-03-31
 * Author: denniswoelfing@gmx.de
 *
 * A program that is equivalent to overapproximation.bpl but uses two loops
 * instead of one loop with two branches so that we can prove correctness.
 */

procedure main() {
	var x : int;
	x := 501;
	while (x < 1000) {
		x := x + 2;
	}
	assert x == 1001;
}
