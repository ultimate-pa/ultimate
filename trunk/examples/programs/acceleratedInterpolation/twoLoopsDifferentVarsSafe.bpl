//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * Two loops different vars.
 *
 */

procedure main() {
	var x, y : int;
	x := 0;
	y := 0;
	
	while (x < 5) {
		x := x + 1;
	}
	assert x == 5;
	
	while (y < 10) {
		y := y + 1;
	}
	assert y == 10;
}
