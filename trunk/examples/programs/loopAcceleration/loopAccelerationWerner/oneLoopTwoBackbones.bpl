//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * A single loop
 *
 */

procedure main() {
	var x, y : int;
	x := 0;
	y := 0;
	
	while (x < 5000) {
		x := x + 1;
		if (x <= 2500) {
			y := y+1;
		}
	}
	assert x == 5000;
	assert y == 2500;
}
