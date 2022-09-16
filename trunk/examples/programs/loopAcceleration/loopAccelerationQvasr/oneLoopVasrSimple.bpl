//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x,y,z : int;
	x := 0;
	y := 0;
	
	while (x <= 5) {
		if (x - 3 > 0) {
			x := x + 1;
			y := y + 2;
		} else {
			x := x + 3;
			y := y + 2;
		}

	}
	assert x >= 6;
}
