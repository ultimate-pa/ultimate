//#Unsafe
/* Date: 2018-05-25
 * Author: jonaswerner95@gmail.com
 *
 * A simple program
 *
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x <= 5) {
		if (x - 2 > 1) {
			x := x + 1;
		} else {
			x := x + 2;
		}
		x := x + 2;
	}	
	assert x > 7;
}
