//#Unsafe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * Two loops same var.
 *
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x < 5) {
		x := x + 3;
	}
	assert x == 6;
	
	while (x < 10) {
		x := x + 3;
	}
	assert x == 13;
}
