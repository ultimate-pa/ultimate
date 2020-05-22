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
	
	while (x < 1) {
		x := x + 1;
	}
	assert x == 2;
	
	while (x < 1) {
		x := x + 1;
	}
	assert x == 2;
}
