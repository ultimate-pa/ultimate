//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * Two loops same var.
 *
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x < 5000) {
		x := x + 1;
	}
	assert x == 5000;
	
	while (x < 10000) {
		x := x + 1;
	}
	assert x == 10000;
}
