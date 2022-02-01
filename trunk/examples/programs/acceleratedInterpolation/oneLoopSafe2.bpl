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
	
	while (x < 15) {
		x := x + 2;
	}
	assert x == 16;
}