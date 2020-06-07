//#Unsafe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * A single loop
 *
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x < 20) {
		x := x + 1;
		assert x > 0;
	}
	assert x <= 20;
}
