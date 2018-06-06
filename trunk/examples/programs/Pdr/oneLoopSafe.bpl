//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * A single loop
 *
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x < 1) {
		x := x + 1;
	}
	assert x == 1;
}
