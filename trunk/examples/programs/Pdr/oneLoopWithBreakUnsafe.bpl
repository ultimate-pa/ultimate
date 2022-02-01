//#Unsafe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x < 10) {
		x := x + 1;
		if (x == 3) {
			break;
		}
	}
	assert x == 10;
}
