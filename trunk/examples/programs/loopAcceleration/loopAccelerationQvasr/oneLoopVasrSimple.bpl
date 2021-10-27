//#Unsafe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x,y,z : int;
	x := 0;
	y := 0;
	
	while (x <= 5) {
		x := x + 1;
		y := 3;
	}
	assert x == 3;
}
