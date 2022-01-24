//#Unsafe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x,y,z : int;
	x := 0;
	y := 0;
	z := 0;
	
	while (x <= 20) {
		if (x <= 10) {
			z := 4;
			x := x + y;
			y := y + 1;
		} else {
			x := x + 2;
			y := y - 3;
			z := z + 1;
		}
	}
	assert x < 20;
}
