//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * A nested Loop
 *
 */

procedure main() {
	var x, y, z : int;
	x := 0;
	y := 0;
	z := 0;
	
	while (x < 5000) {
		x := x + 1;
		while (y < 10000) {
			y := y + 1;
			while (z < 7) {
				z := z + 1;
			}
		}
	}
	assert x == 5000;
	assert y == 10000;
	assert z == 7;
}
