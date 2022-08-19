//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 *
 * A nested Loop
 *
 */

procedure main() {
	var x, y : int;
	x := 0;
	y := 0;
	
	while (x < 50) {
		x := x + 1;
		while (y < 100) {
			y := y + 1;
		}
	}
	assert x == 50;
	assert y == 100;
}
