//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x,y : int;
	x := 0;
	y := 0;
	
	while (x < 100) {
		x := x + 1;
		y := y + 1;
	}
	assert y == 100;
}
