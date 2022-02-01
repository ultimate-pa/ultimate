//#Safe
/* Date: 2018-05-25
 * Author: jonaswerner95@gmail.com
 *
 */

procedure main() {
	var x : int;
	x := 2;
	
	while (x <= 10) {
		if (x > 2) {
			x := x + 1;
		} else {
			x := x + 1;
		}
		x := x + 1;
	}	
	assert x == 12;
}
