//#Safe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x : int;
	x := 0;
	
	while (x < 10) {
		x := x + 1;
	}
	assert x == 10;
}
