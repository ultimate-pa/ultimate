//#Safe
/* Date: 2018-05-25
 * Author: jonaswerner95@gmail.com
 *
 * loop with two paths inside, where both go through a shared node.
 *
 */

procedure main() {
	var x : int;
	x := 2;
	
	while (x <= 10) {
		if (x < 2) {
		
		} else {
			x := x + 1;
		}
	}	
	assert x == 11;
}
