//#Unsafe
/* Date: 2017-06-10
 * Author: jonaswerner95@gmail.com
 */

procedure main() {
	var x,y,z : int;
	x := 0;
	y := 0;
	
	while (x <= 5) {
		if (x < 1){
			x := x + 1;
			y := y + 4;
		} 
		else {
			x := x + 2;
			y := y + 7;
		}

	}
	assert x == 3;
}
