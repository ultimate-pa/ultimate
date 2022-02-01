//#Safe
/* Date: 2017-06-28
 * Author: jonaswerner95@gmail.com
 *
 * loop with Array
 *
 */

procedure main() {
	var x : int;
	var a :[int] int;
	x := 0;
	a[0] := 1;
	
	while (x < 5000) {
		x := x + 1;
		a[0] := x;
	}
	assert x == 5000;
	assert a[0] == 5000;
}
