//#Safe
/* Date: 2017-05-19
 * Author: denniswoelfing@gmx.de / dietsch@informatik.uni-freiburg.de 
 */

procedure main() {
	var x : int;
	x := 1000000;
	while (x > 0) {
		x := x - 1;
	}
	assert x == 0;
}
