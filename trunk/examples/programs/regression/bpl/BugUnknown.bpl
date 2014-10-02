// #Safe
/* 
 * Variant of Alex's bitcounters reduced to two bit.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-09-28
 */
var x, y, of: bool;

procedure main() 
modifies x, y, of;
{

// 	of := false;
	x := false;
	y := false;
	
	while(of == false) {
		if (x == true) {
			x := false;
			of := true;
		} else {
			x := true;
		}
		if (of == true) {
			if (y == true) {
				y := false;
			}
			else {
				y := true;
				of := false;
			}
		}

	}
	assert (!x && !y);
}