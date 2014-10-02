// #Safe
/* 
 * Variant of Alex's bitcounters reduced to two bit.
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-09-28
 */
var x, y, z: bool;

procedure main() 
modifies x, y, z;
{

	x := false;
//     y := true;
	
	while(z == false) {
		if (*) {
			z := true;
		} else {
			x := true;
		}
		if (y == true) {
                z := false;
		}

	}
	assert (!x);
}