// #Unsafe
/* 
 * Bug in r12467. SSA construct used default constants for auxVars (instead of 
 * fresh constant). 
 * If TransFormula occurs twice in trace, same constant is used.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2014-09-28
 */
var x, y, z: bool;

procedure main() 
modifies x, y, z;
{

	x := false;
	
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