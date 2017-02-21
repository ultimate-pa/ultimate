//#Safe
/* Date: 2016-02-04
 * Author: musab@informatik.uni-freiburg.de
 * Example in Figure 4 from Paper "Path Invariants" published in 2007 (D.Beyer, T.A.Henzinger, R.Majumdar).
 * 
 */

var x, y : int;

procedure main() returns ()
modifies x, y;
{
	x := 0;
	y := 50;
	while (x < 100) {
		if (x < 50) {
			x := x + 1;
		} else {
			x := x + 1;
			y := y + 1;
		}
	}
	assert (y <= 100);
	assert (y >= 100);
}


