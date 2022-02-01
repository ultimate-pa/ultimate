//#Safe
/* Date: 2017-01-19
 * Author: musab@informatik.uni-freiburg.de
 * 
 * A file for demonstrating the usefulness of weakest precondition.
 * 
 */

var a, x, y, z : int;

procedure main() returns ()
modifies a, x, y, z;
{
  a := 42;
  z := 0;
  y := 0;
  x := 5;
  while (x > 0) {
	if (y >= 0 && z >= 0 && a >= 0) {
		x := x - 1;
	} else {
		x := -42;
	}
	if (x < 0) {
		y := -10;
		a := y;
		z := a;
	}
  }
  assert (y >= 0 && z >= 0 && a >= 0);
}


