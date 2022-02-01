//#Safe
/* Date: 2017-01-10
 * Author: musab@informatik.uni-freiburg.de
 * 
 * An example for demonstrating the usefulness of live variables.
 */

var x, y, z: int;

procedure main() returns ()
modifies x, y, z;
{
  z := 42;
  x := z + 1;
  y := z + 2;
  while (x <= 0 || y <= 0) {
	if (x <= y) {
		x := x + 2;
	} else {
		y := y + 2;
	}
  }
  assert(42 == z);
}


