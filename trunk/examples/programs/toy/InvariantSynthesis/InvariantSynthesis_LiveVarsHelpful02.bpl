//#Safe
/* Date: 2017-01-10
 * Author: musab@informatik.uni-freiburg.de
 * 
 * An example for demonstrating the usefulness of live variables.
 */

var a, x, y, z, n, m, j, k : int;

procedure main() returns ()
modifies a, x, y, z;
{
  y := a - 1;
  z := x + 1;
  a := z + 2;
  z := 42;
  x := z + 1;
  y := z + 2;
  while (x <= 0 || y <= 0) {
	if (x <= y) {
		x := x + 2;
	} else {
		y := y + 2;
	}
	z := z + 1;
  }
  x := 0;
  y := x;
  while ( y >= 0 ) {
	  x := x + 1;
	  if (x >= 10) {
		  y := y - 1;
	  }
  }
  assert(x >= 0 && z >= 0);
}


