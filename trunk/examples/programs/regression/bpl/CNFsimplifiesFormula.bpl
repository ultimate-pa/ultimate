//#Safe
/*
 * Conversion to CNF already simplifies the large formula to a1.
 * Some algorithms that do not expect simplification from CNF converion might
 * miss the other variables.
 * Date: 2014-08-02
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var a1, a2, a3, b1, b2, b3, c1, c2, c3: bool;

procedure main() returns ()
modifies a1, a2, a3, b1, b2, b3, c1, c2, c3;
{
	var x : int;
  if (*) {
    assume(true);
  } else {
    assume(true);
  }
  assume(x >= 23);
  while (*) {
      assume(true);
    }
  assert(x >= 23);
}
