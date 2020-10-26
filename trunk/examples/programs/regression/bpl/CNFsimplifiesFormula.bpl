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
  if (*) {
    assume(true);
  } else {
    assume(true);
  }
  assume((a1 && a2 && a3) || (a1 && a2 && b3) || a1 || (a1 && a2 && c3));
  while (*) {
      assume(true);
    }
  assert(a1);
}
