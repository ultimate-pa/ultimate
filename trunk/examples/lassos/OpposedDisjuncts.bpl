//#rNonTermination
/*
 * Date: 03.05.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Each disjunct is terminating but the whole program does not terminate.
 *
 */

procedure main() returns ()
{
  var x, y, z: int;
  y := 23;
  z := 42;
  while (x >= 0) {
    if (*) {
      x := x - y;
      y := y + 1;
      z := z - 1;
    } else {
      x := x - z;
      y := y - 1;
      z := z + 1;
    }
  }
}

