//#rNonTermination
/*
 * Date: 16.06.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x: int;
procedure main() returns ()
modifies x;
{
  assume true;
  while (*) {
    if (*) {
      assume(true);
      x := x - 1;
    } else {
      assume(x>= 0);
      x := x - 1;
    }
  }
}

