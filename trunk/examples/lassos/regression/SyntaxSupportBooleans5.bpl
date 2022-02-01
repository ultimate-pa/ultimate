//#rTerminationDerivable
/*
 * Date: 2014-03-22
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans.
 * f(x,b) = (b ? 1 : 0) + x is a ranking function
 *
 */

procedure proc() returns ()
{
  var b: bool;
  var x: int;
  while (x >= 0 && b) {
    if (*) {
      x := x - 1;
    } else {
      b := false;
    }
  }
}
