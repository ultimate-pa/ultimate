//#rTerminationDerivable
/*
 * Reveals bug in revision 7559. Our Template should not be able to
 * derive this ranking function.
 * 
 * Date: 29.11.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y) = 0
 * provided with the supporting invariant y >= 0.
 * 
 */

procedure Dhaka(c: int) returns ()
{
  var x,y : int;
  y := 0;
  while (y < 0) {
    x := x + 1;
  }
}

