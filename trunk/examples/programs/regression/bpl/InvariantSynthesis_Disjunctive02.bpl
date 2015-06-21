//#Safe
/* Date: 2015-04-28
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Simple program with 2 variables for which a disjunctive loop invariant is needed.
 * 
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  assume(x>=5 || y>=5);
  while (*) {
    if (x >= 5) {
      x := x + 1;
      havoc y;
    } else {
      havoc x;
      y := y + 1;
    }
  }
  assert(x >= 0 || y >= 0);
}


