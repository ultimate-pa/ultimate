//#Safe
/* Date: 2015-04-28
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Most(?) simple program for which a disjunctive loop invariant is needed.
 * 
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  assume(x>=9 || x<=-8);
  while (*) {
    x := 2*x;
  }
  assert(x>=6 || x<=-5);
}


