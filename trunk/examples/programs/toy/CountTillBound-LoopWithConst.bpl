//#Safe
/*
 * Date: 23.09.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x:int;
const hundred:int;
axiom hundred > 0;

procedure main()
modifies x;
{
  x := 0;
  while (x < hundred) {
    x := x + 1;
  }

  assert(x == hundred);
}