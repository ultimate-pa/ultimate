//#Safe
/*
 * Date: 23.09.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

var x:int;
const hundred:int;

procedure main()
modifies x;
{
  if(hundred > 0)
  {
	  x := 0;
	  while (hundred > x) {
		x := x + 1;
	  }

	  assert(x == hundred);
  }
}