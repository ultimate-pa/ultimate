//#Safe
/* Date: 2017-05-07
 * Author: enkei@informatik.uni-freiburg.de
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  x:=9;
  while (x < 100 && x > 0) {
    x := x + 5;
  }
  assert(x  == 104);
}


