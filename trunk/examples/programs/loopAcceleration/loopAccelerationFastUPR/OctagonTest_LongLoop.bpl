//#Safe
/* Date: 2017-05-07
 * Author: enkei@informatik.uni-freiburg.de
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  assume(x < 100);
  y:= 0;
  while (x < 100000000000) {
    x := x + 1;
    y := y + 2;
  }
  
  while (x > 0) {
    x := x - 1;
    y := y + 2;
  }
  assert(x > -1 || x<=2 || y <= 2);
}


