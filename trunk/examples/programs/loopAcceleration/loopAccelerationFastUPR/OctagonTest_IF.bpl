//#Safe
/* Date: 2017-05-07
 * Author: enkei@informatik.uni-freiburg.de
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  assume(x == 9);
  assume(y == 10);
  while (y < 100) {
    x := x + 1;
    if (y < x) {
    y := y + 5;
    }
  }
}


