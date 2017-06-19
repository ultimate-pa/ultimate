//#Safe
/* Date: 2017-05-07
 * Author: enkei@informatik.uni-freiburg.de
 */

var x,y : int;

procedure main() returns ()
modifies x,y;
{
  x:=0;
  y:=10;
  while (x < y) {
    x := y + 1;
  }
  assert(x>=6 || x<=-5 || y <= 2);
}


