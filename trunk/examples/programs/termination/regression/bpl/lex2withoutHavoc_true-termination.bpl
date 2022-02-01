//#terminating
/*
 * Date: 10.11.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y: int;

procedure main()
modifies x, y;
{
  assume true;
  while (x>0 && y>0) {
    if (*) {
      x := x - 1;
    } else {
      x := x + 1;
      y := y - 1;
    }
  }
}