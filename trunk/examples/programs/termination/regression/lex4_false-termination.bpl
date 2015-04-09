//#terminating
/*
 * Date: 10.11.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
var x,y,z,u: int;

procedure main()
modifies x, y, z, u;
{
  assume true;
  while (x>0 && y>0 && z>0 && u>0) {
    if (*) {
      x := x - 1;
    } else if (*) {
      havoc x;
      y := y - 1;
    } else if (*) {
      havoc x;
      havoc y;
      z := z - 1;
    } else {
      havoc x;
      havoc y;
      havoc z;
      u := u;
    }
  }
}