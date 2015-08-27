//#rTerminationDerivable
/*
 * Date: 2015-07-15
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */
type myType;
var x,y,z : myType;

procedure main() returns ()
modifies x,y,z;
{
  y := x;
  while (x != z) {
    z := y;
  }
}

