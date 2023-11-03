//#rNonTerminationDerivable
/*
 * 
 * Author: Matthias Heizmann
 * Date: 2015-12-20
 */

procedure main() returns ()
{
  var x, y, z: real;
  while (x < 0.0 && y < 0.0 && z < 0.0 && z < 7.0*y && y < 11.0*x) {
    x := 2.0*x;
    y := 3.0*y;
    z := 5.0*z;
  }
}

