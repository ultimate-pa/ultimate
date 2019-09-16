//#rTerminationDerivable
/*
 * Date: 18.11.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * Variable x bounded by variable d
 *
 */

procedure Mysore2(y: int) returns (x: int)
{
  var b, d:int;
  assume(d >= 1);
  while (x >= b) {
     x := x - d;
     d := d + 2;
  }
}
