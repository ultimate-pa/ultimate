//#rTerminationDerivable
/*
 * Date: 18.02.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure Copenhagen(c: int) returns (x: int)
{
  var y: int;
  var tmp: int;
  
  assume true;
  while (x >= 0 && y >= 0) {
    tmp := y-1;
    y := x;
    x := tmp;
  }
}

