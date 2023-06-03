//#rTerminationDerivable
/*
 * Date: 06.04.2012
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Ranking function: f(x)=x+1048 (or x+1049 ???)
 *
 */

procedure Waldkirch(c: int) returns (x: int)
{
  var y: int;

  assume true;
  while (x >= -1048) {
    x := x - 1;
  }
}

