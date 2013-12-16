//#rTerminationDerivable
/*
 * Date: 09.07.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 */

var x: int;
var b: bool;

procedure main() returns (x: int, y: int)
modifies x, b;
{
  while (true) {
    b := (x >= 0);
    assume b;
    x := x - 1;
  }
}
