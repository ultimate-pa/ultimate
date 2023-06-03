//#rTermination
/*
 * Date: 10.07.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 */

var x: int;
var b: bool;

procedure main() returns (x: int, y: int)
modifies x, b;
{
  while (true) {
    assume b;
    havoc b;
    x := x - 1;
    b := (x >= 0);
  }
}
