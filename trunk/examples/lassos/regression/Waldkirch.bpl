//#rTerminationDerivable
/*
 * Date: 18.02.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 */
var x : int;

procedure Waldkirch() returns ()
modifies x;
{
  assume true;
  while (x >= 0) {
    x := x - 1;
  }
}

