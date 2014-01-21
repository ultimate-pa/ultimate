//#rTerminationDerivable
/*
 * Date: 18.02.2012
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(x) = x
 *
 */
var a : [int] int;

procedure Waldkirch() returns ()
modifies a;
{
  assume true;
  while (a[0] >= 0) {
    a[0] := a[0] - 1;
  }
}

