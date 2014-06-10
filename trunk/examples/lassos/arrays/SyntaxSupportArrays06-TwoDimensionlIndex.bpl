//#rTerminationDerivable
/*
 * Date: 2012-05-31
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[0,0]) = a[0,0]
 *
 */
var a : [int, int] int;

procedure main() returns ()
modifies a;
{
  assume true;
  while (a[0,0] >= 0) {
    a[0,0] := a[0,0] - 1;
  }
}

