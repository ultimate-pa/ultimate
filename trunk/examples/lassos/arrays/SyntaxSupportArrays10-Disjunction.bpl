//#rTerminationDerivable
/*
 * Date: 2012-06-09
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[0]) = a[0]
 *
 */
var a : [int] int;

procedure main() returns ()
modifies a;
{
  assume true;
  while (a[0] >= 0) {
    if (*) {
      a[0] := a[0] - 1;
    } else {
      a[0] := a[1-1] - 1;
    }
  }
}

