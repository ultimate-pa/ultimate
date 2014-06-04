//#rTerminationDerivable
/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[0]) = a[0]
 *
 */
var a : [int] int;
var b : [int] int;
var k : int;

procedure main() returns ()
modifies a, k;
{
  assume true;
  while (a[k] >= 0 && k >= 0) {
    if (*) {
      k := k - 1;
    } else {
      a[k] := a[k] - 1;
    }
  }
}

