//#rTerminationDerivable
/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[3], b[1+2], a[2+1]) = a[0]
 *
 */
var a : [int] int;
var b : [int] int;

procedure main() returns ()
modifies a, b;
{
  assume true;
  while (a[1+2] >= 0) {
    a[3] := a[2+1] - 1;
  }
}

