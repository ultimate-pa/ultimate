//#rTerminationDerivable
/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[0], b[2]) = a[0]
 *
 */
var a : [int] int;
var b : [int] int;

procedure main() returns ()
modifies a, b;
{
  assume true;
  while (a[0] >= 0) {
    b[2] := a[0];
    a[0] := b[2];
    a[0] := a[0] - 1;
  }
}

