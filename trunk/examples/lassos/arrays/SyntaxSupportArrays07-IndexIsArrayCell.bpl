//#rTerminationDerivable
/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Ranking function: f(a[b[23]], b[23]) = a[b[23]]
 *
 */
var a : [int] int;
var b : [int] int;

procedure main() returns ()
modifies a;
{
  assume true;
  while (a[b[23]] >= 0) {
    a[b[23]] := a[b[23]] - 1;
  }
}

