//#rTerminationDerivable
/*
 * Date: 2016-11-03
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int] int;
var i : int;

procedure main() returns ()
modifies a;
{
  assume a == b;
  a := b;
  while (a[i] > 0) {
    a[i] := a[i] - 1;
  }
}