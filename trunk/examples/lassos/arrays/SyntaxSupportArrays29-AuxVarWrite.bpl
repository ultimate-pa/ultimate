//#rTerminationDerivable
/*
 * Date: 2016-10-14
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

var i, j : int;
var a : [int] int;

procedure main() returns ()
modifies a, i;
{
  assume a[j] > 0;
  havoc i;
  a[i] := 1;
  havoc i;
  while (a[j] > 0) {
    a[j] := a[j] - 1;
  }
}
