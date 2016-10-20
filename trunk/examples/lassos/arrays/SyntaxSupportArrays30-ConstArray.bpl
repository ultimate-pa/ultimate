//#rTerminationDerivable
/*
 * Date: 2016-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */

const a : [int] int;
var i, x : int;

procedure main() returns ()
modifies x;
{
  assume a[i] > 0;
  while (x > 0) {
    x := x - a[i];
  }
}