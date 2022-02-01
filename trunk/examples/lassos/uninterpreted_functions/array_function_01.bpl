//#rTerminationDerivable
/*
 * Date: 2016-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */
 
function f(int) returns([int] int);

var a : [int] int;
var i : int;

procedure main() returns ()
modifies a;
{
  assume f(i)[i] > 0;
  while (a[i] > 0) {
    a[i] := a[i] - f(i)[i];
  }
}