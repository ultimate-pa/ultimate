//#rTerminationDerivable
/*
 * Date: 2016-10-20
 * Author: schuessf@informatik.uni-freiburg.de
 *
 */
 
function f(int) returns([int] int);

var a : [int] int;
var i, j, x : int;

procedure main() returns ()
modifies a, x;
{
  assume i == j;
  a[j] := 5;
  assume f(i) == a;
  while (x > 0) {
    x := x - f(i)[i];
  }
}