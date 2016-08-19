//#rTerminationDerivable
/*
 * Date: 2016-08-19
 * Author: schuessf@informatik.uni-freiburg.de
 * 
 * LassoRanker can prove this using the new map-elimination
 */
 
function f(int) returns(int);

var a : [int] int;
var x, i : int;

procedure main() returns ()
modifies a;
{
  assume f(x) > 0;
  while (a[i] > 0) {
    a[i] := a[i] - f(x);
  }
}
