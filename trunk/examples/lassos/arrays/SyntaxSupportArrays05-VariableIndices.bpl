//#rTerminationDerivable
/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */
var a : [int] int;
var b : [int] int;
var i,j : int;

procedure main() returns ()
modifies a, b;
{
  assume i == j;
  while (a[i] >= 0) {
    a[j] := a[j] - 1;
  }
}

