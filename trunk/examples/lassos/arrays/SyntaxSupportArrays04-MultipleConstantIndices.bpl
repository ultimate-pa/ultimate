//#rNonTerminationDerivable
/*
 * Date: 2014-06-01
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */
var a : [int] int;
var b : [int] int;
var x : int;

procedure main() returns ()
modifies a, b;
{
  assume true;
  while (a[2] >= 0) {
    a[2] := a[2] - 1;
    a[1+1] := x;
  }
}

