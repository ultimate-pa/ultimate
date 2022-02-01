//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 26.10.2013

var a : [int] int;
var x, y : int;
var i, j : int;


implementation main() returns ()
{
  assume a[i] + a[j] == 22;
  x := a[i];
  y := a[j];
  assert x + y == 22;
}

procedure main() returns ();
  modifies a, x, y;

