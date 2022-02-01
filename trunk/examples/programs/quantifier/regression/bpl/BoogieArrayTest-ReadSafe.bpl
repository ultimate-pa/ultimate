//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 24.10.2013

var a : [int] int;
var x, y : int;
var i, j : int;


implementation main() returns ()
{
  x := a[i];
  y := a[j];
  if (i == j) {
	assert x == y;
  }
}

procedure main() returns ();
  modifies a, x, y;

