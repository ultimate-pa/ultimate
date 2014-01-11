//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;
var i : int;


implementation main() returns ()
{
  assume a[0] == 23;
  a[0] := a[i];
  assert i != 0 || a[0] == 23;
}

procedure main() returns ();
  modifies a;

