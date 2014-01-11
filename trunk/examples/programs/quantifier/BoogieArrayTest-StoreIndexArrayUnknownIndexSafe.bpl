//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;
var i : int;


implementation main() returns ()
{
  assume a[0] == 0;
  a[a[i]] := 42;
  assert a[i] == 42 || a[i] == 0 || a[0] == 0;
}

procedure main() returns ();
  modifies a;

