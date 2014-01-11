//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;

implementation main() returns ()
{
  assume a[0] == 23;
  a[a[1]] := 42;
  assert a[1] == 0 || a[0] == 23;
}

procedure main() returns ();
  modifies a;

