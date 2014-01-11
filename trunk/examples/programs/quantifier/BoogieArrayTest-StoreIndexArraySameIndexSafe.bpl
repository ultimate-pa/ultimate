//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;

implementation main() returns ()
{
  assume a[0] == 23;
  a[a[0]] := 24;
  assert a[0] == 23 && a[23] == 24;
}

procedure main() returns ();
  modifies a;

