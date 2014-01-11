//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;

implementation main() returns ()
{
  assume a[0] == 23;
  a[1] := a[0];
  assert a[0] == 23 && a[1] == 23;
}

procedure main() returns ();
  modifies a;

