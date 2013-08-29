//#mSafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;
var i : int;

implementation main() returns ()
{
  assume a[a[0]] == 23;
  a[i] := 42;
  assert a[0] == i || i == 0 || a[a[0]] == 23;
}

procedure main() returns ();
  modifies a;

