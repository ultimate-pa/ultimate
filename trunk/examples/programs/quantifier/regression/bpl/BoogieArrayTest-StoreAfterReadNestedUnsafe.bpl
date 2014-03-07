//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;

implementation main() returns ()
{
  assume a[0] != 0;
  assume a[1] != 0;
  assume a[a[0]] != a[a[1]];
  a[0] := 42;
  assert a[a[0]] != a[a[1]];
}

procedure main() returns ();
  modifies a;

