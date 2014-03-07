//#Unsafe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 29.08.2013

var a : [int] int;

implementation main() returns ()
{
  assume a[a[0]] == 23;
  a[0] := 42;
  assert a[a[0]] == 23;
}

procedure main() returns ();
  modifies a;

