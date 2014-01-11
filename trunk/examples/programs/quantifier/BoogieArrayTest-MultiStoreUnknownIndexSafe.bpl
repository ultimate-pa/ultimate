//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 23.09.2013

var a : [int] int;
var i, j, k, l, m : int;


implementation main() returns ()
{
  a[0] := 10;
  a[i] := 11;
  a[j] := 12;
  a[k] := 13;
  a[l] := 14;
  a[m] := 15;
  assert a[0] == 10 || a[0] == 11 || a[0] == 12 || a[0] == 13 || a[0] == 14 || a[0] == 15;
}

procedure main() returns ();
  modifies a;

