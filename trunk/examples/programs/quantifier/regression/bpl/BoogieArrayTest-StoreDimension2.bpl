//#Safe
// Author: heizmann@informatik.uni-freiburg.de
// Date: 27.10.2013

var a : [int, int] int;
var i, j, k, l, m : int;


implementation main() returns ()
{
  a[5,7] := 10;
  a[7,8] := 23;
  assert a[5,7] == 10;
//  && a[7,8] == 23;
}

procedure main() returns ();
  modifies a;

