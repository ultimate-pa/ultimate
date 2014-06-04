//#Safe
/* Author: musab@informatik.uni-freiburg.de
*/
var a : [int] int;

procedure main() returns();
modifies a;

implementation main() returns()
{
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 4;
  a[4] := 5;
  a[5] := 6;
  a[6] := 7;
  a[7] := 8;
  a[8] := 8;
  a[9] := 10;
  assert(a[0] == 1);
}

