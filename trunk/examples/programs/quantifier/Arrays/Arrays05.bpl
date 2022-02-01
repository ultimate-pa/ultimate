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
  if (a[0] == 1) {
    assert(a[0] == 1);
  } else if (a[1] == 2) {
    assert(a[1] == 2);
  } else if (a[2] == 3) {
    assert(a[2] == 3);
  } else if (a[3] == 4) {
    assert(a[3] == 4);
  } else if (a[4] == 1) {
    assert(a[4] == 1);
  }
}

