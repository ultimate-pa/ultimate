//#Safe
/* Author: musab@informatik.uni-freiburg.de
*/
var a : [int] int;

procedure main() returns();
modifies a;

implementation main() returns()
{
  var i : int;
  i := 0;
  a[i] := 1;
  i := i + 1;
  a[i] := 2;
  i := i + 1;
  a[i] := 3;
  i := i + 1;
  a[i] := 4;
  i := i + 1;
  a[i] := 5;
  if (i < 10) {
     assert(a[i] < 10);
  }
  if (a[i] == 1) {
    assert(a[i] == 1);
  } else if (a[1] == 2) {
    assert(a[1] == 2);
  } else if (a[i] == 3) {
    assert(a[i] == 3);
  } else if (a[3] == 4) {
    assert(a[3] == 4);
  } else if (a[4] == 1) {
    assert(a[4] == 1);
  }
}

