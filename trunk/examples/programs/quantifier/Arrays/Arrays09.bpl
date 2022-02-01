//#Safe
/* Author: musab@informatik.uni-freiburg.de
*/
var a : [int] int;

procedure main() returns();
modifies a;

implementation main() returns()
{
  var i : int;
  var j : int;
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
  j := 0;
  a[0] := -100;
  while (j < 5) {
     assert(a[j] < 10);
     j := j + 1;
  }
  assert(a[0] == -100);
}

