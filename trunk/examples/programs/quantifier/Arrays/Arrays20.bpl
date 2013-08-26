/* Author: musab@informatik.uni-freiburg.de
*/
var a : [int] int;
var b : [int] int;

procedure p2 () returns ();
modifies a;

implementation p2() returns() {
  var i : int;
  i := 0;
  while (i < 20) {
    a[i] := b[i];
    i := i + 1;
  }
}

procedure main() returns();
modifies a,b;

implementation main() returns()
{
  var i,j : int;
  a[0] := 1;
  a[1] := 2;
  a[2] := 3;
  a[3] := 4;
  a[4] := 5;
  a[5] := 6;
  a[6] := 7;
  a[7] := 8;
  a[8] := 9;
  a[9] := 10;
  a[10] := 11;
  assert(a[0] == 1);
  assert(a[1] == 2);
  assert(a[2] == 3);
  assert(a[3] == 4);
  assert(a[4] == 5);
  assert(a[5] == 6);
  assert(a[6] == 7);
  assert(a[7] == 8);
  assert(a[8] == 9);
  assert(a[10] == 11);
  assert(a[11] == 12);
  assert(a[12] == 13);
  if (i < 10 && i >= 0) {
     assert(a[i] <= 10);
  } else {
    i := 0;
    assert(a[i] == 1);
    i := i + 1;
    assert(a[i] == 2);
  }
  call p2();
  i := 0;
  while (i < 20) {
    assert(a[i] == b[i]);
  }
}



