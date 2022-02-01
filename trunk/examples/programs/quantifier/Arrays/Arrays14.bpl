//#Safe
/* Author: musab@informatik.uni-freiburg.de
*/
var a : [int] int;

procedure main() returns();
modifies a;

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
  a[11] := 12;
  a[12] := 13;
  a[13] := 14;
  a[14] := 15;
  a[15] := 16;
  a[16] := 17;
  a[17] := 18;
  a[18] := 18;
  a[19] := 110;
  if (i < 10 && i >= 0) {
     assert(a[i] <= 10);
  } else {
    i := 0;
    assert(a[i] == 1);
    i := i + 1;
    assert(a[i] == 2);
  }
  if (j < 10 && j >= 0) {
     assert(a[j] <= 10);
  } else {
    j := 0;
    assert(a[j] == 1);
    i := j + 1;
    assert(a[i] == 2);
  }
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
}


