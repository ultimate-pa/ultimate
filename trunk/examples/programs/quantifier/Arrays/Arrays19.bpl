/* Author: musab@informatik.uni-freiburg.de
*/
var a : [int] int;
var b : [int] int;

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
  a[11] := 12;
  a[12] := 13;
  a[13] := 14;
  a[14] := 15;
  a[15] := 16;
  a[16] := 17;
  a[17] := 18;
  a[18] := 18;
  a[19] := 110;
  j := 0; 
  while (j < 20) {
    b[j] := a[j] - 1;
    j := j + 1;
  }
  j := 0;
  while (j < 20) {
    assert(b[j] == j);
    j := j + 1;
  }
}


