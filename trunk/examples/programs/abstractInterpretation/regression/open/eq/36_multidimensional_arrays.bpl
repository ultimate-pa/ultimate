//#Safe
/* 
 *
 * Author: Alexander Nutz
 */

procedure main();

implementation main() {
  var a1, b1 : [int] int;
  var a2, b2 : [int] [int] int;
  var a3, b3 : [int] [int] [int] int;
  var a4, b4 : [int] [int] [int] [int] int;

  var i, j, k, l, m, n, p, q : int;
  var i1, i2, i3, i4 : int;
  var j1, j2, j3, j4 : int;

  a3[i1][i2][i3] := 3;
  assert a3[i1][i2][i3] == 3;


  a1[j] := 4;
  a2 := a2[i:=a1];
  assert a2[i][j] == 4;


  a3 := b3[j1][j2][j3 := 7];
  assert a3[j1][j2][j3] == 7;
  assume j1 != i1;
  assert a3[j1] == b3[j1];
  assert a3[j1][j2] == b3[j1][j2];
  assert a3[j1][j2][j3] == b3[j1][j2][j3];
}


