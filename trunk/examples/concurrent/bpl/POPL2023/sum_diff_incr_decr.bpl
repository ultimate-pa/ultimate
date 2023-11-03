//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B, C, D : [int]int;
var N : int;

procedure T1()
modifies A, B;
{
  var i : int;

  i := 0;
  while (i < N) {
    atomic {
      A[i] := A[i] + 1;
      B[i] := B[i] - 1;
    }
    i := i + 1;
  }
}

procedure T2()
modifies C, D;
{
  var j : int;

  j := 0;
  while (j < N) { // invariant (j < m \/ C[m] == A[m] + B[m]), stable under update in T1
    C[j] := A[j] + B[j]; // should commute concretely against update in T1
    D[j] := A[j] - B[j]; // should commute abstractly against update in T1, assuming A and B are simplified away here
    j := j + 1;
  }
}

procedure ULTIMATE.start()
modifies A, B, C, D;
{
  var m : int;

  assume 0 <= m && m < N;

  fork 1 T1();
  fork 2,2 T2();
  join 1;
  join 2,2;

  assert C[m] == A[m] + B[m];
}
