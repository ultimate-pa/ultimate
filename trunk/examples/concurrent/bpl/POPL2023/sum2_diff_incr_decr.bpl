//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B, C, D : [int]int;
var N : int;

procedure T1() returns (sum : int)
modifies A, B;
{
  var i : int;

  i := 0;
  sum := 0;
  while (i < N) {
    atomic {
      A[i] := A[i] + 1;
      B[i] := B[i] - 1;
    }
    sum := sum + A[i] + B[i];
    i := i + 1;
  }
}

procedure T2() returns (sum : int)
modifies D;
{
  var j : int;

  j := 0;
  sum := 0;
  while (j < N) {
    sum  := sum + A[j] + B[j]; // should commute concretely against update in T1 [should not commute with lightweight-abstract]
    D[j] := A[j] - B[j];       // should commute abstractly against update in T1, assuming A and B are simplified away in the abstraction here; does not commute concretely
    j := j + 1;
  }
}

procedure ULTIMATE.start()
modifies A, B, D;
{
  var sum1, sum2 : int;

  fork 1 T1();
  fork 2,2 T2();
  join 1 assign sum1;
  join 2,2 assign sum2;

  assert sum1 == sum2;
}
