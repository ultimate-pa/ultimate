//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B : [int]int;
var N : int;

function relU(x : int) returns (int) { if x < 0 then 0 else x }

procedure ULTIMATE.start()
modifies A, B;
{
  var m, result : int;
  assume 0 <= m && m < N;

  fork 1     thread1();
  fork 2,2   thread2();
  fork 3,3,3 thread3();
  join 1;
  join 2,2 assign result;
  join 3,3,3;

  assert A[m] > 0 ==> result >= 1;
}

// map A relU
procedure thread1()
modifies A;
{
  var i : int;

  i := 0;
  while (i < N) {
  atomic {
    A[i] := relU(A[i]);
    i := i + 1;
    }
  }
}

// count number of indices with positive value in A and B
procedure thread2() returns (cnt : int)
{
  var j : int;

  cnt := 0;

  j := 0;
  while (j < N) {
   atomic {
    if (A[j] > 0) {
      cnt := cnt + 1;
    }
    if (B[j] > 0) {
      cnt := cnt + 1;
    }

    j := j + 1;
    }
  }
}

procedure thread3()
modifies B;
{
  var k : int;

  k := 0;
  while (k < N) {
  atomic {
    B[k] := k;
    k := k + 1;
    }
  }
}
