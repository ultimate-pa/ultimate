//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B : [int]int;
var N : int;
var i : int;

function relU(x : int) returns (int) { if x < 0 then 0 else x }

procedure ULTIMATE.start()
modifies A, B, i;
{
  var m, result : int;
  assume 0 <= m && m < N;
  
  i := 0;

  fork 1     thread1();
  fork 4,4,4,4     thread1();
  fork 5,5,5,5,5     thread1();
  fork 6,6,6,6,6,6     thread1();
  fork 2,2   thread2();
  fork 3,3,3 thread3();
  join 1;
  join 4,4,4,4;
  join 5,5,5,5,5;
  join 6,6,6,6,6,6;
  join 2,2 assign result;
  join 3,3,3;

  assert (result >= 1 ==> A[m] > 0 && B[m] > 0);
}

// map A relU
procedure thread1()
modifies A, i;
{
  while (*) {
    havoc i;
    if (0 <= i && i < N) {
      A[i] := relU(A[i]);
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
    if (A[j] > 0 && B[j] > 0) {
      cnt := cnt + 1;
    }
    if (B[j] > 0) {
      cnt := cnt + 1;
    }

    j := j + 1;
  }
}

procedure thread3()
modifies B;
{
  var k : int;

  
  while (*) {
    havoc k;
    if (0 <= k && k < N) {
    B[k] := k;
    }
  }
}
