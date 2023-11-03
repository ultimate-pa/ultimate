//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A, B: [int]int;
var k : int;
var N : int;

procedure ULTIMATE.start()
modifies A, B;
{
  var x : int;

  B := A;
  assume 0 <= k && k < N;
  x := A[k];

  fork 1   thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  assert A[k] == x;
}

procedure thread1()
modifies A;
{
  var i : int;

  i := 0;
  while (i < N) {
    A[i] := A[i] + 1;
    //assert B[i] <= A[i] && A[i] <= B[i] + 1;
    i := i + 1;
  }
}

procedure thread2()
modifies A;
{
  var i : int;

  i := 0;
  while (i < N) {
    A[i] := A[i] - 1;
    //assert B[i] - 1 <= A[i] && A[i] <= B[i];
    i := i + 1;
  }
}
