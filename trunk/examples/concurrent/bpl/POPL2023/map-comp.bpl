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
  assume 0 <= k && k < N;

  B := A;

  fork 1     thread1();
  fork 2,2   thread2();
  fork 3,3,3 thread3();
  join 1;
  join 2,2;
  join 3,3,3;

  assert A[k] == B[k];
}

procedure thread1()
modifies A;
{
  var i : int;

  i := 0;
  while (i < N) {
    A[i] := A[i] + 1;
    i := i + 1;
  }
}

procedure thread2()
modifies A;
{
  var i : int;

  i := 0;
  while (i < N) {
    A[i] := A[i] + 2;
    i := i + 1;
  }
}

procedure thread3()
modifies B;
{
  var i : int;

  i := 0;
  while (i < N) {
    B[i] := B[i] + 3;
    i := i + 1;
  }
}
