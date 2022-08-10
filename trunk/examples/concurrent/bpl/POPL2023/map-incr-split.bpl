//#Safe
/*
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A: [int]int;
var k : int;
var N : int;

procedure ULTIMATE.start()
modifies A;
{
  var x : int;

  assume 0 <= k && k < 2*N;
  x := A[k];

  fork 1   thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  assert A[k] == x + 1;
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

  i := N;
  while (i < 2 * N) {
    A[i] := A[i] + 1;
    i := i + 1;
  }
}
