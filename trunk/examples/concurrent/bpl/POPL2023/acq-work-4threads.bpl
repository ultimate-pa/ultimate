//#Safe
/*
 * Acquire-Work example in which two threads acquire exclusive access to some index in an array A.
 *
 * Author: Dominik Klumpp
 * Date: June 2022
 */

var A : [int]int;
var B : [int]bool;

procedure ULTIMATE.start()
modifies A, B;
{
  fork 1       thread1WithAssert(1);
  fork 2,2     thread1(2);
  fork 3,3,3   thread1(3);
  fork 4,4,4,4 thread1(4);
  join 1;
  join 2,2;
  join 3,3,3;
  join 4,4,4,4;
}

procedure thread1WithAssert(x : int)
modifies A, B;
{
  var i : int;
  var b : bool;

  i := 0;
  while (true) {
    call b := acquire(i);
    if (b) {
      A[i] := x;
      assert A[i] == x;
    }
    i := i + 1;
  }
}

procedure thread1(x : int)
modifies A, B;
{
  var i : int;
  var b : bool;

  i := 0;
  while (true) {
    call b := acquire(i);
    if (b) {
      A[i] := x;
    }
    i := i + 1;
  }
}

procedure acquire(i : int) returns (b : bool)
modifies B;
{
  atomic {
    b := B[i];
    if (b) {
      B[i] := false;
    }
  }
}
