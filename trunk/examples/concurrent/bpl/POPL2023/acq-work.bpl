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
  fork 1   thread1WithAssert(1);
  fork 2,2 thread1(2);
  join 1;
  join 2,2;
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
  var j : int;
  var b : bool;

  j := 0;
  while (true) {
    call b := acquire(j);
    if (b) {
      A[j] := x;
    }
    j := j + 1;
  }
}

procedure acquire(k : int) returns (b : bool)
modifies B;
{
  atomic {
    b := B[k];
    if (b) {
      B[k] := false;
    }
  }
}
