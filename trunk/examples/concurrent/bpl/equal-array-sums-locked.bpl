//#Safe
/*
 * Author: Dominik Klumpp
 * Date: 2022-02-10
 *
 * This is an adaptation of the example from our SV-COMP'22 paper "Ultimate GemCutter and the Axes of Generalization".
 * This version adds additional, unnecessary locking calls in the bodies of the loops in thread1 resp. thread2.
 * These locking calls do not commute against each other, and hence POR cannot reduce as well.
 * As a result, the proof simplification described in the paper is not possible.
 *
 * However, when POR is combined with (global) variable abstraction, the lock variable is abstracted away.
 * Thus, the (abstracted) locking calls commute, simplification is once again possible and the verification terminates quickly
 * (currently 5 iterations in < 12 seconds) when using the LoopLockstep preference order.
 *
 */
var m : bool;
var A : [int]int;
var x, y, n : int;

procedure ULTIMATE.start()
modifies m, x, y;
{
  x := 0;
  y := 0;

  fork 1   thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;

  assert x == y;
}

procedure thread1()
modifies m, x;
{
  var i : int;

  i := 0;
  while (i < n) {
    call lock();
    x := x + A[i];
    call unlock();
    i := i + 1;
  }
}

procedure thread2()
modifies m, y;
{
  var j : int;

  j := 0;
  while (j < n) {
    call lock();
    y := y + A[j];
    call unlock();
    j := j + 1;
  }
}

procedure lock()
modifies m;
{
  atomic { assume m == false; m := true; }
}

procedure unlock()
modifies m;
{
  m := false;
}
