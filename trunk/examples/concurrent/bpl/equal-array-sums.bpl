//#Safe
/*
 * Author: Dominik Klumpp
 * Date: 2022-02-10
 *
 * This is the example from our SV-COMP'22 paper "Ultimate GemCutter and the Axes of Generalization".
 * POR can aggressively reduce this program, as all actions of thread1 and thread2 commute.
 * When combined with the LoopLockstep preference order, this yields significant proof simplification.
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
