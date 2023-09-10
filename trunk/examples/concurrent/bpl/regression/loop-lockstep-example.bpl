//#Safe

/*
 * Example demonstrating benefit of loop-lockstep preference order in Partial Order Reduction.
 *
 * The simplest reduction to prove correct is the one where every complete iteration of thread1
 * is followed by a complete iteration of thread2; this reduction requires only the invariant
 * "x == 0 /\ i == j".
 *
 */

var x, y, N : int;

procedure thread1()
modifies x;
{
  var i : int;
  i := 0;
  while (i < N) {
    x := x + 1;
    x := x + 1;
    x := x + 1;
    x := x + 1;
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;
  while (j < N) {
    x := x - 4;
    j := j + 1;
  }
}

procedure ULTIMATE.start()
modifies x,y;
{
  x := 0;
  fork 1 thread1();
  fork 2,2 thread2();
  join 1;
  join 2,2;
  assert x == 0;
}
