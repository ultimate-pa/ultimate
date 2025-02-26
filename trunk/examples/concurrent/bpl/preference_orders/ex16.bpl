///#Safe
/*
 * Author: Dominik Klumpp
 *
 * Idea: Three threads, where the first two each increment x by c for (overall, across both threads) n iterations, and a third thread that decrements x by c for n iterations.
 *
 * The optimal schedules would have the form ((t1 + t2) t3)*,
 *       where t1, t2, t3 stands for an iteration of the respective while-loop.
 *
 * The idea is that our operators should be flexible enough to understand that an occurrence of (t1 + t2) must be matched by an occurrence of t3,
 * without needing to distinguish whether it was thread1 or thread2 that performed an iteration.
 *
 * Maybe possible with sequential composition: (t3 t1)* until t1 exits its loop, then (t3 t2)*
 */
var n, x, c, i : int;

procedure ULTIMATE.start()
modifies x, i;
{
  assume x == 0;
  assume i == 0;

  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
  join 1;
  join 2;
  join 3;

  assert x == 0;
}

procedure thread1()
modifies x, i;
{
  while (*)
  {
    atomic {
      assume i < n;
      i := i + 1;
    }
    x := x + c;
  }
  assume i >= n;
}

procedure thread2()
modifies x, i;
{
  while (*)
  {
    atomic {
      assume i < n;
      i := i + 1;
    }
    x := x + c;
  }
  assume i >= n;
}

procedure thread3()
modifies x;
{
  var j : int;
  j := 0;

  while (j < n)
  {
    x := x - c;
    j := j + 1;
  }
}
