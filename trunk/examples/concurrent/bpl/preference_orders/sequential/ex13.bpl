///#Safe
/*
 * Author: Marcel Ebbinghaus, Emma Bach
 *
 * Idea: Two threads, where one increments the value of x by c for n iterations, then by 2*c for another n iterations, then by 3*c for another n iterations.
 *       and the other decrements the value of x by c for 3n iterations.
 *
 * The optimal schedules would have a prefix of the form (t1 t2)^* followed, once thread1 exits its first loop, by (t1 t2 t2)*, followed by (t1 t2 t2 t2)* once thread1 exits the second loop.
 *       where t1, t2 stands for an iteration of the respective while-loop. Since we need to "switch" our order twice, we need to apply the sequential operator twice.
 *
 */
var n, x, c: int;
var i, j : int;

procedure ULTIMATE.start()
modifies x, i, j;
{
  assume x == 0;

  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;

  assert x == 0;
}

procedure thread1()
modifies x, i;
{
  i := 0;
  while (i < n)
  {
    x := x + c;
    i := i + 1;
  }

  i := 0;
  while (i < n)
  {
    x := x + 2 * c;
    i := i + 1;
  }

  i := 0;
  while (i < n)
  {
    x := x + 3 * c;
    i := i + 1;
  }
}

procedure thread2()
modifies x, j;
{
  j := 0;

  while (j < 6 * n)
  {
    x := x - c;
    j := j + 1;
  }
}
