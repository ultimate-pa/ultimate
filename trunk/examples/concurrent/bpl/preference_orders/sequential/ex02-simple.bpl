///#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Two threads, where one increments the value of x by c for n iterations and then by 2*c for another n iterations
 *       and the other decrements the value of x by c for 3n iterations.
 *
 * The optimal schedules would have a prefix of the form (t1 t2)^* followed, once thread1 exits its first loop, by (t1 t2 t2)*
 *       where t1, t2 stands for an iteration of the respective while-loop
 *
 */
var n, x: int;

procedure ULTIMATE.start()
modifies x;
{
  assume x == 0;

  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;

  assert x == 0;
}

procedure thread1()
modifies x;
{
  var i : int;

  i := 0;
  while (i < n)
  {
    x := x + 1;
    i := i + 1;
  }

  i := 0;
  while (i < n)
  {
    x := x + 2;
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;

  while (j < 3 * n)
  {
    x := x - 1;
    j := j + 1;
  }
}
