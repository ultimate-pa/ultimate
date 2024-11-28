//#Safe
/*
 * Author: Dominik Klumpp
 *
 * Idea: Two threads, where one increments the value of x by 2*c for m iterations, and then by c for the remaining n-m iterations,
 *       while the other decrements the value of x by c for n+k iterations.
 *
 * The optimal schedules have a prefix of the form (t1 t2 t2)* until the first time that thread1 takes the "else" branch inside the loop,
 * followed by (t1 t2)*, where t1, t2 stands for an iteration of the respective while-loop.
 *
 * These optimal schedules could be achieved in different ways:
 * - concatenation of orders: switch from one order to the other as soon as the "else" branch is first taken
 * - branching combination of orders: use one order each time the "then" branch is taken and another each time the "else" branch is taken.
 */
var m, n, x, c : int;

procedure ULTIMATE.start()
modifies x;
{
  assume x == 0;
  assume 0 < m && m < n;

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
    if (i < m)
    {
      x := x + 2*c;
    }
    else
    {
      x := x + c;
    }
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;

  while (j < n + m)
  {
    x := x - c;
    j := j + 1;
  }
}
