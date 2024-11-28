//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Two threads, where one increments the value of x by 2*c for n/2 iterations and might increment by c once if n is odd.
 *       and the other decrements the value of x by c for n iterations.
 *
 * The optimal schedules would be (t1,t2,t2)^floor(n/2) and might be followed by (t1,t2) if n is odd
 *       where t1, t2 stands for an iteration of the respective while-loop.
 *
 * The idea is to use the first order for the if-branch and the second for the else-branch.
 *
 * Note: It might be that this example can be handled with the same basic order as ex01.bpl.
 *
 */
var n, x, c: int;

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
    if (i + 1 < n)
    {
      x := x + 2 * c;
      i := i + 2;
    }
    else
    {
      x := x + c;
      i := i + 1;
    }
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;

  while (j < n)
  {
    j := j + 1;
    x := x - c;
  }
}
