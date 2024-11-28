//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Two threads, where one increments the value of x by c for n iterations of the nested loop (which runs n times)
 *       and the other decrements the value of x by c for n*n iterations.
 *
 * Optimal schedules would be: not sure yet (we have to think about it)
 *
 */
var n, x, c: int;

procedure ULTIMATE.start()
modifies x;
{
  assume x == 0;
  assume 0 < n;

  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;

  assert x == 0;
}

procedure thread1()
modifies x;
{
  var i, j : int;
  i := 0;

  while (i < n)
  {
    j := 0;
    while (j < n)
    {
      x := x + c;
      j := j + 1;
    }
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var k : int;
  k := 0;

  while (k < n * n)
  {
    x := x - c;
    k := k + 1;
  }
}
