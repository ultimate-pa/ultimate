//#Safe
/*
 * Author: Marcel Ebbinghaus & Emma Bach
 *
 * Idea: Three threads, where the first increments the value of x by 2*c for n iterations
 *       the second increments the value of x by c for 2n iterations
 *       and the third decrements the value of x by c for 4n iterations.
 *
 * The optimal schedules would be a different combination of (t1 t3 t3)* and (t2 t3)* than in example 4,
 *       the necessary combination for this is (t1 t2 t2 t3 t3 t3 t3)*
 *       where t1, t2, t3 stands for an iteration of the respective while-loop.
 *
 * Not entirely sure this is actually formally meaningful anymore, since now the combinations (t1 t3 t3)*
 *       and (t2 t3)* on their own are no longer enough to fully "exhaust" the while loop in thread 3.
 */
var n, x, c: int;

procedure ULTIMATE.start()
modifies x;
{
  assume x == 0;

  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
  join 1;
  join 2;
  join 3;

  assert x == 0;
}

procedure thread1()
modifies x;
{
  var i : int;
  i := 0;

  while (i < n)
  {
    i := i + 1;
    x := x + 2*c;
  }
}

procedure thread2()
modifies x;
{
  var j : int;
  j := 0;

  while (j < 2 * n)
  {
    j := j + 1;
    x := x + c;
  }
}

procedure thread3()
modifies x;
{
  var k : int;
  k := 0;

  while (k < 4 * n)
  {
    k := k + 1;
    x := x - c;
  }
}
