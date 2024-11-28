//#Safe
/*
 * Author: Dominik Klumpp
 *
 * Idea: Two threads, where one increments the value of x by 2*c in odd-numbered iterations (n/2 times) and by c otherwise,
 *       and the other decrements the value of x by 1 n+n/2 times.
 *
 * The optimal schedules would be (t1 t2 t1 t2 t2)* where t1, t2 stands for an iteration of the respective while-loop.
 * The idea is to combine an order with minimal schedules (t1 t2)* and one with minimal schedules (t1 t2 t2)*
 * and switch back and forth between them depending on the branch thread1 takes in each iteration.
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
    if (i % 2 != 0)
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

  while (j < n + n/2)
  {
    x := x - c;
    j := j + 1;
  }
}
