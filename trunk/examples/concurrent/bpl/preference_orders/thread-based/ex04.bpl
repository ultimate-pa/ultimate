//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Three threads, where the first increments the value of y by 2*c for n iterations
 *       the second increments the value of x by c for 2n iterations
 *       and the third decrements the value of x and y by c for 2n iterations.
 *
 * The optimal schedues would be some combination of (t1 t3 t3)* and (t2 t3)*, so something like (t1 t2 t2 t3 t3)*
 *       where t1, t2, t3 stands for an iteration of the respective while-loop.
 *
 */
var n, x, y, c: int;
var i, j: int;

procedure ULTIMATE.start()
modifies x, y, i, j;
{
  assume x == 0 && y == 0;

  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
  join 1;
  join 2;
  join 3;

  assert x == 0 && y == 0;
}

procedure thread1()
modifies y, i;
{
  var i : int;
  i := 0;

  while (i < n)
  {
    i := i + 1;
    y := y + 2*c;
  }
}

procedure thread2()
modifies x, j;
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
modifies x, y, i, j;
{
  var k : int;
  k := 0;

  while (k < 2 * n)
  {
    k := k + 1;
    x := x - c;
    y := y - c;
  }
}
