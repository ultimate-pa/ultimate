//#Safe
/*
 * Author: Emma Bach
 *
 * Idea: Four threads, where the first increments the value of x by c for 4*n iterations
 *       the second increments the value of y by 2*c for 2*n iterations
 *       the third increments the value of z by 4*c for n iterations 
 *       and the fourth decrements the value of x, y and z by c for 4n iterations.
 *
 * The optimal schedues would be some combination of (t1 t4)*, (t2 t4 t4)*, and (t3 t4 t4 t4 t4), so something like (t1 t1 t1 t1 t2 t2 t3 t4 t4 t4 t4)*
 *       where t1, t2, t3, t4 stand for an iteration of the respective while-loop.
 *
 */
var n, x, y, z, c: int;

procedure ULTIMATE.start()
modifies x, y, z;
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
modifies y;
{
  var i : int;
  i := 0;

  while (i < 4*n)
  {
    i := i + 1;
    y := y + c;
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
modifies x,y,z;
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
