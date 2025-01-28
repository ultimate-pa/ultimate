//#Safe
/*
 * Author: Dominik Klumpp
 *
 * Idea: Two threads, where one nondeterministically chooses to increment the value of x by 2*c or by c until it reaches n*c,
 *       while the other decrements the value of x by c for n iterations.
 *
 * The optimal schedules would be (t1 t2 t2)* in the cases where thread1 takes the if-branch, and (t1 t2)* if thread1 takes the else branch,
 * where t1, t2 stands for an iteration of the respective while-loop.
 */
var n, x, c : int;
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
  
  if (*)
  {
    while (i+1 < n)
    {
      x := x + 2*c;
      i := i + 2;
    }
    if (i < n)
    {
      x := x + c;
    }
  }
  else
  {
    while (i < n)
    {
      x := x + c;
      i := i + 1;
    }
  }
}

procedure thread2()
modifies x, j;
{
  j := 0;

  while (j < n)
  {
    x := x - c;
    j := j + 1;
  }
}
