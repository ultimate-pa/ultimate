//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Two threads, where one has a nested loop, where the inner one increments the value of x by c for 100 iterations
 *       and the outer one increments the value of x by an additional c
 *       and the other decrements the value of x by c for 101*n iterations.
 *
 * Optimal schedule would be: (t1 (t2)^101)* but is probably not reasonable,
 *       better would be something like ((t1' t2)* t1'' t2)*       
 *       where t1 stands for a whole iteration of the outer loop, t1' for an iteration of the inner loop
 *       and t1'' for the remaining part of the outer loop
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
    while (j < 100)
    {
      x := x + c;
      j := j + 1;
    }
	  x := x + c;
    i := i + 1;
  }
}

procedure thread2()
modifies x;
{
  var k : int;
  k := 0;

  while (k < (101 * n))
  {
    x := x - c;
    k := k + 1;
  }
}
