//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Three threads, where the first increments the value of y by 2 n times
 *       the second increments the value of x by 1 2n times
 *		 and the third decrements the value of x and y by 1 2n times
 * Optimal Order would be: Combination of (t1,t3,t3)^n and (t2,t3)^2n, so something like (t1,t2,t2,t3,t3)^n
 *       where t1, t2, t3 stands for an iteration of the respective while-loop
 *
 */
var i, j, k, n, x, y: int;

procedure ULTIMATE.start()
modifies i, j, k, n, x, y;
{
 atomic {
  i := 0;
  j := 0;
  k := 0;
  x := 0;
  y := 0;}
  fork 1   thread1();
  fork 2   thread2();
  fork 3   thread3();
  join 1;
  join 2;
  join 3;
  assert (x == 0 && y == 0);
}

procedure thread1()
modifies i, y;
{
  while (i < n) {
    i := i + 1;
	y := y + 2;
  }
}

procedure thread2()
modifies j, x;
{
  while (j < (2 * n)) {
    j := j + 1;
	x := x + 1;
  }
}

procedure thread3()
modifies k, x, y;
{
  while (k < (2 * n)) {
    k := k + 1;
	x := x - 1;
	y := y - 1;
  }
}

