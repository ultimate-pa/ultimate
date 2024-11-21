//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Variation of parallelIncrementDecrementConCom but with 4 threads
 *
 */
var i, j, k, l, n, c1, c2, x, y: int;

procedure ULTIMATE.start()
modifies i, j, k, l, n, c1, c2, x, y;
{
 atomic {
  i := 0;
  j := 0;
  k := 0;
  l := 0;
  c1 := 0;
  c2 := 0;
  x := 0;
  y := 0;}
  fork 1   thread1();
  fork 2   thread2();
  fork 3   thread3();
  fork 4   thread4();
  join 1;
  join 2;
  join 3;
  join 4;
  assert (x==0 && y==0);
}

procedure thread1()
modifies i, c1, x;
{
  while (i < n) {
  atomic {
	c1 := c1 + 1;
	x := x + 1;
	i := i + 1;}
  }
}

procedure thread2()
modifies j, c1, x;
{
  while (j < n) {
  atomic {
	assume (c1 >= 0);
	x := x - 1;
	j := j + 1;}
  }
}

procedure thread3()
modifies k, c2, y;
{
  while (k < n) {
  atomic {
	c2 := c2 + 1;
	y := y + 1;
	k := k + 1;}
  }
}

procedure thread4()
modifies l, c2, y;
{
  while (l < n) {
  atomic {
	assume (c2 >= 0);
	y := y - 1;
	l := l + 1;}
  }
}
