//#Safe
/*
 * Author: Sepehr Nadim
 *
 * Similar to SimpleContextParallelIncrementDecrement extends parallelIncrementDecrementConCom.bpl by irrelevant context for the condition 
 * to test ContextSimplifier, but non atomic.
 *
 */
var i, j, n, x, y, k, l, g: int;

procedure ULTIMATE.start()
modifies i, j, n, x, y, k, l, g;
{
  i := 0;
  j := 0;
  x := 0;
  y := 0;
  k := 0;
  l := 0;
  g := 0;
  fork 1   thread1();
  fork 2   thread2();
  fork 3   thread3();
  join 1;
  join 2;
  join 3;
  assert (x==0); // does not appear in the original trace
}

procedure thread1()
modifies i, x, y, l, g;
{
  while (i < n) {
  atomic { // this has to be atomic or the file is left with *Forceful destruction successful, exit code 0*
	y := y + 1;
	x := x + 1;
	i := i + 1;
	l := y + 1; // this does not make l relevant
	g := l;} // this does not make g relevant
  }
}

procedure thread2()
modifies j, x, y;
{
  while (j < n) {
  assume (y >= 0);
  x := x - 1; // this is removed
  j := j + 1;
  }
}

procedure thread3()
modifies k, l, g;
{
  while (k < n) {
  l := l + 1; // context simplifier removes this
  g := g + 1; // context simplifier removes this
  g := l; // context simplifier removes this
  k := k + 1;
  }
}