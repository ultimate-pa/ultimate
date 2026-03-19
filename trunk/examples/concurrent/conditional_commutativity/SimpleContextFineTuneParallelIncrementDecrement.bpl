//#Safe
/*
 * Author: Sepehr Nadim
 *
 * Similar to SimpleContextParallelIncrementDecrement extends parallelIncrementDecrementConCom.bpl
 * by irrelevant context for the condition, but in a way the current ContextSimplifier can't remove it
 * but a fine tuned version could
 * this makes l relevant when y is relevant, fine tune wouldn't, g stays irrelevant
 * context simplifier does not remove this (except when this appears after the last - g := y + l -), but fine tune could
 */
var i, j, n, x, y, k, l, g: int;

procedure ULTIMATE.start()
modifies i, j, n, x, y, k, l, g;
{
 atomic {
  i := 0;
  j := 0;
  x := 0;
  y := 0;
  k := 0;
  l := 0;
  g := 0;}
  fork 1   thread1();
  fork 2   thread2();
  fork 3   thread3();
  join 1;
  join 2;
  join 3;
  assert (x==0);
}

procedure thread1()
modifies i, x, y, l, g;
{
  while (i < n) {
  atomic {
	y := y + 1;
	x := x + 1;
	g := y + l; // this makes l relevant when y is relevant, fine tune wouldn't, g stays irrelevant
	i := i + 1;}
  }
}

procedure thread2()
modifies j, x, y;
{
  while (j < n) {
  atomic {
	assume (y >= 0);
	x := x - 1;
	j := j + 1;}
  }
}

procedure thread3()
modifies k, l, g;
{
  while (k < n) {
  atomic { // context simplifier does not remove this (except when this appears after the last - g := y + l -), but fine tune could
  	l := l + 1;
	g := g + 1;}
  k := k + 1;
  }
}