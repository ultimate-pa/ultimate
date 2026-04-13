//#Safe
/*
 * Author: Sepehr Nadim
 *
 * Like SimpleContextParallelIncrementDecrementConCom.bpl but design to have fewer statements
 *
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
  while (i < 8) {
  atomic {
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
  while (j < 8) {
  atomic {
	assume (y >= 0);
	x := x - 1;
	j := j + 1;}
  }
}

procedure thread3()
modifies k, l, g;
{
  while (k < 16) {
  atomic { // context simplifier removes this
  	l := l + 1;
	g := g + 1;}
  g := l; // context simplifier removes this
  k := k + 1;
  }
}