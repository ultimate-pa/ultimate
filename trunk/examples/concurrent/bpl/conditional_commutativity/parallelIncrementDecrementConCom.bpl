//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Safe program with two loops, which commute entirely except for "y:=y+1" and "assume (y>=0)".
 * However, they conditionally commute, which allows an easy proof if detected and integrated by our approaches.
 *
 */
var i, j, n, x, y: int;

procedure ULTIMATE.start()
modifies i, j, n, x, y;
{
 atomic {
  i := 0;
  j := 0;
  x := 0;
  y := 0;}
  fork 1   thread1();
  fork 2   thread2();
  join 1;
  join 2;
  assert (x==0);
}

procedure thread1()
modifies i, x, y;
{
  while (i < n) {
	y := y + 1;
	x := x + 1;
	i := i + 1;}
	//assert (x >= 0);
}

procedure thread2()
modifies j, x, y;
{
  while (j < n) {
	assume (y >= 0);
	x := x - 1;
	j := j + 1;
  }
}
