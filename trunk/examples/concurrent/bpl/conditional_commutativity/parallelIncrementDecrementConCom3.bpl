//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Variation of parallelIncrementDecrementConCom.bpl with 3 threads and atomics
 *
 * Observation: Seems to be problematic for IA, DFS and especially for the sleep set criterion,
 * but works fine for the counterexample approach!
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
  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
  join 1;
  join 2;
  join 3;
  assert (x==0);
}

procedure thread1()
modifies i, x, y;
{
  while (i < n) {
	atomic{
	y := y + 1;
	x := x + 1;
	i := i + 1;}}
	//assert (x >= 0);
}

procedure thread2()
modifies j, x, y;
{
  while (j < n) {
	atomic{
	assume (y >= 0);
	x := x - 1;
	j := j + 1;}
  }
}

procedure thread3()
modifies j, x, y;
{
  while (j < n) {
	atomic{
	assume (y >= 0);
	x := x;}
  }
}