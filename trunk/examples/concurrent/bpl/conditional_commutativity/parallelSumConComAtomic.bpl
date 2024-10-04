//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Variation of parallelSumConCom with atomic statements
 *
 * Observation: Writing everything into a single atomic statements seems to be problematic for the sleep set criterion!
 */
var A : [int]int;
var i, j, x, y, z, n : int;

procedure ULTIMATE.start()
modifies i, j, A, n, x, y, z;
{
  atomic {
  assume (n > 1);
  i := 0;
  j := 0;
  x := 0;
  y := 0;
  z := 0;}
  fork 1 thread1();
  fork 2 thread2();
  join 1;
  join 2;
  assume (i == n && j == n);
  assert (x == y);
}

procedure thread1()
modifies i, A, x, z;
{
  while (*) {
  atomic {
    assume (i < n);
	z := z + 1;
    x := x + A[i];
    i := i + 1;}
  }
}

procedure thread2()
modifies j, A, y, z;
{ 
  while (*) {
  atomic {
    assume (j < n);
	assume (z >= 0);
    y := y + A[j];
    j := j + 1;}
  }
}
