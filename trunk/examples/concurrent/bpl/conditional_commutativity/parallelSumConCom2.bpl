//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Variation of parallelSumConComAtomic with 3 threads
 *
 * Observation: Writing everything into a single atomic statements seems to be problematic for the sleep set criterion!
 */
var A : [int]int;
var i, j, k, c, x, y, z, n : int;

procedure ULTIMATE.start()
modifies i, j, k, c, A, n, x, y, z;
{
  atomic {
  assume (n > 1);
  i := 0;
  j := 0;
  k := 0;
  x := 0;
  y := 0;
  z := 0;
  c := 0;}
  fork 1 thread1();
  fork 2 thread2();
  fork 3 thread3();
  join 1;
  join 2;
  join 3;
  assume (i == n && j == n && k == n);
  assert (x == y && x == z);
}

procedure thread1()
modifies i, A, x, c;
{
  while (*) {
  atomic {
    assume (i < n);
	c := c + 1;
    x := x + A[i];
    i := i + 1;}
  }
}

procedure thread2()
modifies j, A, y, c;
{ 
  while (*) {
  atomic {
    assume (j < n);
	assume (c >= 0);
    y := y + A[j];
    j := j + 1;}
  }
}

procedure thread3()
modifies k, A, z, c;
{ 
  while (*) {
  atomic {
    assume (k < n);
	assume (c >= 0);
    z := z + A[k];
    k := k + 1;}
  }
}
