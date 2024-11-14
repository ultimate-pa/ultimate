//#Safe
/*
 * Author: Marcel Ebbinghaus
 *
 * Idea: Program highly benefits from LooplockStep order, but seems to be nonterminating 
 * (or at least takes a lot of time) without our approach
 *
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
  assert (x == y);
}

procedure thread1()
modifies i, A, x, y, z;
{
  z := z + 1;
  while (i <= n) {
    z := z + 1;
    x := x + A[i];
    i := i + 1;
  }
}

procedure thread2()
modifies j, A, x, y, z;
{
  assume (z >= 0);
  while (j <= n) {
    assume (z >= 0);
    y := y + A[j];
    j := j + 1;
  }
}
