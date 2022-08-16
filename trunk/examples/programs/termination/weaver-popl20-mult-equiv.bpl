//#Terminating

/*
 * Extracted from the concurrent benchmark: svcomp/weaver/popl20-mult-equiv.wvr.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-08-01
 *
 */

var M, N, p, MAX: int;

procedure thread1() returns()
modifies N, p;
{
  while (N > 0) {
    atomic {
      if (N > 0) {
        p := (p + M) % MAX;
        N := N - 1;
      }
    }
  }
}

procedure thread2() returns()
modifies N, p;
{
  while (N > 1) {
    atomic {
      if (N > 1) {
        p := (p + M + M) % MAX;
        N := N - 2;
      }
    }
  }
}

procedure ULTIMATE.start() returns()
modifies N, p;
{
  assume M >= 0 && M < MAX;
  assume N >= 0 && N < MAX;
  assume p >= 0 && p < MAX;

  
  fork 1 thread1();
  fork 2 thread2();
}
