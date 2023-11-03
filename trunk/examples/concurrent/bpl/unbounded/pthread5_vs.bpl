//#Safe

/*
 * Extracted from: svcomp/pthread-ext/32_pthread5_vs.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-02-09
 *
 */

var g0, g1, lock, mutex: int;

procedure thread1() returns()
modifies g0, g1, lock, mutex;
{
  atomic { assume mutex == 0; mutex := 1; }
  g0 := 1;
  g1 := 1;
  atomic { assume mutex == 1; mutex := 0; }
  lock := 1;
}

procedure thread2() returns()
modifies mutex;
{
  while (true) {
    atomic { assume mutex == 0; mutex := 1; }
    assert g0 == g1;
    atomic { assume mutex == 1; mutex := 0; }
  }
}

procedure thread3() returns()
modifies g0, g1, lock, mutex;
{
  atomic { assume mutex == 0; mutex := 1; }
  if (*) {
    g0 := 0;
    g1 := 0;
    lock := 0;
  }
  atomic { assume mutex == 1; mutex := 0; }
  atomic { assume mutex == 0; mutex := 1; }
  if (lock == 1) {
    assert g0 == 1 && g1 == 1;
  }
  atomic { assume mutex == 1; mutex := 0; }
}

procedure ULTIMATE.start() returns()
modifies g0, g1, lock, mutex;
{
  g0 := 0;
  g1 := 0;
  lock := 0;
  mutex := 0;
  
  fork 0 thread1();
  fork 0 thread2();
  while (true) {
    fork 0 thread3();
  }
}