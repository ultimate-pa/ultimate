// #Unsafe
/*
 * This is a regression test for the bug fixed in commit b181ccd:
 * When a forked thread forks another thread, the resulting Petri net was empty
 * because 2 thread usage monitors were created, and the join (non-deterministically)
 * used the wrong one (i.e., not the one used by fork).
 *
 * Author: Dominik Klumpp (klumpp@informatik.uni-freiburg.de)
 * Date: 30. 11. 2020
 *
 */

procedure ULTIMATE.start() {
  fork 1 thread1();
  // assert false; // reachable without bugfix
  join 1;
  assert false; // was unreachable before bugfix
}

procedure thread1() {
  fork 2, 2 thread2();
  join 2, 2;
}

procedure thread2() {
}
