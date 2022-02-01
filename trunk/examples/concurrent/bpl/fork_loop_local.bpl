//#Safe

/*
 * Simplified vesion of pthread_nondet_loop_bound.bpl
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-11-09
 *
 */

var x, n: int;

procedure thread() returns()
modifies x;
{
  var t : int;
  t := x;
  x := t;
  assert x == 0;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  x := 0;

  while (*) {
    fork 0 thread();
  }
}
