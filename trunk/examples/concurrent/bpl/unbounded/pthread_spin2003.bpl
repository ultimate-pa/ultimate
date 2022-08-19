//#Safe

/*
 * Extracted from: svcomp/pthread-ext/14_spin2003.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-01-20
 *
 */

var x, m: int;

procedure thread() returns()
modifies x, m;
{
  atomic { assume m == 0; m := 1; }
  x := 0;
  x := 1;
  assert x >= 1;
  atomic { assume m == 1; m := 0; }
}

procedure ULTIMATE.start() returns()
modifies x, m;
{
  x := 1;
  m := 0;

  while (*) {
    fork 0 thread();
  }
}
