//#Safe

/*
 * Extracted from: svcomp/pthread-lit/fkp-2014.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-09-17
 *
 */

var s, t: int;

procedure thread() returns()
modifies s, t;
{
  t := t + 1;
  assert s < t;
  s := s + 1;
}

procedure ULTIMATE.start() returns()
modifies s, t;
{
  i := 0;
  s := 0;
  t := 0;

  while (*) {
    fork 0 thread();
  }
}
