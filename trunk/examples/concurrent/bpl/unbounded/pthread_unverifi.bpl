//#Safe

/*
 * Extracted from: svcomp/pthread-ext/13_unverifi.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-01-20
 *
 */

var r, s: int;

procedure thread() returns()
modifies r, s;
{
  var l : int;
  l := 0;
  r := r + 1;
  if (r == 1) {
    while (true) {
      s := s + 1;
      l := l + 1;
      assert s == l;
    }
  }
}

procedure ULTIMATE.start() returns()
modifies r, s;
{
  r := 0;
  s := 0;

  while (*) {
    fork 0 thread();
  }
}
