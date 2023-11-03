//#Safe

/*
 * Extracted from: svcomp/pthread-nondet/nondet-loop-bound-2.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-09-17
 *
 */

var x, n: int;

procedure thread() returns()
modifies x;
{
  var t : int;
  t := x;
  x := t + 1;
  assert x <= n;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var i : int;
  i := 0;
  x := 0;

  while (i < n) {
    fork i thread();
	i := i + 1;
  }
}
