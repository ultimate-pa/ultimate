//#Safe

/*
 * Extracted from: svcomp/pthread-ext/29_conditionals_vs.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-02-11
 *
 */

var m: int;

procedure thread() returns()
modifies m;
{
  var x, y, z : int;
  
  atomic { assume m == 0; m := 1; }
  if (x == y) {
		z := 0;
	} else {
		z := 1;
	}

	if (z == 0) {
		assert x == y;
	} else {
		assert x != y;
	}
  atomic { assume m == 1; m := 0; }
}

procedure ULTIMATE.start() returns()
modifies m;
{
  m := 0;

  while (*) {
    fork 0 thread();
  }
}