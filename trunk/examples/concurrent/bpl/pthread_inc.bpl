//#Safe

/*
 * Extracted from: svcomp/pthread-ext/01_inc.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-09-17
 *
 */

var value, m: int;

procedure thread() returns()
modifies value, m;
{
  var v : int;
  v := 0;
  assume m == 0;
  m := 1;
  if (value == -1) {
    assume m == 1;
	m := 0;
  } else {
    v := value;
	value := v + 1;
    assume m == 1;
	m := 0;
	assert value > v;
  }
}

procedure ULTIMATE.start() returns()
modifies value, m;
{
  var i : int;
  m := 0;

  while (*) {
    fork i thread();
	i := i + 1;
  }
}
