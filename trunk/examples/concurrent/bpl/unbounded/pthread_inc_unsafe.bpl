//#Unsafe

/*
 * Variation from: svcomp/pthread-ext/01_inc.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-07-21
 *
 */

var value: int;

procedure thread() returns()
modifies value;
{
  var v : int;

  v := value;
  value := v + 1;
  assert value > v;
}

procedure ULTIMATE.start() returns()
modifies value;
{
  while (*) {
    fork 0 thread();
  }
}
