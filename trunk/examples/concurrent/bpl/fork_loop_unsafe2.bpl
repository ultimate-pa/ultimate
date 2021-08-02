//#Unsafe

/*
 * Example that is unsafe, but only with >=3 threads
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2021-05-21
 *
 */

var x: int;

procedure thread() returns()
modifies x;
{
  x := x + 1;
  assert x < 3;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  x := 0;

  while (*) {
    fork 0 thread();
  }
}
