//#Safe

/*
 * We are unable to prove the program safe, because it has an unbounded number
 * of threads.
 * If we add the outcommented join, we can easily prove the program safe.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-09-17
 *
 */

var x: int;

procedure thread() returns()
modifies x;
{
  x := x + 1;
}

procedure ULTIMATE.start() returns()
modifies x;
{
  x := 0;

  while (*) {
    fork 0 thread();
  }

  assert x >= 0;
}
