//#Safe

/*
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2020-11-09
 *
 */

var c : int;

procedure thread() returns()
modifies c;
{
  while (*) {
    c := c + 1;
    assert c != 0;
    c := c - 1;
  }
}

procedure ULTIMATE.start() returns()
modifies c;
{
  c := 0;

  while (*) {
    fork 0 thread();
  }
}
