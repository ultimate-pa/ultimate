//#Safe

/*
 * Extracted from: svcomp/pthread-ext/05_tas.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2022-01-20
 *
 */

var c, lock: int;

procedure thread() returns()
modifies c, lock;
{
  var cond : int;
  
  while (true) {
    atomic { cond := lock; lock := 1; }
    while (cond == 1) {
      atomic { cond := lock; lock := 1; }
    }
    c := c + 1;
    assert c == 1;
    c := c - 1;
    lock := 0;
  }
}

procedure ULTIMATE.start() returns()
modifies c, lock;
{
  lock := 0;
  c := 0;

  while (*) {
    fork 0 thread();
  }
}
