//#Safe

/*
 * Extracted from: svcomp/pthread-ext/01_inc.c
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2021-05-17
 *
 */

var value, m: int;

procedure thread() returns()
modifies value, m;
{
  var v : int;

  atomic { assume m == 0 && value % 10 != 9; m := 1; }
  v := value;
  value := if v == 9 then 0 else v + 1;
  atomic { assume m == 1; m := 0; }
  assert value % 10 > v % 10;
}

procedure ULTIMATE.start() returns()
modifies value, m;
{
  m := 0;
  value := 0;

  while (*) {
    fork 0 thread();
  }
}
