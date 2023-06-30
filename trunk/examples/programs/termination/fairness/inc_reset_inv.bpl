//#Terminating

/*
 * Copy of inc_reset.bpl, with just thread and ULTIMATE.start swapped.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-06-29
 *
 */

var x, n: int;

procedure thread() returns()
modifies x;
{
  var cond : bool;

  while (true) {
    atomic { cond := x > 0; x := x + 1; }
    if (!cond) {
      break;
    }
  }
}

procedure ULTIMATE.start() returns()
modifies x;
{
  fork 0 thread();
  x := 0;
}
