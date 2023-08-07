//#Terminating

/*
 * Variation of inc_reset_inv.bpl, with one thread incrementing and one decrementing.
 *
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-06-29
 *
 */

var x, n: int;

procedure thread1() returns()
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

procedure thread2() returns()
modifies x;
{
  var cond : bool;

  while (true) {
    atomic { cond := x > 0; x := x - 1; }
    if (!cond) {
      break;
    }
  }
}

procedure ULTIMATE.start() returns()
modifies x;
{
  fork 0 thread1();
  fork 1 thread2();
  //atomic {assume x > 0; x := 0;}
}
