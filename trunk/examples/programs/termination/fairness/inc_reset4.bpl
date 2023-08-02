//#Terminating

/*
 * Example that terminates for strong and weak fairness.
 *
 * Author: Marcel Ebbinghaus
 * Date: 2023-08-02
 *
 */

var x, n: int;

procedure thread() returns()
modifies x;
{
	atomic {assume x > 0; x:= 0;}
}

procedure ULTIMATE.start() returns()
modifies x;
{
  var cond : bool;
  fork 0 thread();

  while (true) {
    atomic { cond := x > 0; x := x + 1; }
    if (!cond) {
      break;
    }
  }
}