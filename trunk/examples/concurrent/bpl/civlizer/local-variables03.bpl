/**
 * This program requires invariants that refer to the local variables of a thread.
 * Thus, it serves as a test case for the support of local variables in invariants,
 * specifically in unpetrification and Civlizer.
 *
 * In unpetrification, the global variables introduced during petrification for the
 * local variables in a thread instance must be backtranslated either to the original
 * local variables (if the invariant occurs in the same procedure), or to global ghost
 * mirror variables (if the invariant occurs in another procedure).
 *
 * In Civlizer, local variables must be supported in calls to actions that modify
 * global state, and in calls to yield invariants.
 */

var r0, r1 : int;

procedure ULTIMATE.start()
modifies r0, r1;
{
  var x0 : int;

  fork 1 thread1();

  x0 := 1;
  x0 := x0 + x0;
  r0 := x0;

  join 1;

  assert r0 == 2 && r1 == 4;
}

procedure thread1()
modifies r1;
{
  r1 := 4;
}

