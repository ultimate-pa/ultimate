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
 *
 *
 * This example differs from local-variables01.bpl in that only the local variables
 * of one thread (namely, thread1) are needed. It would be preferable to generate an
 * Owicki-Gries proof in which these variables are only referred to by invariants in
 * thread1 (not in ULTIMATE.start), avoiding the need for ghost mirror variables.
 */

var r0, r1 : int;

procedure ULTIMATE.start()
modifies r0, r1;
{
  var x0 : int;

  fork 1 thread1();

  join 1;

  assert r1 == 4;
}

procedure thread1()
modifies r1;
{
  var x1 : int;
  x1 := 2;
  x1 := x1 + x1;
  r1 := x1;
}

