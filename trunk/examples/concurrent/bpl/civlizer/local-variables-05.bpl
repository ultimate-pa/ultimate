/**
 * Test case for local variables in conditions (that also have a global variable and must thus be handled by an action).
 *
 * Interestingly, the local variable also occurs in the postcondition of the thread
 * and thus in the Civlizer-generated join pool invariants.
 */

var x : int;

procedure ULTIMATE.start()
modifies x;
{
  fork 1 thread1();
  join 1;
}

procedure thread1()
modifies x;
{
  var y : int;
  if (x > y) {
    x := y;
  }
  assert x <= y;
}

