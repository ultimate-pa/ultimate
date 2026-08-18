/**
 * Test case for local variables in conditions (that also have a global variable and must thus be handled by an action).
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
  
  // havoc y to prevent it from occurring in the thread's postcondition
  // (see local-variables-05.bpl for the version without havoc)
  havoc y;
}

