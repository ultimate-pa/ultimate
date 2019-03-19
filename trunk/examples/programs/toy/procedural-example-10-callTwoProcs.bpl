//#Safe
/*
 * debugging TreeAutomizer "malformed subtree array"
 *
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

procedure ULTIMATE.start();

implementation ULTIMATE.start() {
  var x : int;

  x := 0;

  call foo();
  call bar();
  
  assert x == 0;
}

procedure foo() returns ();

implementation foo() returns () {
  return;
}

procedure bar() returns ();

implementation bar() returns () {
  return;
}

