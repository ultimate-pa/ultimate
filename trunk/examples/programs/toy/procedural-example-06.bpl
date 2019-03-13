//#Safe
/*
 *
 * 
 * test to check that ULTIMATE.start is the only entry point
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure ULTIMATE.start();
modifies g;

implementation ULTIMATE.start() {

  g := 3;

  call bar();
  
}

procedure bar() returns ();

implementation bar() returns () {

  assert g == 3;

  return;
}

