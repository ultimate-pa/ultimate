//#Safe
/*
 *
 * Case: procedure needs to return normally before assertion is checked
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
  
  assert g != 0;
}

procedure bar() returns ();

implementation bar() returns () {

  return;
}

