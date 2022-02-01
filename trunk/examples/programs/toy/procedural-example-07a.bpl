//#Unsafe
/*
 *
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

  assert g == 4;

  return;
}

