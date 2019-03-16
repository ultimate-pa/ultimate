//#Safe
/*
 * Tests the case when a global variable is passed to a procedure as a 
 * parameter.
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure ULTIMATE.start();
modifies g;

implementation ULTIMATE.start() {
  var x, y, z, u: int;

  x := 1;
  y := 2;

  g := 3;

  call z, u := bar(g, y);
  
  assert z == 12;
  assert g == 1000;
}

procedure bar(a : int, b : int) returns (c : int, d : int);
modifies g;

implementation bar(a : int, b : int) returns (c : int, d : int) {
  var l: int;

  l := 4;

  c := a + b + g + l;

  g := 1000;

  return;
}

