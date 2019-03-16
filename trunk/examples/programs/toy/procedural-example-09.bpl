//#Safe
/*
 * Like procedural-example-01 but with more global variables.
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g, h, i : int;

procedure ULTIMATE.start();
modifies g, h, i;

implementation ULTIMATE.start() {
  var x, y, z, u: int;

  x := 1;
  y := 2;

  g := 3;
  h := 4;
  i := 5;

  call z, u := bar(x, y);
  
  assert z == 19;
  assert g == 1000;
  assert i == 1001;
}

procedure bar(a : int, b : int) returns (c : int, d : int);
modifies g, i;

implementation bar(a : int, b : int) returns (c : int, d : int) {
  var l: int;

  l := 4;

  c := a + b + g + l + h + i;

  g := 1000;
  i := 1001;

  return;
}

