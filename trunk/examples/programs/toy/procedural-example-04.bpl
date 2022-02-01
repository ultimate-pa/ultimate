//#Safe
/*
 *
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure foo();
modifies g;

implementation foo() {
  var x, y, z: int;

  x := 1;
  y := 2;

  call z := bar(x, y);
  
  assert z == 3;
  assert g == 1000;
}

procedure bar(a : int, b : int) returns (c : int);
modifies g;

implementation bar(a : int, b : int) returns (c : int) {

  c := a + b;

  g := 1000;

  return;
}

