//#Safe
/*
 *
 *
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure foo();
modifies g;

implementation foo() {
  var z: int;

  g := 3;

  call z := bar();
  
  assert z == 8;
}

procedure bar() returns (c : int);

implementation bar() returns (c : int) {

  c := 1 + g + 4;

  return;
}

