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
  var z: int;

  call z := bar();
  
  assert z == 10;
  assert g == 1000;
}

procedure bar() returns (c : int);
modifies g;

implementation bar() returns (c : int) {

  c := 10;

  g := 1000;

  return;
}

