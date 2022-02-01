//#Safe
/*
 *
 * unnecessary modifies (together with the rest) triggers a bug (14.3.2019)
 * in this version, also kills z3  Z3 version 4.8.3 - 64 bit
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
  
  assert z == 3;
}

procedure bar() returns (c : int);
modifies g;

implementation bar() returns (c : int) {

  c := g;

  return;
}

