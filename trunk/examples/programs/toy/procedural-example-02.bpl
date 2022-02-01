
//#Safe
/*
 * simple procedural
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

procedure foo();

implementation foo() {
  var z: int;

  call z := bar();
  
  assert z == 2;
}

procedure bar() returns (c : int);

implementation bar() returns (c : int) {

  c := 2;

  return;
}

