//#Unsafe
/*
 *
 * 
 * test to check "library mode", i.e., every procedure should be an entry point
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure foo();
modifies g;

implementation foo() {

  g := 3;

  call bar();
  
}

procedure bar() returns ();

implementation bar() returns () {

  assert g == 3;

  return;
}

