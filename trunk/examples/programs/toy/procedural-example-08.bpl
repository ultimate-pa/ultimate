//#Safe
/*
 *
 * Case: entry procedure that is also called by some procedure
 * 
 * Author: nutz@informatik.uni-freiburg.de
 *
 */

var g : int;

procedure foo();
modifies g;

implementation foo() {

  g := 3;

  if (*) {
    call foo();
  }
  
  assert g != 0;
}

