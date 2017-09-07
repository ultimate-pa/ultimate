//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-19
 */

procedure main() {
  var x: int;

  if (true) {
  }
  if (x > 2) {
    call foo();
  } else {
    call foo();
  }
}

procedure foo() returns () {
    assert false;
}