//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-19
 */

var g: int;

procedure main() returns ();
modifies g;

implementation main() {
  var x: int;

  g := 0;
  if (x > 2) {
    call foo();
  }
  if (x <= 2) {
    call foo();
  }
  assert(g == 0);
}

procedure foo() returns ();
modifies g;

implementation foo() returns () {
    g := 1;
}