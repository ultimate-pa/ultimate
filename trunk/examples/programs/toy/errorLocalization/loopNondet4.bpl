//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-25
 */

procedure main() returns () {
  var x: int;

  while (*) {
    x := x + 1;
  }
  assert(x == 0);
}