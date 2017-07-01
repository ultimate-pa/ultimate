//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-20
 */

procedure main() {
  var x,y: int;

  while (x > 0) {
    x := x - 1;
  }
  assert(y == 0);
}