//#Unsafe
/*
 * Author: Christian Schilling (schillic@informatik.uni-freiburg.de)
 * Date: 2017-06-28
 */

procedure main() {
  var x: int;

  while (x >= 0) {
    x := x - 1;
    if (x == 1) {
      break;
    }
    if (x == 4) {
      break;
    }
    if (x == 7) {
      break;
    }
    if (x == 10) {
      break;
    }
  }
  assert(x == 0);
}
