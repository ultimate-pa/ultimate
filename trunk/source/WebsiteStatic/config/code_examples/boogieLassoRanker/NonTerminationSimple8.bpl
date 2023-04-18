//#rNonTermination
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

procedure main() returns (x: int)
{
  while (x >= 0) {
    if (*) {
      x := x + 1;
    } else if (*) {
      x := x + 2;
    } else if (*) {
      x := x + 3;
    } else if (*) {
      x := x + 4;
    } else {
      break;
    }
  }
}

