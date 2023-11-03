//#rUnknown
/*
 * Date: 2012-02-12
 * Author: leike@informatik.uni-freiburg.de
 *
 * Termination unknown as of this date.
 */

procedure Collatz(x: int) returns (y: int)
{
  while (y > 1) {
    if (y % 2 == 0) {
      y := y / 2;
    } else {
      y := y * 3 + 1;
    }
  }
}
