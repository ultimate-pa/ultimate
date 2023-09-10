//#rTermination
/*
 * Date: 2013-01-09
 * Author: leike@informatik.uni-freiburg.de
 *
 * Ranking function: f(x, y, oldy) = x;
 * needs the loop invariant y >= 1, which decreases.
 */

procedure DecreasingInvariant() returns ()
{
  var x, y, oldy: int;
  assume(y >= 1);
  while (x >= 0) {
    x := x - y;
    oldy := y;
    havoc y;
    assume(2*y == oldy + 1);
  }
}
