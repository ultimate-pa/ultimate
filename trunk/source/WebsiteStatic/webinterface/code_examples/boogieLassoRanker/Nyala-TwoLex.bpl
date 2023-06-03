//#rTerminationDerivable
/*
 * Date: 2013-07-13
 * Author: leike@informatik.uni-freiburg.de
 *
 * Simple test case for the lexicographic template.
 * Has the lexicographic ranking function
 * f(x, y) = <x, y>
 * given the supporting invariant y ≥ 0.
 *
 */

procedure main() returns (x: int, y: int)
{
  assume(y >= 0);
  while (x >= 0) {
    y := y - 1;
    if (y < 0) {
        x := x - 1;
        havoc y;
        assume(y >= 0);
    }
  }
}
