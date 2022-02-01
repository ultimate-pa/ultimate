//#rTerminationDerivable
/*
 * Date: 2014-10-20
 * Author: Jan Leike
 *
 * Simple test case for the lexicographic template.
 * Has the lexicographic ranking function
 * f(x, y) = <x + 1, y + 1>.
 *
 */

procedure main() returns (x: int, y: int)
{
  while (x >= 0 && y >= 0) {
    y := y - 1;
    if (y <= 5) {
        x := x - 1;
        havoc y;
        assume(y >= 0);
    }
  }
}
