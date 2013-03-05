//#rTerminationDerivable
/*
 * Date: 2012-05-09
 *
 * Has the ranking function f(y1, y2) = y1 + y2
 * provided the supporting invariants y1 >= 0, y2 >= 0.
 */

procedure main() returns (y1: int, y2: int)
{
  assume(y1 > 0);
  assume(y2 > 0);
  while (y1 != y2) {
    if (y1 > y2) {
      y1 := y1 - y2;
    } else {
      y2 := y2 - y1;
    }
  }
}

