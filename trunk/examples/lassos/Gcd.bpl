//#rTerminationDerivable
/*
 * Date: 2012-05-09
 *
 * Has the ranking function f(y1, y2) = y1 + y2
 * provided the supporting invariants y1 >= 0, y2 >= 0.
 */


var y1, y2: int;

procedure main() returns ()
modifies y1, y2;
{
  assume(y1 >= 1);
  assume(y2 >= 1);
  while (y1 >= y2 + 1 || y2 >= y1 + 1) {
    if (y1 >= y2 + 1) {
      y1 := y1 - y2;
    } else {
      y2 := y2 - y1;
    }
  }
}

