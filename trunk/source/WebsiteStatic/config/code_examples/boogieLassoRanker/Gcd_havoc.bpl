//#rTerminationDerivable
/*
 * Date: 2012-05-09
 *
 * Has the ranking function f(y1, y2) = y1 + y2
 * provided the supporting invariants y1 >= 0, y2 >= 0.
 */

procedure main() returns (y1: int, y2: int)
{
  var y1_old: int;
  var y2_old: int;
  
  assume(y1 >= 1);
  assume(y2 >= 1);
  
  while (true) {
    // if (y1 >= y2 + 1) then y1 := y1 - y2; else y2 := y2 - y1;
    y1_old := y1;
    y2_old := y2;
    havoc y1;
    havoc y2;
    assume((y1_old >= y2_old + 1 && y1 == y1_old - y2_old && y2 == y2_old)
        || (y2_old >= y1_old + 1 && y2 == y2_old - y1_old && y1 == y1_old));
  }
}
