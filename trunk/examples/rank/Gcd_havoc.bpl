//#rTermination
/*
 * Date: 2012-05-09
 *
 * Has the ranking function f(y1, y2) = y1 + y2
 * provided the supporting invariants y1 >= 0, y2 >= 0.
 */

var y1, y2: int;

procedure main() returns ()
{
  var y1_old: int;
  var y2_old: int;
  
  assume(y1 >= 0);
  assume(y2 >= 0);
  
  while (y1 != y2) {
    // if (y1 >= y2) then y1 := y1 - y2; else y2 := y2 - y1;
    y1_old := y1;
    y2_old := y2;
    havoc y1;
    havoc y2;
    assume(y1_old < y2_old || y1 == y1_old - y2_old);
    assume(y1_old >= y2_old || y2 == y2_old - y1_old);
  }
}
