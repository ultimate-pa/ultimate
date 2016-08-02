//#rTermination
/*
 * Date: 2016-08-02
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
  var x, y: int;
  y := 2;
  while (x >= 0) {
    x := x - y;
    y := (y + 1) / 2;
  }
}

