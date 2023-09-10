//#rTerminationDerivable
/*
 * Example depicted in Figure 2 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x 
 * with non-decreasing linear supporting invariant x-y>=1
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: real;
  x := y + 42.0;
  while (x >= 0.0) {
    y := 2.0*y - x;
    x := (y + x) / 2.0;
  }
}
