//#rTermination
/*
 * Lasso program depicted in Figure 2 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x 
 * with non-decreasing linear supporting invariant x-y>=42
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: int;
  x := y + 42;
  while (x >= 0) {
    y := 2*y - x;
    x := (y + x) / 2;
  }
}

