//#rTerminationDerivable
/*
 * Lasso program depicted in Figure 3 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x-y
 * with non-decreasing linear supporting invariant 0>=0
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: real;
  y := 23.0;
  while (x >= y) {
    x := x - 1.0;
  }
}

