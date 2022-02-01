//#rTerminationDerivable
/*
 * Lasso program depicted in Figure 1 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x 
 * with non-decreasing linear supporting invariant y>=1
 * 
 * Date: 11.12.2011
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: real;
  y := 23.0;
  while (x >= 0.0) {
    x := x - y;
    y := y + 1.0;
  }
}

