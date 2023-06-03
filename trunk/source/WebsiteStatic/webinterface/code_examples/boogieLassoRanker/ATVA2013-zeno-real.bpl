//#rTerminationDerivable
/*
 * Lasso program depicted in Figure 4 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x
 * with linear supporting invariant y>=1.
 * Has no linear Ranking function with non-decreasing supporting invariant.
 * 
 * The invariant y>=1 is not non-decreasing.
 * 
 * Over the reals the value of y converges to 1 on the following sequence
 * 2, 1.5, 1.25, 1.125, 1.0625, ...
 * 
 * Over the integers the value of y is decreasing from 2 to 1 in the first loop
 * execution and 1 in all further iterations.
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: real;
  y := 2.0;
  while (x >= 0.0) {
    x := x - y;
    y := (y + 1.0) / 2.0;
  }
}

