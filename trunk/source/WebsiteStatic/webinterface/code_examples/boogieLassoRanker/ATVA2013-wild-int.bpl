//#rTerminationDerivable
/*
 * Lasso program depicted in Figure 6 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x
 * with linear supporting invariant y>=1.
 * Has no linear Ranking function with non-decreasing supporting invariant.
 * 
 * The invariant y>=1 is not non-decreasing; because of the havoc statement y 
 * can get any value >=1 in each iteration.
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: int;
  assume (y >= 1);
  while (x >= 0) {
    x := x - y;
    havoc y;
    assume (y >= 1);
  }
}

