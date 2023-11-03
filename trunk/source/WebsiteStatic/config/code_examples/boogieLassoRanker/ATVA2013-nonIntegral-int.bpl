//#rTermination
/*
 * Lasso program depicted in Figure 8 of our ATVA2013 submission.
 * 
 * Has linear Ranking function f(x,y)=x
 * with non-decreasing supporting invariant y>=1 over the integers.
 * Does not terminate over the reals.
 * 
 * Over the integers we can only synthesize the ranking function if we make
 * the stem of this lasso program integral. In this example, the stem is
 * integral if we add the constraint y'>=1.
 * 
 * Date: January 2013
 * Author: Jan Leike and heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: int;
  assume (2*y >= 1);
  while (x >= 0) {
    x := x - 2*y + 1;
  }
}

