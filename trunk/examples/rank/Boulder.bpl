//#rTerminationDerivable
/*
 * Lasso program demonstrated to us by Aaron Bradley in March 2013.
 * Has linear Ranking function f(x,y)=x 
 * with non-decreasing linear supporting invariant y>=1.
 * However this lasso program does not have a polyranking argument that can be
 * found using only linear constraint solving.
 *
 * Date: 24.03.2013
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y, somePositiveNumber: int;
  y := 23;
  while (x >= 0) {
    x := x - y;
    havoc somePositiveNumber;
    assume (somePositiveNumber > 0);
    y := y + somePositiveNumber;
  }
}