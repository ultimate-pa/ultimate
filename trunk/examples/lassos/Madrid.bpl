//#rNonTermination
/*
 * Date: 02.05.2013
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Bug in r8689. Lasso ranker says:
 * Found linear ranking function 0 with linear supporting invariant 0 + 1 * x + -2 >= 0
 * 
 * Reason for Bug:
 * Variable x is no "rankingVariable" of the loop (not contained in inVars
 * of loop). Therefore the following implication did not contain coeffcients
 * for x in the right hand side of the implication.
 *     loop -> rankDecrease
 * When adding supporting invariants a coeffcient for x was not added to the
 * implication above, but the coeffcient for x was added to the following
 * implication
 *     stem -> si.
 * 
 */
var x:int;

procedure main() returns ()
modifies x;
{
  x := 7;
  while (true) {
    x := 2;
  }
}
