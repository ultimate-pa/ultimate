//#rNonTerminationDerivable
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * Requires nonlinear nontermination analysis
 */

procedure main() returns ()
{
  var x, old_x: int;
  while (x > 1) {
    old_x := x;
    havoc x;
    assume(x >= 2*old_x);
  }
}
