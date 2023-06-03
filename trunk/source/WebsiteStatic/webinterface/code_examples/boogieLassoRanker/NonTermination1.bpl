//#rNonTerminationDerivable
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * Requires nonlinear nontermination analysis
 */

procedure main() returns ()
{
  var x: int;
  while (x > 1) {
    x := 2*x;
  }
}
