//#rNonTerminationDerivable
/*
 * Date: 2015-07-06
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Counterexample to some completeness conjecture.
 * Lasso does not have geometric nontermination argument although x and y do
 * not occur in the sum of a guard.
 * Using coefficients for nilpotency, we can solve it.
 * 
 */

procedure main() returns ()
{
  var x, y, z: int;
  while (z >= 1 && y <= -1) {
    x := 3*x;
    y := 2*y;
    z := x + y;
  }
}

