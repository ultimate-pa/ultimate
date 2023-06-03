//#rNonTerminationDerivable
/*
 * Date: 2015-12-01
 * Author: Matthias Heizmann
 * 
 * we need two lambdas
 * we do not need any nilpotent components
 * we need that both vectors in Y are similar or that one is 0
 * 
 * (i.e., allowing Ys that are not a basis of |R^n is a feature that we need
 * for completeness)
 *
 */

procedure main() returns () {
  var a, b:int;
  
  while (a == b && a > 1 && b > 1) {
    a := 3*a;
    b := 3*b;
  }
}