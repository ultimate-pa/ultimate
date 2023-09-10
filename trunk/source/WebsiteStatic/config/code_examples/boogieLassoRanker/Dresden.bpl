//#rNonTermination
/*
 * Date: 2015-01-14
 * Author: heizmann@informatik.uni-freiburg.de
 * 
 * Lasso program inspired from Vincent's problems with the coolant examples.
 * 
 * Does not have a geometric nontermination argument because y has value 23 at
 * position zero and at position one, but value 42 at position two.
 * 
 * Has a geometric nontermination argument if we add one iteration of the loop 
 * to the stem.
 * Another solution would be to partition the transition relations.
 * 
 */

procedure main() returns ()
{
  var x,y: int;
  y := 23;
  while (*) {
    x := x + 1;
    y := 42;
  }
}
