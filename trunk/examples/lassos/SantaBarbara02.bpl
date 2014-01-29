//#rNonTermination
/*
 * Program whose nontermination cannot be proven with our current 
 * nontermination analysis even if we consider the homogenized program.
 *
 * Date: 29.01.2014
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
var a : real;
  a := 1;
  while (a >= -1 && a <= 1) {
    a := -a;
  }
}
