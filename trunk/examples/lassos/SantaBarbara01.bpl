//#rNonTermination
/*
 * Program whose nontermination can be proven with our current method, if our 
 * analysis considers the following homogenized program.
 *   assume (z > 0);
 *   a := z;
 *   while (a >= -z) {
 *   assume (z > 0);
 *        a := -a;
 *   }
 * 
 * Date: 29.01.2014
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
var a : real;
  a := 1;
  while (a >= -1) {
    a := -a;
  }
}