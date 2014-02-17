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
 * Discussion with Jan showed that this is no bug. That we can not find a
 * nontermination argument even if we transform the program into homogenized
 * form.
 * 
 * Date: 29.01.2014
 * Author: heizmann@informatik.uni-freiburg.de
 */

procedure main() returns ()
{
var a : real;
  a := 1.0;
  while (a >= (0.0 - 1.0)) {
    a := 0.0 - a;
  }
}
