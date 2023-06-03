//#rTermination
/*
 * Program from Example 2 of
 * 2004VMCAI - Podelski,Rybalchenko - A complete method for the synthesis of linear ranking functions
 * 
 * Program is terminating over the integers but nonterminating over the reals.
 * In order to prove termination we would need to implement computation of the
 * integral hull.
 *
 * In r13910 the nontermination analysis incorrectly synthesizes a
 * geometric nontermination argument.
 * 
 * Date: 2015-04-06
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x: int;
  while (x >= 0) {
    x := -2*x + 10;
  }
}
