//#rTermination
/*
 * Date: 2014-01-21
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Example 1 of
 * 2006CAV - Braverman - Termination of Interger Linear Programs
 * The loop is is terminating over integers and nonterminating over the reals.
 */

var x,y:int;

procedure main() returns ()
modifies x,y;
{
  assume(true);
  while (4*x+y > 0) {
    x, y := -2*x + 4*y, 4*x;
  }
}
