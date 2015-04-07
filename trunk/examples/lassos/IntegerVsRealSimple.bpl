//#rTermination
/*
 * Most simple(?) loop that is terminating over the integers but nonterminating
 * over the reals.
 * 
 * Date: 2015-04-06
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x: int;
  while (x >= 0 && x <= 1) {
    x := 3*x - 1;
  }
}
