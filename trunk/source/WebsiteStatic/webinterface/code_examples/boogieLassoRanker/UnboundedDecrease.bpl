//#rTerminationDerivable
/*
 * Example that shows that the decrease of the ranking function may be 
 * unbounded. (y has no upper bound in this example)
 * Our definition of a ranking function does not require that f(x')>=0 holds,
 * it only requires that f(x)>=0 holds.
 * 
 * Date: 11.02.2014
 * Author: heizmann@informatik.uni-freiburg.de
 *
 */

procedure main() returns ()
{
  var x, y: int;
  assume(true);
  while (x >= 0) {
    havoc y;
    assume y >= 1;
    x := x - y;
  }
}

