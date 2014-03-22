//#rTerminationDerivable
/*
 * Date: 2014-03-22
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * Test case for the correct handling of booleans.
 * Needs boolean support in the nontermination analysis.
 *
 */

procedure proc() returns ()
{
  var b: bool;
  var x: int;
  while (x >= 0 && b) {
    if (*) {
      x := x - 1;
    } else {
      b := false;
    }
  }
}
