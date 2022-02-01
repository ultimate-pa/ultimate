//#rNonTerminationDerivable
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 * Does not terminate for y >= 5.
 */

procedure main() returns (x: int)
{
  var y: int;
  assume y >= 5;
  while (x >= 0) {
    y := y - 1;
  }
}

