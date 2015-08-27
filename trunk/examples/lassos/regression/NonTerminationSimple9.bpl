//#rNonTerminationDerivable
/*
 * Date: 2014-06-26
 * Author: leike@informatik.uni-freiburg.de
 *
 */

procedure main() returns (x: int)
{
  var y: int;
  while (x >= 0) {
    havoc y;
    x := x + y;
  }
}

