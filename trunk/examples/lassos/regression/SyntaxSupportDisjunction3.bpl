//#rTerminationDerivable
/*
 * Date: 2013-12-21
 * Author: leike@informatik.uni-freiburg.de
 *
 */

procedure SyntaxSupportDisjunction3() returns (x: int)
{
  var random: int;
  assume(true);
  while (x >= 0) {
    havoc random;
    if (random > 0) {
      x := x - 1;
    } else {
      x := x - 1;
    }
  }
}

