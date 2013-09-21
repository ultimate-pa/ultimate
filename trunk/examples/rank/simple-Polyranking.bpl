//#rTerminationDerivable
/*
 * Date: 21.09.2013
 * Author: leikej@informatik.uni-freiburg.de
 *
 * This example is from
 * A. R. Bradley, Z. Manna, and H. B. Sipma.
 * The polyranking principle.
 * In ICALP, pages 1349–1361. Springer, 2005.
 */

procedure simplePolyranking(N: int) returns (x: int, y: int)
{
  var random: int;
  assume(x + y >= 0);
  while (x <= N) {
    havoc random;
    if (random > 0) {
      x := 2*x + y;
      y := y + 1;
    } else {
      x := x + 1;
    }
  }
}

