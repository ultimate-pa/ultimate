//#rNonTerminationDerivable
/*
 * Date: 2014-09-25
 * Author: heizmann@informatik.uni-freiburg.de
 * Reveals bug in 12406.
 *
 */

var k : int;
var a : [int] int;

procedure main() returns ()
modifies a, k;
{
  k := 0;
  a[k] := a[k] + 1;
  while (a[k] != 0) {
    k := k - 1;
  }
}
