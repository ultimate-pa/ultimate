//#rNonTerminationDerivable
/*
 * Date: 2012-06-09
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */
var a : [int] int;
var b : [int] int;
var k : int;

procedure main() returns ()
modifies a, k;
{
  assume true;
  while (a[k] >= 0) {
    a[k] := a[k] - 1;
    k := k + 1;
  }
}

