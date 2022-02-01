//#rNonTerminationDerivable
/*
 * Date: 2014-09-25
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */
var a : [int] int;
var k : int;
var oldValue : int;

procedure main() returns ()
modifies a, k, oldValue;
{
  a[0] := a[0]; // lines necessary to reproduce bug in 12406
  a[k] := a[k]; // lines necessary to reproduce bug in 12406
  while (a[k] != oldValue) {
    oldValue := a[k];
    k := k + 1;
  }
}

