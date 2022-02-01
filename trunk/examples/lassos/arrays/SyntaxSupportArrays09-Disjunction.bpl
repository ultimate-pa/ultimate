//#rNonTerminationDerivable
/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 *
 */
var a : [int] int;

procedure main() returns ()
modifies a;
{
  assume true;
  while (a[0] >= 0) {
    if (*) {
      a[0] := a[0] + 1;
    } else {
      a[0] := a[0] - 1;
    }
  }
}

