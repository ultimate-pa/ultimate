//#rTerminationDerivable
/*
 * Date: 2012-06-03
 * Author: heizmann@informatik.uni-freiburg.de
 *
 * 2-lex ranking function: f(k, a[k]) = (k, a[k])
 *
 */
var a : [int] int;
var b : [int] int;
var k : int;

procedure main() returns ()
modifies a, k;
{
  assume true;
  while (a[k] >= 23 && k >= 5) {
    if (*) {
      k := k - 1;
    } else {
      a[k] := a[k] - 1;
    }
  }
}

