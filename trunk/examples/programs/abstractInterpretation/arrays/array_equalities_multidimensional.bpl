//#Safe
/*
 * Date: 2018-11-16
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int, int] int;
var x : int;

procedure main() returns ()
modifies b;
{
  b[0, 0] := 1;
  assume a[0, 1] >= 0;
  assume x <= 0;
  assume a == b[0, 1:= x];
  assert a[0, 1] == 0;
}