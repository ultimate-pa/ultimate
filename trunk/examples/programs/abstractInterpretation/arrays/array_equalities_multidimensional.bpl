//#Safe
/*
 * Date: 2018-11-11
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int, int] int;
var i : int;

procedure main() returns ()
modifies a;
{
  a[0, 1] := 0;
  assume a == b[0, 2:=0];
  assume 0 <= i && i <= 2;
  assert a[0, i] == 0;
}