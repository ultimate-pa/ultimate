//#Safe
/*
 * Date: 2018-10-09
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int] int;
var i : int;

procedure main() returns ()
modifies a, b;
{
  a[i] := 0;
  b[i+1] := 0;
  assume a == b;
  assert b[i] == 0 && a[i+1] == 0;
}