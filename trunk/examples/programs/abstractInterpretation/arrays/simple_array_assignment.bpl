//#Safe
/*
 * Date: 2017-11-24
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int] int;
var i : int;

procedure main() returns ()
modifies a, b;
{
  a[0] := 0;
  b := a[1 := 1];
  assume i == 0 || i == 1;
  assert b[i] == i;
}