//#Safe
/*
 * Date: 2017-11-30
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int] int;
var i, x : int;

procedure main() returns ()
modifies a, b, x;
{
  a[0] := 0;
  b := a[1 := 0];
  assume i == 0 || i == 1;
  x := b[i];
  assert x == 0;
}