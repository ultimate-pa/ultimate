//#Safe
/*
 * Date: 2018-11-30
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int, int] int;
var i : int;

procedure main() returns ()
modifies a;
{
  a[0, 3] := 1;
  a[1, 3] := 2;
  assume i == 0 || i == 1;
  assert a[i, 3] > 0;
}