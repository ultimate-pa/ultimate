//#Safe
/*
 * Date: 2018-12-23
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int, int] int;
var i : int;

procedure main() returns ()
modifies a, i;
{
  a[0, 0] := 0;
  a[1, 0] := 0;
  a[2, 0] := 0;
  assume i >= 0 && i < 3;
  a[i, 0] := 0;
  assert a[0, 0] == 0;
}