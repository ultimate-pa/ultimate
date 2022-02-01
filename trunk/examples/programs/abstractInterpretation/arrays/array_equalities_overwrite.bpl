//#Safe
/*
 * Date: 2018-11-19
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b : [int] int;
var i, j, n : int;

procedure main() returns ()
modifies a, i;
{
  assume b[0] == 0;
  assume a == b;
  a[1] := 0;
  assert a[1] == 0;
}