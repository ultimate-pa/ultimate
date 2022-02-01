//#Safe
/*
 * Date: 2018-10-09
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int, int] int;
var i, j: int;

procedure main() returns ()
modifies a;
{
  assume a[i, j] == i;
  assert a[i, j] == i;
}