//#Safe
/*
 * Date: 2018-11-11
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int, int] int;
var i, j, n : int;

procedure main() returns ()
modifies a, i;
{
  assume 0 <= j && j < n;
  i := 0;
  while (i < n) {
    a[1, i] := 0;
    i := i + 1;
  }
  assert a[1, j] == 0;
}