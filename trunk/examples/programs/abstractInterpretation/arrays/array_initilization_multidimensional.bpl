//#Safe
/*
 * Date: 2018-10-09
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int, int] int;
var i, j, n : int;

procedure main() returns ()
modifies a, i;
{
  i := 0;
  while (i < n) {
    a[i, 1] := 0;
    i := i + 1;
  }
  assume 0 <= j && j < n;
  assert a[j, 1] == 0;
}