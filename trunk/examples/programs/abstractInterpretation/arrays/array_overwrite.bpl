//#Safe
/*
 * Date: 2018-10-09
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int] int;
var i, n : int;

procedure main() returns ()
modifies a, i;
{
  assume n > 0;
  i := 0;
  while (i < n) {
    a[0] := 0;
    i := i + 1;
  }
  assert a[0] == 0;
}