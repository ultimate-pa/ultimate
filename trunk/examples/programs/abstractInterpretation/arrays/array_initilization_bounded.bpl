//#Safe
/*
 * Date: 2017-11-17
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a : [int] int;
var i : int;
var j : int;
var n : int;

procedure main() returns ()
modifies a, i, n;
{
  n := 3;
  i := 0;
  while (i < n) {
    a[i] := 0;
    i := i + 1;
  }
  assume 0 <= j && j < n;
  assert a[j] == 0;
}