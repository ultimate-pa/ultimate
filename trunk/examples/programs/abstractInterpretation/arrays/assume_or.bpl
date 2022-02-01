//#Safe
/*
 * Date: 2018-11-24
 * schuessf@informatik.uni-freiburg.de
 *
 */

var a, b: [int] int;
var i : int;

procedure main() returns ()
modifies a;
{
  assume i > 1 && (i == 0 || i == 1 || a[i] == 0);
  a[0] := 0;
  a[1] := 0;
  assert a[i] == 0;
}