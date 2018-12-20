//#Safe
/*
 * Date: 2018-12-20
 * schuessf@informatik.uni-freiburg.de
 *
 * Extraction of Luxembourg-WithArrays.bpl which leads to "Post is unsound"
 * for the ArrayDomain.
 *
 */

var a : [int] int;
var x, y : int;

procedure main() returns ()
modifies a;
{
  assume x > y;
  a[x] := 1000;
  a[y] := 1000;
  assert a[x] == 1000;
}