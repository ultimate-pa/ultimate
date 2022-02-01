//#rNonTerminationDerivable
/*
 * Date: 2016-10-13
 * schuessf@informatik.uni-freiburg.de
 * 
 * The map-elimination failed on this example, because the stem was
 * transformed to false (a != b was transformed to false, which is not
 * overapproximation).
 *
 * This was fixed 2016-10-14
 */

var a, b : [int] int;
var i : int;

procedure main() returns ()
modifies a, b, i;
{
  a[i] := 0;
  b[i] := 1;
  i := 1;
  a[i] := 2;
  b[i] := 2;
  assume a != b;
  while (a[i] > 0) {
    a[i] := a[i] + 1;
  }
}