//#rTerminationDerivable
/*
 * Date: 2016-09-06
 * Author: schuessf@informatik.uni-freiburg.de
 *
 * This program threw an exception in earlier versions, because
 * the "assume a == b" in the stem occurs in the transformula as:
 * 
 * (= (store a i 1) (store b j 2))
 *
 */

var a, b : [int] int;
var i, j, x, y : int;

procedure main() returns ()
modifies a, b, x;
{
  a[i] := 1;
  b[j] := 2;
  assume a == b;
  havoc a, b;
  assume y > 0;
  while (x > 0) {
    x := x - y;
  }
}
