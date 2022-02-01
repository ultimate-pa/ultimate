//#rTermination
/*
 * Date: 2016-09-12
 * Author: schuessf@informatik.uni-freiburg.de
 * 
 * In this example (select (store b j 0) i) occurs as a index of a.
 * This led to an exception before, because it contains a store-expression.
 * Now this index is just ignored and not added to the indices. 
 */

var a, b : [int] int;
var i, j, x, y : int;

procedure main() returns ()
modifies a, b, x, y;
{
  b[j] := 0;
  y := a[b[i]];
  havoc b;
  a[i] := x;
  assume b[i] == 0;
  assume y > 0;
  while (x > 0) {
    x := x - y;
  }
}