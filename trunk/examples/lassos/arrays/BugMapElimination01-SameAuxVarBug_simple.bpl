//#rTermination
/*
 * Date: 2016-09-12
 * Author: schuessf@informatik.uni-freiburg.de
 * 
 * In this example a[i] and a[j] have to be replaced by aux-var, because they
 * contain mixed in- and out-vars (a is havoced before i and j afterwards).
 * 
 * In an earlier version, always the same aux-var was returnd, so the stem was
 * transformed to:
 * (aux = 0) and (aux = 1)
 * and therefore to false.
 */

var a : [int] int;
var i, j, x, y : int;

procedure main() returns ()
modifies a, i, j, x;
{
  havoc a;
  assume a[i] == 0;
  assume a[j] == 1;
  havoc i, j;
  assume y > 0;
  while (x > 0) {
    x := x - y;
  }
}