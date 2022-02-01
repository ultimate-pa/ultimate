//#rTerminationDerivable
/*
 * Date: 2016-09-14
 * schuessf@informatik.uni-freiburg.de
 * 
 */

var a : [int] int;
var x, i, j : int;

procedure main() returns ()
modifies a, i, j, x;
{
  havoc a, j;
  assume a[i] > 1;
  assume i == j;
  havoc i;
  while (x > 0) {
	x := x - a[j];
  }
}