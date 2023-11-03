//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-03-29
 *
 */

var i, j, x, y : int;
var a, b : [int] int;

procedure main() returns ()
{
	assume a[i:=x] == b[j:=y];
	assume i == j;
	assert x == y;
}
