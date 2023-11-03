//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-03-29
 *
 */

var x, y : int;
var a : [int] int;

procedure main() returns ()
modifies a;
{
	a[x] := 1;
	a[y] := 2;
	assert a[y] == 2;
}
