//#Safe

/*
 * Author: Frank Schüssele (schuessf@informatik.uni-freiburg.de)
 * Date: 2023-03-29
 *
 */

var x, y, z : int;
var a : [int,int] int;

procedure main() returns ()
modifies a;
{
	a[x,y] := 1;
	assume y == z;
	assert a[x,z] == 1;
}
