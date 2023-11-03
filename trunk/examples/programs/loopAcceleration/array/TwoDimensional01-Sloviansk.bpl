//#Safe
/*
 * Test: Initialization of a multi-dimensional array.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-07-24
 */
var i : int;
var a : [int,int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1000000) {
		a[23, i] := 42;
		i := i + 1;
	}
	assert(a[23, 1048] == 42);
}
