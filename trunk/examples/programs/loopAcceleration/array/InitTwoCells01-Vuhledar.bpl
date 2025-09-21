//#Safe
/*
 * Test: Two array writes in one iteration.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-26
 */
var i : int;
var a : [int]int;
var N : int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1234567) {
		a[i] := 42;
		a[i+1] := 23;
		i := i + 2;
	}
	assert(a[1234] >= 5);
}
