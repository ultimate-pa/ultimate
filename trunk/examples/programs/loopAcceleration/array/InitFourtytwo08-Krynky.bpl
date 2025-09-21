//#Safe
/*
 * Test: With ev0 update
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-28
 */
var i,j : int;
var a : [int]int;

procedure main() 
modifies a, i, j;
{
	i := 0;
	while (i < 1000000) {
		a[i] := i;
		i := i + 1;
		j := 23;
	}
	assert(a[42] == 42);
}
