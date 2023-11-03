//#Safe
/*
 * Test: The index k can have exactly two values.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-22
 */
var i,k : int;
var a : [int]int;

procedure main() 
modifies a, i, k;
{
	i := 0;
	k := 27;
	while (i < 1000000) {
		a[k] := 42;
		i := i + 1;
		k := 78;
	}
	assert(a[27] == 42);
	assert(a[78] == 42);
}
