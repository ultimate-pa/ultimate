//#Safe
/*
 * Test: Initialize only every second position.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-07-24
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 100) {
		a[i] := 42;
		i := i + 2;
	}
	assert(a[48] == 42);
}
