//#Safe
/*
 * Test: Initialized value is based on index.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-07-27
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1000000) {
		a[i] := i;
		i := i + 1;
	}
	assert(a[1048] == 1048);
}
