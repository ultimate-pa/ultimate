//#Safe
/*
 * Test: Initialized value is based on index.
 * In contrast to InitAscending01-Izium.bpl the expressions for index
 * and value are not just `i`.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-09-14
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1000000) {
		a[i+2] := 3*i-1;
		i := i + 1;
	}
	assert(a[1002] == 2999);
}
