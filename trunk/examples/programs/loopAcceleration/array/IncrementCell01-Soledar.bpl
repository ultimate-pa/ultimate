//#Safe
/*
 * Test: Reads and write from/to similar cell in each iteration.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-12-20
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a,i;
{
	a[12345] := 23;
	i := 0;
	while (i < 1000000) {
		a[i] := a[i] + 1;
		i := i + 1;
	}
	assert(a[12345] == 24);
}