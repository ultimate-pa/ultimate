//#Unsafe
/*
 * Test: Reads and write from/to similar cell in each iteration.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-01-09
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a,i;
{
	a[0] := 23;
	i := 0;
	while (i < 1000000) {
		a[0] := a[0] + 1;
		i := i + 1;
	}
	assert(a[0] == 1000000);
}
