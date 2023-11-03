//#Unsafe
/*
 * Test: Reads and write from/to similar cell in each iteration.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-01-09
 */
var i,k : int;
var a : [int]int;

procedure main() 
modifies a,i;
{
	a[k] := 23;
	i := 0;
	while (i < 1000000) {
		a[k] := a[k] + 1;
		i := i + 1;
	}
	assert(a[k] == 1000000);
}
