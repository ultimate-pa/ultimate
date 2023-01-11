//#Safe
/*
 * Test: Value in range is havoced.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-12-12
 */
var i,x : int;
var a : [int]int;
var N : int;

procedure main() 
modifies a, i, x;
{
	a[123456] := 42;
	i := 0;
	while (i < N) {
		havoc x;
		a[i] := x;
		i := i + 1;
	}
	assert(N <= 123456  ==> a[123456] == 42);
}
