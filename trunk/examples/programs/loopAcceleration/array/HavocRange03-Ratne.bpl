//#Safe
/*
 * Test: Value in range is havoced but also bound by a constraint.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-06-03
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
		assume x < 77;
		a[i] := x;
		havoc x;
		i := i + 1;
	}
	assert(a[123456] < 100);
}
