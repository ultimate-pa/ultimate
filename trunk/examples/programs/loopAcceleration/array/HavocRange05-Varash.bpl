//#Safe
/*
 * Test: Value in range is havoced but also bound by a constraint that is moving.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2023-10-26
 */
var i,x : int;
var a : [int]int;
var N : int;

procedure main() 
modifies a, i, x;
{
	a[123456] := 42;
	i := 0;
	while (i < 1234567) {
		havoc x;
		assume x < i;
		a[i] := x;
		havoc x;
		i := i + 1;
	}
	assert(a[1234] < 1234);
}
