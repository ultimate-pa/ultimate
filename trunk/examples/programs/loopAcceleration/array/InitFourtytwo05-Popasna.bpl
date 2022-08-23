//#Safe
/*
 * Test: Loop bound is variable
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-07-17
 */
var i,n : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < n) {
		a[i] := 42;
		i := i + 1;
	}
	assert(1048< n ==> a[1048] == 42);
}
