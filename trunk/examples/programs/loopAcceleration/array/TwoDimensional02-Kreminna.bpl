//#Safe
/*
 * Readonly var is index of write.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-11-30
 */
var i : int;
var a : [int,int]int;
var idx : int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1000000) {
		a[idx, i] := 42;
		i := i + 1;
	}
	assert(a[idx, 1048] == 42);
}
