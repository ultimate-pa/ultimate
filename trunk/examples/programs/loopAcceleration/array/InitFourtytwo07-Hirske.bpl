//#Unsafe
/*
 * Test: Incorrect specification of updated range via quantiier.
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-07-19
 */
var i : int;
var a : [int]int;

procedure main() 
modifies a, i;
{
	i := 0;
	while (i < 1000000) {
		a[i] := 42;
		i := i + 1;
	}
	assert(forall k : int :: (0 <= k && k < 1000001) ==> a[k] == 42);
}
