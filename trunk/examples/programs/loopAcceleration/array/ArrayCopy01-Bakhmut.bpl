//#Safe
/*
 * Test: Range of elements is copied
 * 
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-07-24
 */
var i : int;
var a,b : [int]int;

procedure main() 
modifies a,b,i;
{
	i := 0;
	while (i < 1000000) {
		a[i] := b[i];
		i := i + 1;
	}
	assert(a[1048] == b[1048]);
}
