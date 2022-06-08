//#Unsafe
/*
 * Author: heizmann@informatik.uni-freiburg.de
 * Date: 2022-06-27
 */
var i,r,n,j : int;
var a : [int]int;

procedure main() 
modifies a, i, r, n;
{
	i := 0;
	while (i < 1000000) {
		a[i] := 0;
		i := i + 1;
	}
	assert(a[1048] == -1);
}
