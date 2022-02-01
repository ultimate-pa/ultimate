//#Safe
/*
 * Author: heizmann@informatik.uni-freiburg.de, Betim Musa
 * Date: 2016-03-13
 */
var i,r,n,j : int;
var a : [int]int;

// procedure main() 
// modifies a, i, r, n;
// {
// 	i := 0;
// // 	n := 3;
// 	while (i < n) {
// 		a[i] := 0;
// 		i := i + 1;
// 	}
// 	assume(0 <= r && r < n);
// 	assert(a[r] == 0);
// }


procedure main() 
modifies a, i, r, n, j;
{
	i := 0;
	assume j == i;
// 	n := 3;
	while (i < n) {
		a[i] := 0;
		i := i + 1;
	}
	assume(0 <= r && r < n);
	assert(a[r] == 0);
}

