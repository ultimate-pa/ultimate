//#Unsafe
/*
 * Author: Yu-Wen Chen
 * counterexample: x = 1, y = 1, i = 2, j = 3
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[x] := i;
	a[y] := j;
	assume x == y || i == j;

	assert i == j;
}
