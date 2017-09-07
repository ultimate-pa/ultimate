//#Unsafe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	b[y] := j;
	a[z] := k;
	i := k;
	k := b[y];

	assert k == i;
	assert z == y;
	assert k != b[y];
}
