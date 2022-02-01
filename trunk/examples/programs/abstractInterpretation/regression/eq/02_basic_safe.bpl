//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[x] := i;
	b[y] := j;
	a[z] := k;
	
	i := k;
	assert k == i && a[z] == k && b[y] == j;
}
