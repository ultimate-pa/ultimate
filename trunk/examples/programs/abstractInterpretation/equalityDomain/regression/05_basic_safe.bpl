//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	b[y] := i;
	a[z] := k;
	i := k;
	k := b[y];

//	assume a[x] != i;

//	assert a[x] != i && i == a[z];
}
