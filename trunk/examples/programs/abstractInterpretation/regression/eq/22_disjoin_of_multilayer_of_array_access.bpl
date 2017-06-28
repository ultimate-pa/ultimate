//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[b[c[y]]] := a[x];
	a[0] := i;
	a[0] := j;
	a[0] := 0;
	assume b[c[y]] == i || c[y] == j;

	assert a[b[c[y]]] == a[x];
}
