//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[b[c[y]]] := i;
	a[x] := j;
	assume i != j;

	assert b[c[y]] != x && i != j && a[b[c[y]]] != a[x] && a[b[c[y]]] == i && a[x] == j;
}
