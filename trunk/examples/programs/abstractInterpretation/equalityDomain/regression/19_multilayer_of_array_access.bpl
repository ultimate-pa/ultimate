//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	c[y] := k;	
	b[c[y]] := j;
	a[b[c[y]]] := i;

	assert c[y] == k && b[c[y]] == j && a[b[c[y]]] == i;
}
