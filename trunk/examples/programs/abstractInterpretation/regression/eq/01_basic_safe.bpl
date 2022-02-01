//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * 
 */

procedure Easy() {
	var x, y, i, j, k: int;
	var a, b : [int] int;
	
	a[x] := i;
	b[y] := j;
	
	i := k;
	assert b[y] == j;
}
