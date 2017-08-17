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
	a[y] := j;
	assume i != j;

	//# holds
	assert i != j && x != y;
	
	//# 
}
