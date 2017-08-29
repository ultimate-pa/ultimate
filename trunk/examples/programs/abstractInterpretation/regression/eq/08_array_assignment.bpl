//#Safe
/*
 * Author: Yu-Wen Chen
 * Note: The result of this test is not manually verified. DD just added the missing header based on some Ultimate results. 
 * AN: safe according to Ultimate Automizer webinterface on 24.06.2017
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[x] := j;
	b[y] := i;
	a[z] := k;
	i := k;
	k := b[y];
	x := y;	
	assume a[x] != i;
	a := b;
	
	assert a[x] == k && x == y;

}
