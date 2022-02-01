//#Safe
/*
 * Author: Yu-Wen Chen
 * (AN: safe according to Ultimate Automizer webinterface on 24.06.2017)
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	b[y] := i;
	a[z] := k;
	i := k;
	k := b[y];

	assume a[x] != i;

	assert a[x] != i && k == b[y];
}
