//#Unsafe
/*
 * Author: Yu-Wen Chen
 * unsafe (according to Automizer web interface, relabeled on 21.8.2017 by nutz)
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
