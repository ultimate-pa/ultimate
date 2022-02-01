//#Unsafe
/*
 * Author: Yu-Wen Chen
 *
 * annotation verified through Ultimate Automizer webinterface (Alexander Nutz, Aug 2017)
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
