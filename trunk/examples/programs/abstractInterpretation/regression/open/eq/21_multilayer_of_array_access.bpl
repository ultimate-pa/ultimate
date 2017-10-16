//#Safe
/*
 * Author: Yu-Wen Chen
 *  annotations correctness checked via Automizer Webinterface (Alexander Nutz)
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[b[c[y]]] := a[x];

	assert a[b[c[y]]] == a[x];
}
