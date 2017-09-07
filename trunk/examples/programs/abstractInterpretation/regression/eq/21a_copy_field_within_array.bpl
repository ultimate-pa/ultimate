//#Safe
/*
 * Author: Alexander Nutz
 *
 * simpler variant of regression test 21_..
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;
	
	a[y] := a[x];

	assert a[y] == a[x];
}
