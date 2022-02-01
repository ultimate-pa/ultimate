//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;

	a := b[i:=x][j:=z][k:=y];
	
	assert a[k] == y;
}
