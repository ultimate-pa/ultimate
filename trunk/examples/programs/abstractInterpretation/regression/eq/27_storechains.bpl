//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;

	// the array c should allow the array equality domain to keep enough information
	// to prove the assertion:
	// after the assume the following should hold
	//  a --k-- c (weak equivalence) and c[j] = z
	assume a == b[i:=x][j:=z][k:=y] && c == b[i:=x][j:=z];

	assume j != k;
	
	assert a[j] == z;
}
