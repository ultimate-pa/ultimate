//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure Easy() {
	var x, y, z, i, j, k: int;
	var a, b, c : [int] int;

	// The array c should allow the array equality domain to keep enough 
	// information to prove the assertion.
	// after the assume the following should hold
	//  a --k-- c (weak equivalence) and c[j] = z
        // [EDIT] to find out that a--k--c, we may need array extensionality, so
        //  this test relies on that, too. (technical explanation: we introduce
	//  auxilliary arrays to reduce all store chains to length 1, without
	//  extensionality we may arrive at a state 
	//  c --j-- aux1 --j-- aux2 and c[j] = aux2[j], 
	//  thus c = aux2, but we need extensionality to conclude that)
	assume a == b[i:=x][j:=z][k:=y] && c == b[i:=x][j:=z];

	assume j != k;
	
	assert a[j] == z;
}
