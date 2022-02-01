//#Safe
/*
 * Tests if our join operation conserves weak equivalence edges that are not 
 * given explicitly but through the closure operation on the weak equivalence
 * graph that ensures a variation of the triangle inequality.
 * simple version of test 30_...
 *
 * Author: Alexander Nutz
 * 
 */

procedure Easy() {
	var x, y, z, u, v, i, j, k: int;
	var a, b, c, d : [int] int;


	assume a == b[i := x];
	assume b == c[j := y];
	// we have weak equivalence edges
	// a --i-- b
	// b --j-- c
	// and, by closure, a --i,j-- c

	assume k != i && k != j;

	assert a[k] == c[k];
}
