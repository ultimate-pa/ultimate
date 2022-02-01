//#Safe
/*
 * Tests the interplay between weak equivalence edges and the ground partial assignment.
 * When adding a ground disequality, an existing weak equivalence edge may induce an equality of array
 * selects.
 *
 * Author: Alexander Nutz
 * 
 */

procedure Easy() {
	var x, y, z, u, v, i, j, k: int;
	var a, b, c, d : [int] int;


	assume a == b[i := x];
	// we have a weak equivalence edge
	// a --i-- b

	assume k != i;
	// at this point we can conclude a[k] = b[k] (but we don't have the terms yet)

	// this assertion should be provable by the eq domain
        // we should propagate once we have added both select terms.. 
	assert a[k] == b[k];
}
