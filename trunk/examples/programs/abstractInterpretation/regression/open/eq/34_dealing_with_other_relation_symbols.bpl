//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure foo() {
	var a, b, c : [int] int;
	var i, x, y : int;

	// can CommuhashNormalForm recognize that the terms are the same?
        assume x <= y;
        assume !(y >= x);

	assert false;

//	a := b[i:=x];
//	c := b[i:=y];
//	assume x == y;
//	assert a == c;
}
