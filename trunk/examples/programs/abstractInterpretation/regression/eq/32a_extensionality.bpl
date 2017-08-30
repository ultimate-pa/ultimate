//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure foo() {
	var a, b, c : [int] int;
	var i, x, y : int;
	a := b[i:=x];
	c := b[i:=y];
	assume x == y;
	assert a == c;
}
