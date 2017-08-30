//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure foo() {
	var a, b, c : [int] int;
	var i, x, y : [int] int;
	a := b[i:=x];
	asume a[i] == b[i];
	assert a == b;
}
