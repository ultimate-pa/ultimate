//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure foo() {
	var a, b, c : [int] int;
	var i, x, y : [int] int;
	a := b[i:=x];
	a[i] := b[i];
	assert a == b;
}
