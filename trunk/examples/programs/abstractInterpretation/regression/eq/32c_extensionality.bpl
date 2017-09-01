//#Safe
/*
 * Author: Alexander Nutz
 * 
 */

procedure foo() {
	var a, b, c : [int] int;
	var i, x, y : int;
	a := b[i:=x];
	b[i] := x;
	assert a == b;
}
