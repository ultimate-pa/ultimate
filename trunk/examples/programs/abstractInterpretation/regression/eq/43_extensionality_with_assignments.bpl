//#Safe
/*
 * Author: nutz
 */

procedure foo() {
	var x, y, i, j, k: int;
	var a, b : [int] int;
	
	a := b[i:=x];
	a[i] := b[i];
	
	assert a == b;
}
