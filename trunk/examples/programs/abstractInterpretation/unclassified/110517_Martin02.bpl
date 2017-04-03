//#Unsafe
procedure foo() {
	var n,x: int;
	x := 0;
	n := 1000000;
	
	while (x < n) {
		x := x + 1;
	}
	
	assert false;
}