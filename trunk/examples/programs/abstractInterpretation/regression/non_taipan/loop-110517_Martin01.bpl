//#Unsafe
procedure foo() {
	var x: int;
	x := 0;
	
	while (x < 100000) {
		assert true;
		x := x + 1;
	}
	
	assert false;
}
